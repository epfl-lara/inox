/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers.z3

import utils._

import z3.scala.{Z3Solver => ScalaZ3Solver, _}
import solvers._

import scala.collection.mutable.{Map => MutableMap}

case class UnsoundExtractionException(ast: Z3AST, msg: String)
  extends Exception("Can't extract " + ast + " : " + msg)

// This is just to factor out the things that are common in "classes that deal
// with a Z3 instance"
trait Z3Native extends ADTManagers with Interruptible { self: AbstractSolver =>
  import context._
  import program._
  import program.trees._
  import program.symbols._

  type Trees = Z3AST
  type Model = Z3Model

  protected implicit val semantics: program.Semantics

  interruptManager.registerForInterrupts(this)

  @volatile
  private[this] var interrupted = false

  private[this] var freed = false
  private[this] val traceE = new Exception()

  protected def unsound(ast: Z3AST, msg: String): Nothing =
    throw UnsoundExtractionException(ast, msg)

  override def finalize() {
    if (!freed) {
      println("!! Solver "+this.getClass.getName+"["+this.hashCode+"] not freed properly prior to GC:")
      traceE.printStackTrace()
      free()
    }
  }

  protected[z3] var z3 : Z3Context = new Z3Context(
    "MODEL"             -> true,
    "TYPE_CHECK"        -> true,
    "WELL_SORTED_CHECK" -> true
  )

  // @nv: This MUST take place AFTER Z3Context was created!!
  // Well... actually maybe not, but let's just leave it here to be sure
  toggleWarningMessages(true)

  def free(): Unit = synchronized {
    freed = true
    if (z3 ne null) {
      z3.delete()
      z3 = null
    }
    interruptManager.unregisterForInterrupts(this)
  }

  def interrupt(): Unit = synchronized {
    if ((z3 ne null) && !interrupted) {
      interrupted = true
      z3.interrupt()
    }
  }

  def functionDefToDecl(tfd: TypedFunDef): Z3FuncDecl = {
    functions.cachedB(tfd) {
      val sortSeq    = tfd.params.map(vd => typeToSort(vd.getType))
      val returnSort = typeToSort(tfd.getType)

      z3.mkFreshFuncDecl(tfd.id.uniqueName, sortSeq, returnSort)
    }
  }

  def declareVariable(v: Variable): Z3AST = variables.cachedB(v) {
    symbolToFreshZ3Symbol(v)
  }

  // ADT Manager
  private[z3] val adtManager = new ADTManager

  // Bijections between Inox Types/Functions/Ids to Z3 Sorts/Decls/ASTs
  private[z3] val functions = new IncrementalBijection[TypedFunDef, Z3FuncDecl]()
  private[z3] val lambdas   = new IncrementalBijection[FunctionType, Z3FuncDecl]()
  private[z3] val variables = new IncrementalBijection[Variable, Z3AST]()

  private[z3] val constructors = new IncrementalBijection[ConsType, Z3FuncDecl]()
  private[z3] val selectors    = new IncrementalBijection[(ConsType, Int), Z3FuncDecl]()
  private[z3] val testers      = new IncrementalBijection[ConsType, Z3FuncDecl]()

  private[z3] val sorts = new IncrementalMap[Type, Z3Sort]()

  def push(): Unit = {
    adtManager.push()
    functions.push()
    lambdas.push()
    variables.push()

    constructors.push()
    selectors.push()
    testers.push()

    sorts.push()
  }

  def pop(): Unit = {
    adtManager.pop()
    functions.pop()
    lambdas.pop()
    variables.pop()

    constructors.pop()
    selectors.pop()
    testers.pop()

    sorts.pop()
  }

  def reset(): Unit = {
    throw new CantResetException(this)
  }

  private def declareStructuralSort(t: Type): Unit = {
    adtManager.declareADTs(t, declareDatatypes)
  }

  private def declareDatatypes(adts: Seq[(Type, DataType)]): Unit = {
    import Z3Context.{ADTSortReference, RecursiveType, RegularSort}

    val indexMap: Map[Type, Int] = adts.map(_._1).zipWithIndex.toMap

    def typeToSortRef(tt: Type): ADTSortReference = {
      if (indexMap contains tt) {
        RecursiveType(indexMap(tt))
      } else {
        RegularSort(typeToSort(tt))
      }
    }

    // Define stuff
    val defs = for ((_, DataType(sym, cases)) <- adts) yield {(
      sym.uniqueName,
      cases.map(c => c.sym.uniqueName),
      cases.map(c => c.fields.map { case (id, tpe) => (id.uniqueName, typeToSortRef(tpe))})
    )}

    val resultingZ3Info = z3.mkADTSorts(defs)

    for ((z3Inf, (tpe, DataType(sym, cases))) <- resultingZ3Info zip adts) {
      sorts += (tpe -> z3Inf._1)
      assert(cases.size == z3Inf._2.size)

      for ((c, (consFun, testFun)) <- cases zip (z3Inf._2 zip z3Inf._3)) {
        testers += (c.tpe -> testFun)
        constructors += (c.tpe -> consFun)
      }

      for ((c, fieldFuns) <- cases zip z3Inf._4) {
        assert(c.fields.size == fieldFuns.size)

        for ((selFun, index) <- fieldFuns.zipWithIndex) {
          selectors += (c.tpe, index) -> selFun
        }
      }
    }
  }

  // Prepare some of the Z3 sorts, but *not* the tuple sorts; these are created on-demand.
  sorts += CharType() -> z3.mkBVSort(16)
  sorts += IntegerType() -> z3.mkIntSort
  sorts += RealType() -> z3.mkRealSort
  sorts += BooleanType() -> z3.mkBoolSort

  // FIXME: change to `z3.mkSeqSort(z3.mkBVSort(16))` once sequence support is fixed in z3
  sorts += StringType() -> z3.mkSeqSort(z3.mkBVSort(8))

  // assumes prepareSorts has been called....
  protected def typeToSort(oldtt: Type): Z3Sort = oldtt match {
    case BooleanType() | IntegerType() | RealType() | CharType() | StringType() =>
      sorts(oldtt)

    case tt @ BVType(_, i) =>
      sorts.cached(tt) {
        z3.mkBVSort(i)
      }

    case tpe @ (_: ADTType  | _: TupleType | _: TypeParameter | UnitType()) =>
      if (!sorts.contains(tpe)) declareStructuralSort(tpe)
      sorts(tpe)

    case tt @ SetType(base) =>
      sorts.cached(tt) {
        declareStructuralSort(tt)
        z3.mkSetSort(typeToSort(base))
      }

    case tt @ BagType(base) =>
      typeToSort(MapType(base, IntegerType()))

    case tt @ MapType(from, to) =>
      sorts.cached(tt) {
        declareStructuralSort(tt)
        val fromSort = typeToSort(from)
        val toSort = typeToSort(to)

        z3.mkArraySort(fromSort, toSort)
      }

    case ft @ FunctionType(from, to) =>
      sorts.cached(ft) {
        val symbol = z3.mkFreshStringSymbol(ft.toString)
        z3.mkUninterpretedSort(symbol)
      }

    case other =>
      unsupported(other)
  }

  protected[z3] def toZ3Formula(expr: Expr, bindings: Map[Variable, Z3AST] = Map.empty): Z3AST = {

    def rec(ex: Expr)(implicit bindings: Map[Variable, Z3AST]): Z3AST = ex match {

      case Let(vd, e, b) =>
        val re = rec(e)
        rec(b)(bindings + (vd.toVariable -> re))

      case a @ Assume(cond, body) =>
        val (rc, rb) = (rec(cond), rec(body))
        z3.mkITE(rc, rb, z3.mkFreshConst("fail", typeToSort(body.getType)))

      case v: Variable => bindings.getOrElse(v,
        variables.cachedB(v)(z3.mkFreshConst(v.id.uniqueName, typeToSort(v.getType)))
      )

      case ite @ IfExpr(c, t, e) => z3.mkITE(rec(c), rec(t), rec(e))
      case And(exs) => z3.mkAnd(exs.map(rec): _*)
      case Or(exs) => z3.mkOr(exs.map(rec): _*)
      case Implies(l, r) => z3.mkImplies(rec(l), rec(r))
      case Not(Equals(l, r)) => z3.mkDistinct(rec(l), rec(r))
      case Not(e) => z3.mkNot(rec(e))
      case bv @ BVLiteral(_, _, _) =>
        z3.mkNumeral(bv.copy(signed = true).toBigInt.toString, typeToSort(bv.getType))
      case IntegerLiteral(v) => z3.mkNumeral(v.toString, typeToSort(IntegerType()))
      case FractionLiteral(n, d) => z3.mkNumeral(s"$n / $d", typeToSort(RealType()))
      case CharLiteral(c) => z3.mkInt(c, typeToSort(CharType()))
      case BooleanLiteral(v) => if (v) z3.mkTrue() else z3.mkFalse()
      case Equals(l, r) => z3.mkEq(rec( l ), rec( r ) )
      case Plus(l, r) => l.getType match {
        case BVType(_,_) => z3.mkBVAdd(rec(l), rec(r))
        case _ => z3.mkAdd(rec(l), rec(r))
      }
      case Minus(l, r) => l.getType match {
        case BVType(_,_) => z3.mkBVSub(rec(l), rec(r))
        case _ => z3.mkSub(rec(l), rec(r))
      }
      case Times(l, r) => l.getType match {
        case BVType(_,_) => z3.mkBVMul(rec(l), rec(r))
        case _ => z3.mkMul(rec(l), rec(r))
      }
      case Division(l, r) =>
        val (rl, rr) = (rec(l), rec(r))
        l.getType match {
          case IntegerType() =>
            z3.mkITE(
              z3.mkGE(rl, z3.mkNumeral("0", typeToSort(IntegerType()))),
              z3.mkDiv(rl, rr),
              z3.mkUnaryMinus(z3.mkDiv(z3.mkUnaryMinus(rl), rr))
            )
          case BVType(true, _) => z3.mkBVSdiv(rl, rr)
          case BVType(false, _) => z3.mkBVUdiv(rl, rr)
          case _ => z3.mkDiv(rl, rr)
        }
      case Remainder(l, r) => l.getType match {
        case BVType(true, _) => z3.mkBVSrem(rec(l), rec(r))
        case BVType(false, _) => z3.mkBVUrem(rec(l), rec(r))
        case _ =>
          val q = rec(Division(l, r))
          z3.mkSub(rec(l), z3.mkMul(rec(r), q))
      }

      case Modulo(l, r) => l.getType match {
        case BVType(false, _) => z3.mkBVUrem(rec(l), rec(r))
        case BVType(true, size) => // we want x mod |y|
          val lr = rec(l)
          val rr = rec(r)
          z3.mkBVSmod(
            lr,
            z3.mkITE(
              z3.mkBVSle(rr, rec(BVLiteral(true, 0, size))),
              z3.mkBVNeg(rr),
              rr
            )
          )

        case _ =>
          z3.mkMod(rec(l), rec(r))
      }

      case UMinus(e) => e.getType match {
        case BVType(_,_) => z3.mkBVNeg(rec(e))
        case _ => z3.mkUnaryMinus(rec(e))
      }

      case BVNot(e) => z3.mkBVNot(rec(e))
      case BVAnd(l, r) => z3.mkBVAnd(rec(l), rec(r))
      case BVOr(l, r) => z3.mkBVOr(rec(l), rec(r))
      case BVXor(l, r) => z3.mkBVXor(rec(l), rec(r))
      case BVShiftLeft(l, r) => z3.mkBVShl(rec(l), rec(r))
      case BVAShiftRight(l, r) => z3.mkBVAshr(rec(l), rec(r))
      case BVLShiftRight(l, r) => z3.mkBVLshr(rec(l), rec(r))

      case c @ BVWideningCast(e, _)  =>
        val Some((from, to)) = c.cast
        val BVType(signed, _) = e.getType
        if (signed) z3.mkSignExt(to - from, rec(e))
        else z3.mkZeroExt(to - from, rec(e))

      case c @ BVNarrowingCast(e, _) =>
        val Some((from, to)) = c.cast
        z3.mkExtract(to - 1, 0, rec(e))

      case BVUnsignedToSigned(e) => rec(e)
      case BVSignedToUnsigned(e) => rec(e)

      case LessThan(l, r) => l.getType match {
        case IntegerType() => z3.mkLT(rec(l), rec(r))
        case RealType() => z3.mkLT(rec(l), rec(r))
        case BVType(true,_) => z3.mkBVSlt(rec(l), rec(r))
        case BVType(false,_) => z3.mkBVUlt(rec(l), rec(r))
        case CharType() => z3.mkBVUlt(rec(l), rec(r))
      }
      case LessEquals(l, r) => l.getType match {
        case IntegerType() => z3.mkLE(rec(l), rec(r))
        case RealType() => z3.mkLE(rec(l), rec(r))
        case BVType(true,_) => z3.mkBVSle(rec(l), rec(r))
        case BVType(false,_) => z3.mkBVUle(rec(l), rec(r))
        case CharType() => z3.mkBVUle(rec(l), rec(r))
      }
      case GreaterThan(l, r) => l.getType match {
        case IntegerType() => z3.mkGT(rec(l), rec(r))
        case RealType() => z3.mkGT(rec(l), rec(r))
        case BVType(true,_) => z3.mkBVSgt(rec(l), rec(r))
        case BVType(false,_) => z3.mkBVUgt(rec(l), rec(r))
        case CharType() => z3.mkBVUgt(rec(l), rec(r))
      }
      case GreaterEquals(l, r) => l.getType match {
        case IntegerType() => z3.mkGE(rec(l), rec(r))
        case RealType() => z3.mkGE(rec(l), rec(r))
        case BVType(true,_) => z3.mkBVSge(rec(l), rec(r))
        case BVType(false,_) => z3.mkBVUge(rec(l), rec(r))
        case CharType() => z3.mkBVUge(rec(l), rec(r))
      }

      case u : UnitLiteral =>
        typeToSort(u.getType)
        val constructor = constructors.toB(UnitCons)
        constructor()

      case t @ Tuple(es) =>
        val tpe @ TupleType(tps) = t.getType
        typeToSort(tpe)
        val constructor = constructors.toB(TupleCons(tps))
        constructor(es.map(rec): _*)

      case ts @ TupleSelect(t, i) =>
        val tpe @ TupleType(tps) = t.getType
        typeToSort(tpe)
        val selector = selectors.toB((TupleCons(tps), i-1))
        selector(rec(t))

      case c @ ADT(id, tps, args) =>
        typeToSort(c.getType) // Making sure the sort is defined
        val constructor = constructors.toB(ADTCons(id, tps.map(_.getType)))
        constructor(args.map(rec): _*)

      case c @ ADTSelector(cc, sel) =>
        val tpe @ ADTType(_, tps) = cc.getType
        typeToSort(tpe) // Making sure the sort is defined
        val selector = selectors.toB(ADTCons(c.constructor.id, tps) -> c.selectorIndex)
        selector(rec(cc))

      case IsConstructor(e, id) =>
        val tpe @ ADTType(_, tps) = e.getType
        typeToSort(tpe)
        val tester = testers.toB(ADTCons(id, tps))
        tester(rec(e))

      case f @ FunctionInvocation(id, tps, args) =>
        z3.mkApp(functionDefToDecl(getFunction(id, tps.map(_.getType))), args.map(rec): _*)

      case fa @ Application(caller, args) =>
        val ft @ FunctionType(froms, to) = caller.getType
        val funDecl = lambdas.cachedB(ft) {
          val sortSeq    = (ft +: froms).map(tpe => typeToSort(tpe))
          val returnSort = typeToSort(to)

          val name = FreshIdentifier("dynLambda").uniqueName
          z3.mkFreshFuncDecl(name, sortSeq, returnSort)
        }
        z3.mkApp(funDecl, (caller +: args).map(rec): _*)

      /**
       * ===== Set operations =====
       */
      case f @ FiniteSet(elems, base) =>
        elems.foldLeft(z3.mkEmptySet(typeToSort(base.getType)))((ast, el) => z3.mkSetAdd(ast, rec(el)))

      case ElementOfSet(e, s) => z3.mkSetMember(rec(e), rec(s))

      case SubsetOf(s1, s2) => z3.mkSetSubset(rec(s1), rec(s2))

      case SetIntersection(s1, s2) => z3.mkSetIntersect(rec(s1), rec(s2))

      case SetUnion(s1, s2) => z3.mkSetUnion(rec(s1), rec(s2))

      case SetAdd(s, e) => z3.mkSetAdd(rec(s), rec(e))

      case SetDifference(s1, s2) => z3.mkSetDifference(rec(s1), rec(s2))

      /**
       * ===== Bag operations =====
       */
      case fb @ FiniteBag(elems, base) =>
        typeToSort(fb.getType)
        rec(FiniteMap(elems, IntegerLiteral(0), base, IntegerType()))

      case BagAdd(b, e) =>
        val (bag, elem) = (rec(b), rec(e))
        z3.mkStore(bag, elem, z3.mkAdd(z3.mkSelect(bag, elem), rec(IntegerLiteral(1))))

      case MultiplicityInBag(e, b) =>
        z3.mkSelect(rec(b), rec(e))

      case BagUnion(b1, b2) =>
        val plus = z3.getFuncDecl(OpAdd, typeToSort(IntegerType()), typeToSort(IntegerType()))
        z3.mkArrayMap(plus, rec(b1), rec(b2))

      case BagIntersection(b1, b2) =>
        rec(BagDifference(b1, BagDifference(b1, b2)))

      case BagDifference(b1, b2) =>
        val BagType(base) = b1.getType
        val abs = z3.getAbsFuncDecl()
        val plus = z3.getFuncDecl(OpAdd, typeToSort(IntegerType()), typeToSort(IntegerType()))
        val minus = z3.getFuncDecl(OpSub, typeToSort(IntegerType()), typeToSort(IntegerType()))
        val div = z3.getFuncDecl(OpDiv, typeToSort(IntegerType()), typeToSort(IntegerType()))

        val all2 = z3.mkConstArray(typeToSort(base), z3.mkInt(2, typeToSort(IntegerType())))
        val withNeg = z3.mkArrayMap(minus, rec(b1), rec(b2))
        z3.mkArrayMap(div, z3.mkArrayMap(plus, withNeg, z3.mkArrayMap(abs, withNeg)), all2)

      /**
       * ===== Map operations =====
       */
      case al @ MapApply(a, i) =>
        z3.mkSelect(rec(a), rec(i))

      case al @ MapUpdated(a, i, e) =>
        z3.mkStore(rec(a), rec(i), rec(e))

      case FiniteMap(elems, default, keyTpe, valueType) =>
        val ar = z3.mkConstArray(typeToSort(keyTpe.getType), rec(default))

        elems.foldLeft(ar) {
          case (array, (k, v)) => z3.mkStore(array, rec(k), rec(v))
        }

      case MapMerge(mask, map1, map2) =>
        // TODO: This should move to scala-z3
        def getIteFuncDecl(valueTpe: Type) = {
          val valueSort = typeToSort(valueTpe)
          val app = z3.mkITE(
            z3.mkFreshConst("b", typeToSort(BooleanType())),
            z3.mkFreshConst("v1", valueSort),
            z3.mkFreshConst("v2", valueSort))
          z3.getASTKind(app) match {
            case Z3AppAST(decl, _) => decl
            case _ => error("Unexpected non-app AST " + app)
          }
        }

        val MapType(_, valueTpe) = map1.getType
        z3.mkArrayMap(getIteFuncDecl(valueTpe), rec(mask), rec(map1), rec(map2))

      /* ====== String operations ====
       * FIXME: replace z3 strings with sequences once they are fixed (in z3)
       */
      case StringLiteral(v) =>
        z3.mkString(v)

      case StringLength(a) =>
        z3.mkSeqLength(rec(a))

      case StringConcat(a, b) =>
        z3.mkSeqConcat(rec(a), rec(b))

      case SubString(a, start, Plus(start2, length)) if start == start2 =>
        z3.mkSeqExtract(rec(a), rec(start), rec(length))

      case SubString(a, start, end) =>
        z3.mkSeqExtract(rec(a), rec(start), rec(Minus(end, start)))

      case gv @ GenericValue(tp, id) =>
        typeToSort(tp)
        val constructor = constructors.toB(TypeParameterCons(tp))
        constructor(rec(IntegerLiteral(id)))

      case other =>
        unsupported(other)
    }

    val res = rec(expr)(bindings)
    res
  }

  protected lazy val emptySeq = {
    z3.getASTKind(z3.mkEmptySeq(typeToSort(StringType()))) match {
      case Z3AppAST(decl, _) => decl
      case ast => error("Unexpected non-app AST " + ast)
    }
  }

  protected[z3] def fromZ3Formula(model: Z3Model, tree: Z3AST, tpe: Type): (Expr, Map[Choose, Expr]) = {
    val z3ToChooses: MutableMap[Z3AST, Choose] = MutableMap.empty
    val z3ToLambdas: MutableMap[Z3AST, Lambda] = MutableMap.empty

    def rec(t: Z3AST, tpe: Type, seen: Set[Z3AST]): Expr = {
      val kind = z3.getASTKind(t)
      kind match {
        case Z3NumeralIntAST(Some(v)) =>
          tpe match {
            case BVType(signed, size) => BVLiteral(signed, BigInt(v), size)
            case CharType() => CharLiteral(v.toChar)
            case IntegerType() => IntegerLiteral(BigInt(v))
            case other => unsupported(other, s"Unexpected target type for value $v")
          }

        case Z3NumeralIntAST(None) =>
          val ts = t.toString
          tpe match {
            case BVType(signed, size) =>
              if (ts.startsWith("#b")) BVLiteral(signed, BigInt(ts.drop(2), 2), size)
              else if (ts.startsWith("#x")) BVLiteral(signed, BigInt(ts.drop(2), 16), size)
              else if (ts.startsWith("#")) throw new InternalSolverError("z3", s"Unexpected format for BV value: $ts")
              else BVLiteral(signed, BigInt(ts, 10), size)

            case IntegerType() =>
              if (ts.startsWith("#")) throw new InternalSolverError("z3", s"Unexpected format for Integer value: $ts")
              else IntegerLiteral(BigInt(ts, 10))

            case other => unsupported(other, s"Unexpected target type for value $ts")
          }

        case Z3NumeralRealAST(n: BigInt, d: BigInt) => FractionLiteral(n, d)

        case Z3AppAST(decl, args) =>
          val argsSize = args.size
          if (argsSize == 0 && (variables containsB t)) {
            variables.toA(t)
          } else if(functions containsB decl) {
            val tfd = functions.toA(decl)
            assert(tfd.params.size == argsSize)
            FunctionInvocation(tfd.id, tfd.tps, args.zip(tfd.params).map{ case (a, p) => rec(a, p.getType, seen) })
          } else if (constructors containsB decl) {
            constructors.toA(decl) match {
              case ADTCons(id, tps) =>
                ADT(id, tps, args zip getConstructor(id, tps).fields map { case (a, vd) => rec(a, vd.getType, seen) })

              case UnitCons =>
                UnitLiteral()

              case TupleCons(ts) =>
                tupleWrap(args.zip(ts).map { case (a, t) => rec(a, t, seen) })

              case TypeParameterCons(tp) =>
                val IntegerLiteral(n) = rec(args(0), IntegerType(), seen)
                GenericValue(tp, n.toInt)

              case t =>
                unsupported(t, "Woot? structural type that is non-structural")
            }
          } else {
            tpe match {
              case ft: FunctionType if seen(t) => z3ToChooses.getOrElse(t, {
                val res = Choose(Variable.fresh("x", ft, true).toVal, BooleanLiteral(true))
                z3ToChooses(t) = res
                res
              })

              case ft @ FunctionType(fts, tt) => z3ToLambdas.getOrElse(t, {
                val n = t.toString.split("!").last.init.toInt
                val args = fts.map(tpe => ValDef.fresh("x", tpe, true))
                val res = uniquateClosure(n, lambdas.getB(ft)
                  .flatMap(decl => model.getFuncInterpretations.find(_._1 == decl))
                  .map { case (_, mapping, elseValue) =>
                    val body = mapping.foldLeft(rec(elseValue, tt, seen + t)) { case (elze, (z3Args, z3Result)) =>
                      if (t == z3Args.head) {
                        val cond = andJoin((args zip z3Args.tail).map { case (vd, z3Arg) =>
                          Equals(vd.toVariable, rec(z3Arg, vd.getType, seen + t))
                        })

                        IfExpr(cond, rec(z3Result, tt, seen + t), elze)
                      } else {
                        elze
                      }
                    }

                    Lambda(args, body)
                  }.getOrElse(try {
                    simplestValue(ft, allowSolver = false).asInstanceOf[Lambda]
                  } catch {
                    case _: NoSimpleValue =>
                      Lambda(args, Choose(ValDef.fresh("res", tt), BooleanLiteral(true)))
                  }))

                z3ToLambdas(t) = res
                res
              })

              case MapType(from, to) =>
                model.getArrayValue(t) match {
                  case Some((z3map, z3default)) =>
                    val default = rec(z3default, to, seen)
                    val entries = z3map.map {
                      case (k,v) => (rec(k, from, seen), rec(v, to, seen))
                    }

                    FiniteMap(entries.toSeq, default, from, to)
                  case None => unsound(t, "invalid array AST")
                }

              case BagType(base) =>
                val fm @ FiniteMap(entries, default, from, IntegerType()) = rec(t, MapType(base, IntegerType()), seen)
                if (default != IntegerLiteral(0)) {
                  unsound(t, "co-finite bag AST")
                }

                FiniteBag(entries, base)

              case tpe @ SetType(dt) =>
                model.getSetValue(t) match {
                  case None => unsound(t, "invalid set AST")
                  case Some((_, false)) => unsound(t, "co-finite set AST")
                  case Some((set, true)) =>
                    val elems = set.map(e => rec(e, dt, seen))
                    FiniteSet(elems.toSeq, dt)
                }

              case StringType() => StringLiteral(utils.StringUtils.decode(z3.getString(t)))

              case _ =>
                import Z3DeclKind._
                z3.getDeclKind(decl) match {
                  case OpTrue =>    BooleanLiteral(true)
                  case OpFalse =>   BooleanLiteral(false)
            //      case OpEq =>      Equals(rargs(0), rargs(1))
            //      case OpITE =>     IfExpr(rargs(0), rargs(1), rargs(2))
            //      case OpAnd =>     andJoin(rargs)
            //      case OpOr =>      orJoin(rargs)
            //      case OpIff =>     Equals(rargs(0), rargs(1))
            //      case OpXor =>     not(Equals(rargs(0), rargs(1)))
            //      case OpNot =>     not(rargs(0))
            //      case OpImplies => implies(rargs(0), rargs(1))
            //      case OpLE =>      LessEquals(rargs(0), rargs(1))
            //      case OpGE =>      GreaterEquals(rargs(0), rargs(1))
            //      case OpLT =>      LessThan(rargs(0), rargs(1))
            //      case OpGT =>      GreaterThan(rargs(0), rargs(1))
            //      case OpAdd =>     Plus(rargs(0), rargs(1))
            //      case OpSub =>     Minus(rargs(0), rargs(1))
                  case OpUMinus =>  UMinus(rec(args(0), tpe, seen))
            //      case OpMul =>     Times(rargs(0), rargs(1))
            //      case OpDiv =>     Division(rargs(0), rargs(1))
            //      case OpIDiv =>    Division(rargs(0), rargs(1))
            //      case OpMod =>     Modulo(rargs(0), rargs(1))

                  case other => unsound(t,
                      s"""|Don't know what to do with this declKind: $other
                          |Expected type: ${Option(tpe).map{_.asString}.getOrElse("")}
                          |Tree: $t
                          |The arguments are: $args""".stripMargin
                    )
                }
            }
          }
        case _ => unsound(t, "unexpected AST")
      }
    }

    val res = rec(tree, tpe, Set.empty)
    val chooses = z3ToChooses.toMap.map { case (ast, c) => c -> z3ToLambdas(ast) }

    (res, chooses)
  }

  // Tries to convert a Z3AST into a *ground* Expr. Doesn't try very hard, because
  //   1) we assume Z3 simplifies ground terms, so why match for +, etc, and
  //   2) we use this precisely in one context, where we know function invocations won't show up, etc.
  protected[z3] def asGround(tree: Z3AST, tpe: Type): Option[Expr] = {

    def rec(t: Z3AST, tpe: Type): Expr = z3.getASTKind(t) match {
      case Z3NumeralIntAST(Some(v)) =>
        tpe match {
          case BVType(signed, size) => BVLiteral(signed, BigInt(v), size)
          case CharType() => CharLiteral(v.toChar)
          case _ => IntegerLiteral(BigInt(v))
        }

      case Z3NumeralIntAST(None) =>
        val ts = t.toString
        tpe match {
          case BVType(signed, size) =>
            if (ts.startsWith("#b")) BVLiteral(signed, BigInt(ts.drop(2), 2), size)
            else if (ts.startsWith("#x")) BVLiteral(signed, BigInt(ts.drop(2), 16), size)
            else if (ts.startsWith("#")) unsound(t, s"Unexpected format for BV value: $ts")
            else BVLiteral(signed, BigInt(ts, 10), size)

          case _ =>
            if (ts.startsWith("#")) unsound(t, s"Unexpected format for Integer value: $ts")
            else IntegerLiteral(BigInt(ts, 10))
        }

      case Z3NumeralRealAST(n: BigInt, d: BigInt) => FractionLiteral(n, d)

      case Z3AppAST(decl, args) => {
        val argsSize = args.size
        if (functions containsB decl) {
          val tfd = functions.toA(decl)
          FunctionInvocation(tfd.id, tfd.tps, (args zip tfd.params).map(p => rec(p._1, p._2.getType)))
        } else if (lambdas containsB decl) {
          val ft @ FunctionType(from, _) = lambdas.toA(decl)
          Application(rec(args.head, ft), (args.tail zip from).map(p => rec(p._1, p._2)))
        } else if (argsSize == 0 && (variables containsB t)) {
          variables.toA(t)
        } else if (argsSize == 1 && (testers containsB decl)) {
          testers.toA(decl) match {
            case c @ ADTCons(id, tps) => IsConstructor(rec(args(0), c.getType), id)
            case _ => BooleanLiteral(true)
          }
        } else if (argsSize == 1 && (selectors containsB decl)) {
          selectors.toA(decl) match {
            case (c @ ADTCons(id, tps), i) =>
              ADTSelector(rec(args(0), c.getType), getConstructor(id).fields(i).id)
            case (c @ TupleCons(tps), i) =>
              TupleSelect(rec(args(0), c.getType), i + 1)
            case _ => unsound(t, "Unexpected selector tree")
          }
        } else if (constructors containsB decl) {
          constructors.toA(decl) match {
            case c @ ADTCons(id, tps) =>
              ADT(id, tps, (args zip getConstructor(id, tps).fields).map(p => rec(p._1, p._2.getType)))
            case c @ TupleCons(tps) =>
              Tuple((args zip tps).map(p => rec(p._1, p._2)))
            case UnitCons => UnitLiteral()
            case _ => unsound(t, "Unexpected constructor tree")
          }
        } else {
          import Z3DeclKind._
          z3.getDeclKind(decl) match {
            case OpTrue => BooleanLiteral(true)
            case OpFalse => BooleanLiteral(false)
            case op => unsound(t, "Unexpected decl kind: " + op)
          }
        }
      }

      case _ => unsound(t, "Unexpected tree")
    }

    try {
      Some(rec(tree, tpe))
    } catch {
      case _: UnsoundExtractionException => None
    }
  }

  protected[z3] def softFromZ3Formula(model: Z3Model, tree: Z3AST, tpe: Type) : Option[(Expr, Map[Choose, Expr])] = {
    try {
      Some(fromZ3Formula(model, tree, tpe))
    } catch {
      case e: Unsupported => None
      case e: UnsoundExtractionException => None
      case n: java.lang.NumberFormatException => None
    }
  }

  def symbolToFreshZ3Symbol(v: Variable): Z3AST = {
    z3.mkFreshConst(v.id.uniqueName, typeToSort(v.getType))
  }

  def extractNot(e: Z3AST): Option[Z3AST] = z3.getASTKind(e) match {
    case Z3AppAST(decl, args) => z3.getDeclKind(decl) match {
      case OpNot => Some(args.head)
      case _ => None
    }
    case _ => None
  }

  private[z3] class ModelExtractor(model: Z3Model) {
    private val innerChooses: MutableMap[Identifier, Expr] = MutableMap.empty

    def apply(z3ast: Z3AST, tpe: Type): Expr = {
      val (e, cs) = fromZ3Formula(model, z3ast, tpe)
      innerChooses ++= cs.map(p => p._1.res.id -> p._2)
      e
    }

    def get(z3ast: Z3AST, tpe: Type): Option[Expr] =
      softFromZ3Formula(model, z3ast, tpe).map { case (e, cs) =>
        innerChooses ++= cs.map(p => p._1.res.id -> p._2)
        e
      }

    def chooses = innerChooses.toMap
  }

  def extractModel(model: Z3Model): program.Model = {
    val ex = new ModelExtractor(model)

    val vars = variables.aToB.flatMap {
      /** WARNING this code is very similar to Z3Unrolling.modelEval!!! */
      case (v,z3ID) => (v.getType match {
        case BooleanType() =>
          model.evalAs[Boolean](z3ID).map(BooleanLiteral)

        case Int32Type() =>
          model.evalAs[Int](z3ID).map(Int32Literal(_)).orElse {
            model.eval(z3ID).flatMap(t => ex.get(t, Int32Type()))
          }

         /*
          * NOTE The following could be faster than the default case, but be carefull to
          *      fallback to the default when a BigInt doesn't fit in a regular Int.
          *
          * case IntegerType() =>
          *  model.evalAs[Int](z3ID).map(IntegerLiteral(_)).orElse {
          *    model.eval(z3ID).flatMap(ex.get(_, IntegerType()))
          *  }
          */

        case other => model.eval(z3ID).flatMap(t => ex.get(t, other))
      }).map(v.toVal -> _)
    }

    val chooses: MutableMap[(Identifier, Seq[Type]), Expr] = MutableMap.empty
    chooses ++= ex.chooses.map(p => (p._1, Seq.empty[Type]) -> p._2)

    chooses ++= model.getFuncInterpretations.flatMap { case (decl, mapping, _) =>
      functions.getA(decl).flatMap(tfd => tfd.fullBody match {
        case c: Choose =>
          val ex = new ModelExtractor(model)
          val body = mapping.foldRight(c: Expr) { case ((args, res), elze) =>
            IfExpr(andJoin((tfd.params.map(_.toVariable) zip args).map {
              case (v, e) => Equals(v, ex(e, v.getType))
            }), ex(res, tfd.getType), elze)
          }
          chooses ++= ex.chooses.map(p => (p._1, tfd.tps) -> p._2)
          Some((c.res.id, tfd.tps) -> body)
        case _ => None
      })
    }.toMap

    inox.Model(program)(vars, chooses.toMap)
  }

  def extractUnsatAssumptions(cores: Set[Z3AST]): Set[Expr] = {
    cores.flatMap { c =>
      variables.getA(c).orElse(z3.getASTKind(c) match {
        case Z3AppAST(decl, args) => z3.getDeclKind(decl) match {
          case OpNot => variables.getA(args.head)
          case _ => None
        }
        case ast => None
      })
    }
  }
}
