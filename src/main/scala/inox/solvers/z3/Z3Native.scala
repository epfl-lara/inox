/* Copyright 2009-2016 EPFL, Lausanne */

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

  import program._
  import program.trees._
  import program.symbols._
  import program.symbols.bestRealType

  type Trees = Z3AST
  type Model = Z3Model

  protected implicit val semantics: program.Semantics

  ctx.interruptManager.registerForInterrupts(this)

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

  def free(): Unit = {
    freed = true
    if (z3 ne null) {
      z3.delete()
      z3 = null
    }
    ctx.interruptManager.unregisterForInterrupts(this)
  }

  def interrupt(): Unit = {
    if(z3 ne null) {
      z3.interrupt()
    }
  }

  def functionDefToDecl(tfd: TypedFunDef): Z3FuncDecl = {
    functions.cachedB(tfd) {
      val sortSeq    = tfd.params.map(vd => typeToSort(vd.getType))
      val returnSort = typeToSort(tfd.returnType)

      z3.mkFreshFuncDecl(tfd.id.uniqueName, sortSeq, returnSort)
    }
  }

  def declareVariable(v: Variable): Z3AST = variables.cachedB(v) {
    symbolToFreshZ3Symbol(v)
  }

  // ADT Manager
  private[z3] val adtManager = new ADTManager

  // Bije[z3]ctions between Inox Types/Functions/Ids to Z3 Sorts/Decls/ASTs
  private[z3] val functions = new IncrementalBijection[TypedFunDef, Z3FuncDecl]()
  private[z3] val lambdas   = new IncrementalBijection[FunctionType, Z3FuncDecl]()
  private[z3] val variables = new IncrementalBijection[Variable, Z3AST]()

  private[z3] val constructors = new IncrementalBijection[Type, Z3FuncDecl]()
  private[z3] val selectors    = new IncrementalBijection[(Type, Int), Z3FuncDecl]()
  private[z3] val testers      = new IncrementalBijection[Type, Z3FuncDecl]()

  private[z3] val sorts     = new IncrementalMap[Type, Z3Sort]()

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
      val tpe = tt match {
        case adt: ADTType => adt.getADT.root.toType
        case _ => tt
      }

      if (indexMap contains tpe) {
        RecursiveType(indexMap(tpe))
      } else {
        RegularSort(typeToSort(tt))
      }
    }

    // Define stuff
    val defs = for ((_, DataType(sym, cases)) <- adts) yield {(
      sym.uniqueName,
      cases.map(c => c.sym.uniqueName),
      cases.map(c => c.fields.map { case(id, tpe) => (id.uniqueName, typeToSortRef(tpe))})
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
  sorts += Int32Type -> z3.mkBVSort(32)
  sorts += CharType -> z3.mkBVSort(16)
  sorts += IntegerType -> z3.mkIntSort
  sorts += RealType -> z3.mkRealSort
  sorts += BooleanType -> z3.mkBoolSort
  sorts += StringType -> z3.mkSeqSort(z3.mkBVSort(16))

  // assumes prepareSorts has been called....
  protected def typeToSort(oldtt: Type): Z3Sort = bestRealType(oldtt) match {
    case Int32Type | BooleanType | IntegerType | RealType | CharType | StringType =>
      sorts(oldtt)

    case tt @ BVType(i) =>
      sorts.cached(tt) {
        z3.mkBVSort(i)
      }

    case tpe @ (_: ADTType  | _: TupleType | _: TypeParameter | UnitType) =>
      if (!sorts.contains(tpe)) declareStructuralSort(tpe)
      sorts(tpe)

    case tt @ SetType(base) =>
      sorts.cached(tt) {
        declareStructuralSort(tt)
        z3.mkSetSort(typeToSort(base))
      }

    case tt @ BagType(base) =>
      typeToSort(MapType(base, IntegerType))

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
      case IntLiteral(v) => z3.mkInt(v, typeToSort(Int32Type))
      case IntegerLiteral(v) => z3.mkNumeral(v.toString, typeToSort(IntegerType))
      case FractionLiteral(n, d) => z3.mkNumeral(s"$n / $d", typeToSort(RealType))
      case CharLiteral(c) => z3.mkInt(c, typeToSort(CharType))
      case BooleanLiteral(v) => if (v) z3.mkTrue() else z3.mkFalse()
      case Equals(l, r) => z3.mkEq(rec( l ), rec( r ) )
      case Plus(l, r) => l.getType match {
        case BVType(_) => z3.mkBVAdd(rec(l), rec(r))
        case _ => z3.mkAdd(rec(l), rec(r))
      }
      case Minus(l, r) => l.getType match {
        case BVType(_) => z3.mkBVSub(rec(l), rec(r))
        case _ => z3.mkSub(rec(l), rec(r))
      }
      case Times(l, r) => l.getType match {
        case BVType(_) => z3.mkBVMul(rec(l), rec(r))
        case _ => z3.mkMul(rec(l), rec(r))
      }
      case Division(l, r) =>
        val (rl, rr) = (rec(l), rec(r))
        l.getType match {
          case IntegerType =>
            z3.mkITE(
              z3.mkGE(rl, z3.mkNumeral("0", typeToSort(IntegerType))),
              z3.mkDiv(rl, rr),
              z3.mkUnaryMinus(z3.mkDiv(z3.mkUnaryMinus(rl), rr))
            )
          case BVType(_) => z3.mkBVSdiv(rl, rr)
          case _ => z3.mkDiv(rl, rr)
        }
      case Remainder(l, r) => l.getType match {
        case BVType(_) => z3.mkBVSrem(rec(l), rec(r))
        case _ =>
          val q = rec(Division(l, r))
          z3.mkSub(rec(l), z3.mkMul(rec(r), q))
      }
      case Modulo(l, r) => z3.mkMod(rec(l), rec(r))
      case UMinus(e) => e.getType match {
        case BVType(_) => z3.mkBVNeg(rec(e))
        case _ => z3.mkUnaryMinus(rec(e))
      }

      case BVNot(e) => z3.mkBVNot(rec(e))
      case BVAnd(l, r) => z3.mkBVAnd(rec(l), rec(r))
      case BVOr(l, r) => z3.mkBVOr(rec(l), rec(r))
      case BVXor(l, r) => z3.mkBVXor(rec(l), rec(r))
      case BVShiftLeft(l, r) => z3.mkBVShl(rec(l), rec(r))
      case BVAShiftRight(l, r) => z3.mkBVAshr(rec(l), rec(r))
      case BVLShiftRight(l, r) => z3.mkBVLshr(rec(l), rec(r))
      case LessThan(l, r) => l.getType match {
        case IntegerType => z3.mkLT(rec(l), rec(r))
        case RealType => z3.mkLT(rec(l), rec(r))
        case Int32Type => z3.mkBVSlt(rec(l), rec(r))
        case CharType => z3.mkBVUlt(rec(l), rec(r))
      }
      case LessEquals(l, r) => l.getType match {
        case IntegerType => z3.mkLE(rec(l), rec(r))
        case RealType => z3.mkLE(rec(l), rec(r))
        case Int32Type => z3.mkBVSle(rec(l), rec(r))
        case CharType => z3.mkBVUle(rec(l), rec(r))
      }
      case GreaterThan(l, r) => l.getType match {
        case IntegerType => z3.mkGT(rec(l), rec(r))
        case RealType => z3.mkGT(rec(l), rec(r))
        case Int32Type => z3.mkBVSgt(rec(l), rec(r))
        case CharType => z3.mkBVUgt(rec(l), rec(r))
      }
      case GreaterEquals(l, r) => l.getType match {
        case IntegerType => z3.mkGE(rec(l), rec(r))
        case RealType => z3.mkGE(rec(l), rec(r))
        case Int32Type => z3.mkBVSge(rec(l), rec(r))
        case CharType => z3.mkBVUge(rec(l), rec(r))
      }

      case u : UnitLiteral =>
        val tpe = bestRealType(u.getType)
        typeToSort(tpe)
        val constructor = constructors.toB(tpe)
        constructor()

      case t @ Tuple(es) =>
        val tpe = bestRealType(t.getType)
        typeToSort(tpe)
        val constructor = constructors.toB(tpe)
        constructor(es.map(rec): _*)

      case ts @ TupleSelect(t, i) =>
        val tpe = bestRealType(t.getType)
        typeToSort(tpe)
        val selector = selectors.toB((tpe, i-1))
        selector(rec(t))

      case c @ ADT(ADTType(id, tps), args) =>
        val adt = ADTType(id, tps map bestRealType)
        typeToSort(adt) // Making sure the sort is defined
        val constructor = constructors.toB(adt)
        constructor(args.map(rec): _*)

      case c @ ADTSelector(cc, sel) =>
        val ADTType(id, tps) = cc.getType
        val adt = ADTType(id, tps map bestRealType)
        typeToSort(adt) // Making sure the sort is defined
        val selector = selectors.toB(adt -> c.selectorIndex)
        selector(rec(cc))

      case AsInstanceOf(expr, adt) =>
        rec(expr)

      case IsInstanceOf(e, ADTType(id, tps)) =>
        val adt = ADTType(id, tps map bestRealType)
        adt.getADT match {
          case tsort: TypedADTSort =>
            tsort.constructors match {
              case Seq(tcons) =>
                rec(IsInstanceOf(e, tcons.toType))
              case more =>
                val v = Variable.fresh("e", adt, true)
                rec(Let(v.toVal, e, orJoin(more map (tcons => IsInstanceOf(v, tcons.toType)))))
            }
          case tcons: TypedADTConstructor =>
            typeToSort(adt)
            val tester = testers.toB(adt)
            tester(rec(e))
        }

      case f @ FunctionInvocation(id, tps, args) =>
        z3.mkApp(functionDefToDecl(getFunction(id, tps)), args.map(rec): _*)

      case fa @ Application(caller, args) =>
        val ft @ FunctionType(froms, to) = bestRealType(caller.getType)
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
        elems.foldLeft(z3.mkEmptySet(typeToSort(base)))((ast, el) => z3.mkSetAdd(ast, rec(el)))

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
        rec(FiniteMap(elems, IntegerLiteral(0), base, IntegerType))

      case BagAdd(b, e) =>
        val (bag, elem) = (rec(b), rec(e))
        z3.mkStore(bag, elem, z3.mkAdd(z3.mkSelect(bag, elem), rec(IntegerLiteral(1))))

      case MultiplicityInBag(e, b) =>
        z3.mkSelect(rec(b), rec(e))

      case BagUnion(b1, b2) =>
        val plus = z3.getFuncDecl(OpAdd, typeToSort(IntegerType), typeToSort(IntegerType))
        z3.mkArrayMap(plus, rec(b1), rec(b2))

      case BagIntersection(b1, b2) =>
        rec(BagDifference(b1, BagDifference(b1, b2)))

      case BagDifference(b1, b2) =>
        val abs = z3.getAbsFuncDecl()
        val plus = z3.getFuncDecl(OpAdd, typeToSort(IntegerType), typeToSort(IntegerType))
        val minus = z3.getFuncDecl(OpSub, typeToSort(IntegerType), typeToSort(IntegerType))
        val div = z3.getFuncDecl(OpDiv, typeToSort(IntegerType), typeToSort(IntegerType))

        val all2 = z3.mkConstArray(typeToSort(IntegerType), z3.mkInt(2, typeToSort(IntegerType)))
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
        val ar = z3.mkConstArray(typeToSort(keyTpe), rec(default))

        elems.foldLeft(ar) {
          case (array, (k, v)) => z3.mkStore(array, rec(k), rec(v))
        }

      /**
       * ====== String operations ====
       */
      case StringLiteral(v) => v.map(c => z3.mkUnitSeq(z3.mkInt(c, typeToSort(CharType)))) match {
        case Seq() => z3.mkEmptySeq(typeToSort(CharType))
        case Seq(e) => e
        case es => z3.mkSeqConcat(es : _*)
      }

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
        val constructor = constructors.toB(tp)
        constructor(rec(IntegerLiteral(id)))

      case other =>
        unsupported(other)
    }

    val res = rec(expr)(bindings)
    res
  }

  protected[z3] def fromZ3Formula(model: Z3Model, tree: Z3AST, tpe: Type): (Expr, Map[Choose, Expr]) = {

    val z3ToChooses: MutableMap[Z3AST, Choose] = MutableMap.empty
    val z3ToLambdas: MutableMap[Z3AST, Lambda] = MutableMap.empty

    def rec(t: Z3AST, tpe: Type, seen: Set[Z3AST]): Expr = {
      val kind = z3.getASTKind(t)
      kind match {
        case Z3NumeralIntAST(Some(v)) =>
          val leading = t.toString.substring(0, 2 min t.toString.length)
          if (leading == "#x") {
            _root_.smtlib.common.Hexadecimal.fromString(t.toString.substring(2)) match {
              case Some(hexa) =>
                tpe match {
                  case Int32Type => IntLiteral(hexa.toInt)
                  case CharType  => CharLiteral(hexa.toInt.toChar)
                  case IntegerType => IntegerLiteral(BigInt(hexa.toInt))
                  case other =>
                    unsupported(other, "Unexpected target type for BV value")
                }
              case None => unsound(t, "could not translate hexadecimal Z3 numeral")
              }
          } else {
            tpe match {
              case Int32Type => IntLiteral(v)
              case CharType  => CharLiteral(v.toChar)
              case IntegerType => IntegerLiteral(BigInt(v))
              case other =>
                unsupported(other, "Unexpected type for BV value: " + other)
            } 
          }

        case Z3NumeralIntAST(None) =>
          val ts = t.toString
          if(ts.length > 4 && ts.substring(0, 2) == "bv" && ts.substring(ts.length - 4) == "[32]") {
            val integer = ts.substring(2, ts.length - 4)
            tpe match {
              case Int32Type => IntLiteral(integer.toLong.toInt)
              case CharType  => CharLiteral(integer.toInt.toChar)
              // @nv XXX: why would we have this!? case IntegerType => IntegerLiteral(BigInt(integer))
              case _ =>
                reporter.fatalError("Unexpected target type for BV value: " + tpe.asString)
            }
          } else {  
            _root_.smtlib.common.Hexadecimal.fromString(t.toString.substring(2)) match {
              case Some(hexa) =>
                tpe match {
                  case Int32Type => IntLiteral(hexa.toInt)
                  case CharType  => CharLiteral(hexa.toInt.toChar)
                  case _ => unsound(t, "unexpected target type for BV value: " + tpe.asString)
                }
              case None => unsound(t, "could not translate Z3NumeralIntAST numeral")
            }
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
              case adt: ADTType =>
                ADT(adt, args.zip(adt.getADT.toConstructor.fieldsTypes).map { case (a, t) => rec(a, t, seen) })

              case UnitType =>
                UnitLiteral()

              case TupleType(ts) =>
                tupleWrap(args.zip(ts).map { case (a, t) => rec(a, t, seen) })

              case tp: TypeParameter =>
                val IntegerLiteral(n) = rec(args(0), IntegerType, seen)
                GenericValue(tp, n.toInt)

              case t =>
                unsupported(t, "Woot? structural type that is non-structural")
            }
          } else {
            tpe match {
              case ft: FunctionType if seen(t) => z3ToChooses.getOrElseUpdate(t, {
                Choose(Variable.fresh("x", ft, true).toVal, BooleanLiteral(true))
              })

              case ft @ FunctionType(fts, tt) => z3ToLambdas.getOrElseUpdate(t, {
                val n = t.toString.split("!").last.init.toInt
                uniquateClosure(n, (lambdas.getB(ft) match {
                  case None => simplestValue(ft)
                  case Some(decl) => model.getFuncInterpretations.find(_._1 == decl) match {
                    case None => simplestValue(ft)
                    case Some((_, mapping, elseValue)) =>
                      val args = fts.map(tpe => ValDef(FreshIdentifier("x", true), tpe))
                      val body = mapping.foldLeft(rec(elseValue, tt, seen + t)) { case (elze, (z3Args, z3Result)) =>
                        if (t == z3Args.head) {
                          val cond = andJoin((args zip z3Args.tail).map { case (vd, z3Arg) =>
                            Equals(vd.toVariable, rec(z3Arg, vd.tpe, seen + t))
                          })

                          IfExpr(cond, rec(z3Result, tt, seen + t), elze)
                        } else {
                          elze
                        }
                      }

                      Lambda(args, body)
                  }
                }).asInstanceOf[Lambda])
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
                val fm @ FiniteMap(entries, default, from, IntegerType) = rec(t, MapType(base, IntegerType), seen)
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

                  case OpSeqEmpty if tpe == StringType => StringLiteral("")

                  case OpSeqUnit if tpe == StringType =>
                    val CharLiteral(c) = rec(args(0), CharType, seen)
                    StringLiteral(c.toString)

                  case OpSeqConcat if tpe == StringType => StringLiteral(args.map(rec(_, CharType, seen)).map {
                    case CharLiteral(c) => c.toString
                  }.reduce(_ + _))

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
      case (v,z3ID) => (v.tpe match {
        case BooleanType =>
          model.evalAs[Boolean](z3ID).map(BooleanLiteral)

        case Int32Type =>
          model.evalAs[Int](z3ID).map(IntLiteral(_)).orElse {
            model.eval(z3ID).flatMap(t => ex.get(t, Int32Type))
          }

        case IntegerType =>
          model.evalAs[Int](z3ID).map(i => IntegerLiteral(BigInt(i)))

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
              case (v, e) => Equals(v, ex(e, v.tpe))
            }), ex(res, tfd.returnType), elze)
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
