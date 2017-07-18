/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package smtlib

import utils._

import _root_.smtlib.common._
import _root_.smtlib.printer.{ RecursivePrinter => SMTPrinter }
import _root_.smtlib.trees.Commands.{
  Constructor => SMTConstructor,
  FunDef => SMTFunDef,
  _
}
import _root_.smtlib.trees.Terms.{
  Forall => SMTForall,
  Identifier => SMTIdentifier,
  Let => SMTLet,
  _
}
import _root_.smtlib.trees.CommandsResponses._
import _root_.smtlib.theories.{Constructors => SmtLibConstructors, _}
import _root_.smtlib.theories.experimental._
import _root_.smtlib.Interpreter

import scala.collection.BitSet
import scala.collection.mutable.{Map => MutableMap}

trait SMTLIBTarget extends SMTLIBParser with Interruptible with ADTManagers {
  val program: Program
  lazy val trees: program.trees.type = program.trees
  lazy val symbols: program.symbols.type = program.symbols
  import program._
  import trees._
  import symbols._

  def targetName: String

  protected def unsupported(t: Tree, str: String): Nothing

  protected val interpreter: Interpreter

  protected implicit val semantics: program.Semantics

  /* Interruptible interface */
  private var aborted = false

  ctx.interruptManager.registerForInterrupts(this)

  def interrupt(): Unit = {
    aborted = true
    if (interpreter != null) interpreter.interrupt()
  }

  def free(): Unit = {
    ctx.interruptManager.unregisterForInterrupts(this)
    interpreter.free()
  }

  /* Send a command to the solver */
  def emit(cmd: SExpr, rawOut: Boolean = false): SExpr = {
    interpreter.eval(cmd) match {
      case err @ Error(msg) if !aborted && !rawOut =>
        ctx.reporter.fatalError(s"Unexpected error from $targetName solver: $msg")
      case res =>
        res
    }
  }

  def parseSuccess() = {
    val res = interpreter.parser.parseGenResponse
    if (res != Success) {
      ctx.reporter.warning("Unnexpected result from " + targetName + ": " + res + " expected success")
    }
  }

  /*
   * Translation from Inox Expressions to SMTLIB terms and reverse
   */

  /* Symbol handling */
  protected object SimpleSymbol {
    def apply(sym: SSymbol) = QualifiedIdentifier(SMTIdentifier(sym))
    def unapply(term: Term): Option[SSymbol] = term match {
      case QualifiedIdentifier(SMTIdentifier(sym, Seq()), None) => Some(sym)
      case _ => None
    }
  }

  import scala.language.implicitConversions
  protected implicit def symbolToQualifiedId(s: SSymbol): QualifiedIdentifier = SimpleSymbol(s)

  protected val adtManager = new ADTManager

  protected def id2sym(id: Identifier): SSymbol = {
    SSymbol(id.uniqueNameDelimited("!").replace("|", "$pipe").replace("\\", "$backslash"))
  }

  protected def freshSym(id: Identifier): SSymbol = freshSym(id.name)
  protected def freshSym(name: String): SSymbol = id2sym(FreshIdentifier(name))

  /* Metadata for CC, and variables */
  protected val constructors  = new IncrementalBijection[Type, SSymbol]
  protected val selectors     = new IncrementalBijection[(Type, Int), SSymbol]
  protected val testers       = new IncrementalBijection[Type, SSymbol]
  protected val variables     = new IncrementalBijection[Variable, SSymbol]
  protected val sorts         = new IncrementalBijection[Type, Sort]
  protected val functions     = new IncrementalBijection[TypedFunDef, SSymbol]
  protected val lambdas       = new IncrementalBijection[FunctionType, SSymbol]

  /* Helper functions */

  protected def quantifiedTerm(quantifier: (SortedVar, Seq[SortedVar], Term) => Term,
                               vars: Seq[ValDef],
                               body: Expr)
                              (implicit bindings: Map[Identifier, Term]): Term = {
    if (vars.isEmpty) toSMT(body)(Map())
    else {
      val sortedVars = vars map { vd =>
        SortedVar(id2sym(vd.id), declareSort(vd.getType))
      }
      quantifier(
        sortedVars.head,
        sortedVars.tail,
        toSMT(body)(bindings ++ vars.map { vd => vd.id -> (id2sym(vd.id): Term) }.toMap))
    }
  }

  // Returns a quantified term where all free variables in the body have been quantified
  protected def quantifiedTerm(quantifier: (SortedVar, Seq[SortedVar], Term) => Term, body: Expr)
                              (implicit bindings: Map[Identifier, Term]): Term = {
    quantifiedTerm(quantifier, exprOps.variablesOf(body).toSeq.map(_.toVal), body)
  }

  protected final def declareSort(t: Type): Sort = {
    val tpe = bestRealType(t)
    sorts.cachedB(tpe)(computeSort(tpe))
  }

  protected def computeSort(t: Type): Sort = t match {
    case BooleanType => Core.BoolSort()
    case IntegerType => Ints.IntSort()
    case RealType    => Reals.RealSort()
    case BVType(l)   => FixedSizeBitVectors.BitVectorSort(l)
    case CharType    => FixedSizeBitVectors.BitVectorSort(16)
    case StringType  => Strings.StringSort()

    case mt @ MapType(from, to) =>
      Sort(SMTIdentifier(SSymbol("Array")), Seq(declareSort(from), declareSort(to)))

    case FunctionType(from, to) =>
      Ints.IntSort()

    case tpe @ (_: ADTType | _: TupleType | _: TypeParameter | UnitType) =>
      declareStructuralSort(tpe)

    case other =>
      unsupported(other, s"Could not transform $other into an SMT sort")
  }

  protected def declareDatatypes(datatypes: Seq[(Type, DataType)]): Unit = {
    // We pre-declare ADTs
    for ((tpe, DataType(sym, _)) <- datatypes) {
      sorts += tpe -> Sort(SMTIdentifier(id2sym(sym)))
    }

    def toDecl(c: Constructor): SMTConstructor = {
      val s = id2sym(c.sym)

      testers += c.tpe -> SSymbol("is-" + s.name)
      constructors += c.tpe -> s

      SMTConstructor(s, c.fields.zipWithIndex.map {
        case ((cs, t), i) =>
          selectors += (c.tpe, i) -> id2sym(cs)
          (id2sym(cs), declareSort(t))
      })
    }

    val adts = for ((tpe, DataType(sym, cases)) <- datatypes.toList) yield {
      (id2sym(sym), cases.map(toDecl))
    }

    if (adts.nonEmpty) {
      val cmd = DeclareDatatypes(adts)
      emit(cmd)
    }
  }

  protected def declareStructuralSort(t: Type): Sort = {
    adtManager.declareADTs(t, declareDatatypes)
    sorts.toB(bestRealType(t))
  }

  protected def declareVariable(v: Variable): SSymbol = {
    variables.cachedB(v) {
      val s = id2sym(v.id)
      val cmd = DeclareFun(s, List(), declareSort(v.getType))
      emit(cmd)
      s
    }
  }

  protected def declareFunction(tfd: TypedFunDef): SSymbol = {
    functions.cachedB(tfd) {
      val id = if (tfd.tps.isEmpty) {
        tfd.id
      } else {
        FreshIdentifier(tfd.id.name)
      }
      val s = id2sym(id)
      emit(DeclareFun(
        s,
        tfd.params.map((p: ValDef) => declareSort(p.tpe)),
        declareSort(tfd.returnType)))
      s
    }
  }

  protected def declareLambda(tpe: FunctionType): SSymbol = {
    val realTpe = bestRealType(tpe).asInstanceOf[FunctionType]
    lambdas.cachedB(realTpe) {
      val id = FreshIdentifier("dynLambda")
      val s = id2sym(id)
      emit(DeclareFun(
        s,
        (realTpe +: realTpe.from).map(declareSort),
        declareSort(realTpe.to)
      ))
      s
    }
  }

  /* Translate a Inox Expr to an SMTLIB term */

  def sortToSMT(s: Sort): SExpr = {
    s match {
      case Sort(id, Nil) =>
        id.symbol

      case Sort(id, subs) =>
        SList((id.symbol +: subs.map(sortToSMT)).toList)
    }
  }

  protected def toSMT(t: Type): SExpr = {
    sortToSMT(declareSort(t))
  }

  protected def toSMT(e: Expr)(implicit bindings: Map[Identifier, Term]): Term = {
    e match {
      case v @ Variable(id, tp, flags) =>
        declareSort(tp)
        bindings.getOrElse(id, variables.toB(v))

      case UnitLiteral() =>
        declareSort(UnitType)
        declareVariable(Variable.fresh("Unit", UnitType))

      case IntegerLiteral(i)     => if (i >= 0) Ints.NumeralLit(i) else Ints.Neg(Ints.NumeralLit(-i))
      case BVLiteral(bits, size) => FixedSizeBitVectors.BitVectorLit(List.range(1, size + 1).map(i => bits(size + 1 - i)))
      case FractionLiteral(n, d) => Reals.Div(Reals.NumeralLit(n), Reals.NumeralLit(d))
      case CharLiteral(c)        => FixedSizeBitVectors.BitVectorLit(Hexadecimal.fromShort(c.toShort))
      case BooleanLiteral(v)     => Core.BoolConst(v)
      case Let(b, d, e) =>
        val id = id2sym(b.id)
        val value = toSMT(d)
        val newBody = toSMT(e)(bindings + (b.id -> id))

        SMTLet(
          VarBinding(id, value),
          Seq(),
          newBody)

      case s @ ADTSelector(e, id) =>
        val ADTType(id, tps) = e.getType
        val adt = ADTType(id, tps map bestRealType)
        declareSort(adt)
        val selector = selectors.toB(adt -> s.selectorIndex)
        FunctionApplication(selector, Seq(toSMT(e)))

      case AsInstanceOf(expr, adt) =>
        toSMT(expr)

      case io @ IsInstanceOf(e, ADTType(id, tps)) =>
        val adt = ADTType(id, tps map bestRealType)
        declareSort(adt)
        adt.getADT match {
          case tcons: TypedADTConstructor =>
            val tester = testers.toB(tcons.toType)
            FunctionApplication(tester, Seq(toSMT(e)))
          case _ =>
            toSMT(BooleanLiteral(true))
        }

      case ADT(ADTType(id, tps), es) =>
        val adt = ADTType(id, tps map bestRealType)
        declareSort(adt)
        val constructor = constructors.toB(adt)
        if (es.isEmpty) {
          constructor
        } else {
          FunctionApplication(constructor, es.map(toSMT))
        }

      case t @ Tuple(es) =>
        val tpe = bestRealType(t.getType)
        declareSort(tpe)
        val constructor = constructors.toB(tpe)
        FunctionApplication(constructor, es.map(toSMT))

      case ts @ TupleSelect(t, i) =>
        val tpe = bestRealType(t.getType)
        declareSort(tpe)
        val selector = selectors.toB((tpe, i - 1))
        FunctionApplication(selector, Seq(toSMT(t)))

      case al @ MapApply(a, i) =>
        ArraysEx.Select(toSMT(a), toSMT(i))

      case al @ MapUpdated(map, k, v) =>
        ArraysEx.Store(toSMT(map), toSMT(k), toSMT(v))

      case ra @ FiniteMap(elems, default, _, _) =>
        val s = declareSort(ra.getType)

        var res: Term = FunctionApplication(
          QualifiedIdentifier(SMTIdentifier(SSymbol("const")), Some(s)),
          List(toSMT(default)))
        for ((k, v) <- elems) {
          res = ArraysEx.Store(res, toSMT(k), toSMT(v))
        }

        res

      case gv @ GenericValue(tpe, n) =>
        declareSort(tpe)
        val constructor = constructors.toB(tpe)
        FunctionApplication(constructor, Seq(toSMT(IntegerLiteral(n))))

      /**
       * ===== Everything else =====
       */
      case ap @ Application(caller, args) =>
        val dyn = declareLambda(caller.getType.asInstanceOf[FunctionType])
        FunctionApplication(dyn, (caller +: args).map(toSMT))

      case Not(u) => Core.Not(toSMT(u))

      case UMinus(u) => u.getType match {
        case IntegerType => Ints.Neg(toSMT(u))
        case BVType(_)   => FixedSizeBitVectors.Neg(toSMT(u))
        case RealType    => Reals.Neg(toSMT(u))
      }

      case Equals(a, b)    => Core.Equals(toSMT(a), toSMT(b))
      case Implies(a, b)   => Core.Implies(toSMT(a), toSMT(b))
      case Plus(a, b)      => a.getType match {
        case BVType(_)   => FixedSizeBitVectors.Add(toSMT(a), toSMT(b))
        case IntegerType => Ints.Add(toSMT(a), toSMT(b))
        case RealType    => Reals.Add(toSMT(a), toSMT(b))
      }
      case Minus(a, b)     => a.getType match {
        case BVType(_)   => FixedSizeBitVectors.Sub(toSMT(a), toSMT(b))
        case IntegerType => Ints.Sub(toSMT(a), toSMT(b))
        case RealType    => Reals.Sub(toSMT(a), toSMT(b))
      }
      case Times(a, b)     => a.getType match {
        case BVType(_)   => FixedSizeBitVectors.Mul(toSMT(a), toSMT(b))
        case IntegerType => Ints.Mul(toSMT(a), toSMT(b))
        case RealType    => Reals.Mul(toSMT(a), toSMT(b))
      }

      case Division(a, b)  => a.getType match {
        case BVType(_) => FixedSizeBitVectors.SDiv(toSMT(a), toSMT(b))
        case IntegerType =>
          val ar = toSMT(a)
          val br = toSMT(b)
          Core.ITE(
            Ints.GreaterEquals(ar, Ints.NumeralLit(0)),
            Ints.Div(ar, br),
            Ints.Neg(Ints.Div(Ints.Neg(ar), br))
          )
        case RealType => Reals.Div(toSMT(a), toSMT(b))
      }

      case Remainder(a, b) => a.getType match {
        case BVType(_) => FixedSizeBitVectors.SRem(toSMT(a), toSMT(b))
        case IntegerType =>
          val q = toSMT(Division(a, b))
          Ints.Sub(toSMT(a), Ints.Mul(toSMT(b), q))
      }

      case Modulo(a, b) => a.getType match {
        case BVType(size) => // we want x mod |y|
          val ar = toSMT(a)
          val br = toSMT(b)
          FixedSizeBitVectors.SMod(
            ar,
            Core.ITE(
              FixedSizeBitVectors.SLessThan(br, toSMT(BVLiteral(0, size))),
              FixedSizeBitVectors.Neg(br),
              br
            )
          )

        case IntegerType => Ints.Mod(toSMT(a), toSMT(b))
      }

      case LessThan(a, b) => a.getType match {
        case BVType(_)   => FixedSizeBitVectors.SLessThan(toSMT(a), toSMT(b))
        case IntegerType => Ints.LessThan(toSMT(a), toSMT(b))
        case RealType    => Reals.LessThan(toSMT(a), toSMT(b))
        case CharType    => FixedSizeBitVectors.ULessThan(toSMT(a), toSMT(b))
      }
      case LessEquals(a, b) => a.getType match {
        case BVType(_)   => FixedSizeBitVectors.SLessEquals(toSMT(a), toSMT(b))
        case IntegerType => Ints.LessEquals(toSMT(a), toSMT(b))
        case RealType    => Reals.LessEquals(toSMT(a), toSMT(b))
        case CharType    => FixedSizeBitVectors.ULessEquals(toSMT(a), toSMT(b))
      }
      case GreaterThan(a, b) => a.getType match {
        case BVType(_)   => FixedSizeBitVectors.SGreaterThan(toSMT(a), toSMT(b))
        case IntegerType => Ints.GreaterThan(toSMT(a), toSMT(b))
        case RealType    => Reals.GreaterThan(toSMT(a), toSMT(b))
        case CharType    => FixedSizeBitVectors.UGreaterThan(toSMT(a), toSMT(b))
      }
      case GreaterEquals(a, b) => a.getType match {
        case BVType(_)   => FixedSizeBitVectors.SGreaterEquals(toSMT(a), toSMT(b))
        case IntegerType => Ints.GreaterEquals(toSMT(a), toSMT(b))
        case RealType    => Reals.GreaterEquals(toSMT(a), toSMT(b))
        case CharType    => FixedSizeBitVectors.UGreaterEquals(toSMT(a), toSMT(b))
      }

      case BVNot(u)                  => FixedSizeBitVectors.Not(toSMT(u))
      case BVAnd(a, b)               => FixedSizeBitVectors.And(toSMT(a), toSMT(b))
      case BVOr(a, b)                => FixedSizeBitVectors.Or(toSMT(a), toSMT(b))
      case BVXor(a, b)               => FixedSizeBitVectors.XOr(toSMT(a), toSMT(b))
      case BVShiftLeft(a, b)         => FixedSizeBitVectors.ShiftLeft(toSMT(a), toSMT(b))
      case BVAShiftRight(a, b)       => FixedSizeBitVectors.AShiftRight(toSMT(a), toSMT(b))
      case BVLShiftRight(a, b)       => FixedSizeBitVectors.LShiftRight(toSMT(a), toSMT(b))

      case c @ BVWideningCast(e, _)  =>
        val Some((from, to)) = c.cast
        FixedSizeBitVectors.SignExtend(to - from, toSMT(e))

      case c @ BVNarrowingCast(e, _) =>
        val Some((from, to)) = c.cast
        FixedSizeBitVectors.Extract(to - 1, 0, toSMT(e))

      case And(sub)                  => SmtLibConstructors.and(sub.map(toSMT))
      case Or(sub)                   => SmtLibConstructors.or(sub.map(toSMT))
      case IfExpr(cond, thenn, elze) => Core.ITE(toSMT(cond), toSMT(thenn), toSMT(elze))
      case fi @ FunctionInvocation(_, _, sub) =>
        val fun = declareFunction(fi.tfd)
        if (sub.isEmpty) fun
        else FunctionApplication(fun, sub.map(toSMT))
      case Forall(vs, bd) =>
        quantifiedTerm(SMTForall, vs, bd)(Map())

      /** String operations */
      // FIXME: replace by Seq(BV(16)) once solvers can handle them
      case StringLiteral(v) =>
        declareSort(StringType)
        Strings.StringLit(v)

      case StringLength(a) => Strings.Length(toSMT(a))
      case StringConcat(a, b) => Strings.Concat(toSMT(a), toSMT(b))
      case SubString(a, start, Plus(start2, length)) if start == start2 =>
        Strings.Substring(toSMT(a), toSMT(start), toSMT(length))
      case SubString(a, start, end) =>
        Strings.Substring(toSMT(a), toSMT(start), toSMT(Minus(end, start)))

      case o =>
        unsupported(o, "")
    }
  }

  protected class Context(
    val vars: Map[SSymbol, Expr],
    val functions: Map[SSymbol, DefineFun],
    val seen: Set[(BigInt, Type)] = Set.empty,
    private[SMTLIBTarget] val chooses: MutableMap[(BigInt, Type), Choose] = MutableMap.empty,
    private[SMTLIBTarget] val lambdas: MutableMap[(BigInt, Type), Lambda] = MutableMap.empty
  ) extends super.AbstractContext {
    def withSeen(n: (BigInt, Type)): Context = new Context(vars, functions, seen + n, chooses, lambdas)
    def withVariable(sym: SSymbol, expr: Expr): Context = new Context(vars + (sym -> expr), functions, seen, chooses, lambdas)

    def getFunction(sym: SSymbol, ft: FunctionType): Option[Lambda] = functions.get(sym).map {
      case df @ DefineFun(SMTFunDef(a, args, _, body)) =>
        val vds = (args zip ft.from).map(p => ValDef(FreshIdentifier(p._1.name.name), p._2))
        val exBody = fromSMT(body, ft.to)(withVariables(args.map(_.name) zip vds.map(_.toVariable)))
        Lambda(vds, exBody)
    }

    def getChooses = chooses.toMap.map { case (n, c) => c -> lambdas(n) }
  }

  override protected def fromSMT(sort: Sort)(implicit context: Context): Type = sorts.getA(sort) match {
    case Some(tpe) => tpe
    case None => super.fromSMT(sort)
  }

  protected object Num {
    def unapply(t: Term): Option[BigInt] = t match {
      case SNumeral(n) => Some(n)
      case FunctionApplication(f, Seq(SNumeral(n))) if f.toString == "-" => Some(-n)
      case _ => None
    }
  }

  /* Translate an SMTLIB term back to a Inox Expr */
  override protected def fromSMT(t: Term, otpe: Option[Type] = None)(implicit context: Context): Expr = {

    // Use as much information as there is, if there is an expected type, great, but it might not always be there
    (t, otpe) match {
      case (_, Some(UnitType)) =>
        UnitLiteral()

      case (FixedSizeBitVectors.BitVectorConstant(n, b), Some(CharType)) if b == BigInt(16) =>
        CharLiteral(n.toInt.toChar)

      case (SHexadecimal(h), Some(CharType)) =>
        CharLiteral(h.toInt.toChar)


      case (Num(i), Some(IntegerType)) =>
        IntegerLiteral(i)

      case (Num(i), Some(RealType)) =>
        exprOps.normalizeFraction(FractionLiteral(i, 1))

      case (Reals.Div(SNumeral(n1), SNumeral(n2)), Some(RealType)) =>
        exprOps.normalizeFraction(FractionLiteral(n1, n2))

      case (Ints.Neg(Reals.Div(SNumeral(n1), SNumeral(n2))), Some(RealType)) =>
        exprOps.normalizeFraction(FractionLiteral(-n1, n2))

      case (Ints.Neg(SDecimal(value)), Some(RealType)) =>
        exprOps.normalizeFraction(FractionLiteral(
          value.bigDecimal.movePointRight(value.scale).toBigInteger.negate,
          BigInt(10).pow(value.scale)))

      case (SString(v), _) => StringLiteral(v)

      case (Num(n), Some(ft: FunctionType)) if context.seen(n -> ft) =>
        context.chooses.getOrElseUpdate(n -> ft, {
          Choose(Variable.fresh("x", ft, true).toVal, BooleanLiteral(true))
        })

      case (Num(n), Some(ft: FunctionType)) => context.lambdas.getOrElseUpdate(n -> ft, {
        val count = if (n < 0) -2 * n.toInt else 2 * n.toInt + 1
        val FirstOrderFunctionType(from, to) = ft
        uniquateClosure(count, lambdas.getB(ft)
          .flatMap { dynLambda =>
            context.withSeen(n -> ft).getFunction(dynLambda, FunctionType(IntegerType +: from, to))
          }.map { case Lambda(dispatcher +: args, body) =>
            val dv = dispatcher.toVariable

            val dispatchedBody = exprOps.postMap {
              case Equals(`dv`, IntegerLiteral(i)) => Some(BooleanLiteral(n == i))
              case Equals(IntegerLiteral(i), `dv`) => Some(BooleanLiteral(n == i))
              case Equals(`dv`, UMinus(IntegerLiteral(i))) => Some(BooleanLiteral(n == -i))
              case Equals(UMinus(IntegerLiteral(i)), `dv`) => Some(BooleanLiteral(n == -i))
              case _ => None
            } (body)

            val simpBody = simplifyByConstructors(dispatchedBody)
            assert(!(exprOps.variablesOf(simpBody) contains dispatcher.toVariable), "Dispatcher still in lambda body")
            mkLambda(args, simpBody, ft)
          }.getOrElse(try {
            simplestValue(ft, allowSolver = false).asInstanceOf[Lambda]
          } catch {
            case _: NoSimpleValue =>
              val args = from.map(tpe => ValDef(FreshIdentifier("x", true), tpe))
              mkLambda(args, Choose(ValDef(FreshIdentifier("res"), ft), BooleanLiteral(true)), ft)
          }))
      })

      case (SimpleSymbol(s), _) if constructors.containsB(s) =>
        constructors.toA(s) match {
          case adt: ADTType =>
            ADT(adt, Nil)
          case t =>
            unsupported(t, "woot? for a single constructor for non-case-object")
        }

      case (FunctionApplication(SimpleSymbol(s), List(e)), _) if testers.containsB(s) =>
        testers.toA(s) match {
          case adt: ADTType =>
            IsInstanceOf(fromSMT(e, adt), adt)
          case t =>
            unsupported(t, "woot? tester for non-adt type")
        }

      case (FunctionApplication(SimpleSymbol(s), List(e)), _) if selectors.containsB(s) =>
        selectors.toA(s) match {
          case (adt: ADTType, i) =>
            ADTSelector(fromSMT(e, adt), adt.getADT.toConstructor.fields(i).id)
          case (tt: TupleType, i) =>
            TupleSelect(fromSMT(e, tt), i + 1)
          case (t, _) =>
            unsupported(t, "woot? selector for non-structural type")
        }

      case (FunctionApplication(SimpleSymbol(s), args), _) if constructors.containsB(s) =>
        constructors.toA(s) match {
          case adt: ADTType =>
            val rargs = args.zip(adt.getADT.toConstructor.fields.map(_.getType)).map(fromSMT)
            ADT(adt, rargs)

          case tt: TupleType =>
            val rargs = args.zip(tt.bases).map(fromSMT)
            tupleWrap(rargs)

          case tp: TypeParameter =>
            val IntegerLiteral(n) = fromSMT(args(0), IntegerType)
            GenericValue(tp, n.toInt)

          case t =>
            unsupported(t, "Woot? structural type that is non-structural")
        }

      // @nv: useful hack for dynLambda extraction
      case (Core.Equals(QualifiedIdentifier(SimpleIdentifier(sym), None), e), _)
      if (context.vars contains sym) && context.vars(sym).isTyped =>
        val v = context.vars(sym)
        Equals(v, fromSMT(e, bestRealType(v.getType)))

      case (Core.Equals(e, QualifiedIdentifier(SimpleIdentifier(sym), None)), _)
      if (context.vars contains sym) && context.vars(sym).isTyped =>
        val v = context.vars(sym)
        Equals(fromSMT(e, bestRealType(v.getType)), v)

      case _ => super.fromSMT(t, otpe)
    }
  }
}
