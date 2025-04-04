/* Copyright 2009-2018 EPFL, Lausanne */

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
import _root_.smtlib.Interpreter

import scala.collection.BitSet
import scala.collection.mutable.{Map => MutableMap}

trait SMTLIBTarget extends SMTLIBParser with Interruptible with ADTManagers {
  // The only values that can be assigned to `trees` and `symbols` are `program.trees` and `program.symbols` respectively,
  // but that has to be done in a concrete class explicitly overriding `trees` and `symbols`.
  // Otherwise, we can run into initialization issue.
  val trees: program.trees.type
  val symbols: program.symbols.type

  import context.{given, _}
  import program._
  import trees._
  import symbols.{given, _}

  def targetName: String

  protected def unsupported(t: Tree, str: String): Nothing

  protected val interpreter: Interpreter

  protected val semantics: program.Semantics
  given givenSemantics: semantics.type = semantics

  /* Interruptible interface */
  private var aborted = false

  interruptManager.registerForInterrupts(this)

  def interrupt(): Unit = {
    aborted = true
    if (interpreter != null) interpreter.interrupt()
  }

  def free(): Unit = {
    interruptManager.unregisterForInterrupts(this)
    interpreter.free()
  }

  /* Send a command to the solver */
  def emit(cmd: SExpr, rawOut: Boolean = false): SExpr = {
    interpreter.eval(cmd) match {
      case err @ Error(msg) if !aborted && !rawOut =>
        throw new InternalSolverError(targetName, msg)
      case res =>
        res
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
    SSymbol(id.uniqueNameDelimited("!")
      .replace("|", "$pipe")
      .replace(":", "$colon")
      .replace("\\", "$backslash"))
  }

  protected def freshSym(id: Identifier): SSymbol = freshSym(id.name)
  protected def freshSym(name: String): SSymbol = id2sym(FreshIdentifier(name))

  /* Metadata for CC, and variables */
  protected val constructors  = new IncrementalBijection[ConsType, SSymbol]
  protected val selectors     = new IncrementalBijection[(ConsType, Int), SSymbol]
  protected val testers       = new IncrementalBijection[ConsType, SSymbol]
  protected val variables     = new IncrementalBijection[Variable, SSymbol]
  protected val sorts         = new IncrementalBijection[Type, Sort]
  protected val functions     = new IncrementalBijection[TypedFunDef, SSymbol]
  protected val lambdas       = new IncrementalBijection[FunctionType, SSymbol]
  protected val predicates    = new IncrementalBijection[Variable, SSymbol]
  protected val predicateCalls= new IncrementalBijection[Expr, SSymbol]

  def registerPredicate(v: Variable): Unit = {
    val s = id2sym(v.id)
    predicates += v -> s
  }

  /* Helper functions */

  protected def quantifiedTerm(quantifier: (SortedVar, Seq[SortedVar], Term) => Term,
                               vars: Seq[ValDef],
                               body: Expr)
                              (using bindings: Map[Identifier, Term]): Term = {
    if (vars.isEmpty) toSMT(body)(using Map())
    else {
      val sortedVars = vars map { vd =>
        SortedVar(id2sym(vd.id), declareSort(vd.getType))
      }
      quantifier(
        sortedVars.head,
        sortedVars.tail,
        toSMT(body)(using bindings ++ vars.map { vd => vd.id -> (id2sym(vd.id): Term) }.toMap))
    }
  }

  // Returns a quantified term where all free variables in the body have been quantified
  protected def quantifiedTerm(quantifier: (SortedVar, Seq[SortedVar], Term) => Term, body: Expr)
                              (using bindings: Map[Identifier, Term]): Term =
    quantifiedTerm(quantifier, exprOps.variablesOf(body).toSeq.map(_.toVal), body)

  protected final def declareSort(tpe: Type): Sort =
    // println(s"@@@@ CALLED WITH $tpe with ${tpe match
    //   case ADTType(id, _) => id.uniqueName
    //   case _ => "None"
    // } and found? ${if sorts.containsA(tpe) then "cached" else "NONONO"}")
    sorts.cachedB(tpe)(computeSort(tpe))

  protected def computeSort(t: Type): Sort = t match {
    case BooleanType() => Core.BoolSort()
    case IntegerType() => Ints.IntSort()
    case RealType()    => Reals.RealSort()
    case BVType(_,l)   => FixedSizeBitVectors.BitVectorSort(l)
    case FPType(e, s)  => FloatingPoint.FloatingPointSort(e, s)
    case RoundingMode  => FloatingPoint.RoundingModeSort()
    case CharType()    => FixedSizeBitVectors.BitVectorSort(16)
    case StringType()  => Strings.StringSort()

    case mt @ MapType(from, to) =>
      Sort(SMTIdentifier(SSymbol("Array")), Seq(declareSort(from), declareSort(to)))

    case FunctionType(from, to) =>
      Ints.IntSort()

    case tpe @ (_: ADTType | _: TupleType | _: TypeParameter | UnitType()) =>
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
    sorts.toB(t)
  }

  protected def declareVariable(v: Variable): SSymbol = {
    variables.cachedB(v) {
      val s = id2sym(v.id)
      if predicates.containsA(v) then
        () // handled by [[declarePredicate]] separately already
      else 
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
        tfd.params.map((p: ValDef) => declareSort(p.getType)),
        declareSort(tfd.getType)))
      s
    }
  }

  protected def declareLambda(tpe: FunctionType): SSymbol = {
    lambdas.cachedB(tpe) {
      val id = FreshIdentifier("dynLambda")
      val s = id2sym(id)
      emit(DeclareFun(
        s,
        (tpe +: tpe.from).map(declareSort),
        declareSort(tpe.to)
      ))
      s
    }
  }

  /* Translate a Inox Expr to an SMTLIB term */

  private def intToTerm(i: BigInt): Term = i match {
    case i if i >= 0 => Ints.NumeralLit(i)
    case i => Ints.Neg(Ints.NumeralLit(-i))
  }

  private def realToTerm(r: BigInt): Term = r match {
    case r if r >= 0 => Reals.NumeralLit(r)
    case r => Reals.Neg(Reals.NumeralLit(-r))
  }

  private def flattenPlus(e: Expr): Seq[Expr] = e match {
    case Plus(lhs, rhs) => flattenPlus(lhs) ++ flattenPlus(rhs)
    case _ => Seq(e)
  }

  private def flattenTimes(e: Expr): Seq[Expr] = e match {
    case Times(lhs, rhs) => flattenTimes(lhs) ++ flattenTimes(rhs)
    case _ => Seq(e)
  }

  protected def toSMT(e: Expr)(using bindings: Map[Identifier, Term]): Term = {
    e match {
      case v @ Variable(id, tp, flags) =>
        declareSort(v.getType)
        bindings.getOrElse(id, variables.toB(v))

      case UnitLiteral() =>
        declareSort(UnitType())
        declareVariable(Variable.fresh("Unit", UnitType()))

      case IntegerLiteral(i)     => intToTerm(i)
      case BVLiteral(_, bits, size) => FixedSizeBitVectors.BitVectorLit(List.range(1, size + 1).map(i => bits(size + 1 - i)))
      case FPLiteral(e, s, bits) =>
        val size = e + s
        FloatingPoint.FPLit(
          FixedSizeBitVectors.BitVectorLit(List.range(1, 2).map(i => bits(size + 1 - i))),
          FixedSizeBitVectors.BitVectorLit(List.range(2, e + 2).map(i => bits(size + 1 - i))),
          FixedSizeBitVectors.BitVectorLit(List.range(e + 2, size + 1).map(i => bits(size + 1 - i)))
        )

      case FractionLiteral(n, d) => Reals.Div(realToTerm(n), realToTerm(d))
      case CharLiteral(c)        => FixedSizeBitVectors.BitVectorLit(Hexadecimal.fromShort(c.toShort))
      case BooleanLiteral(v)     => Core.BoolConst(v)
      case Let(b, d, e) =>
        val id = id2sym(b.id)
        val value = toSMT(d)
        val newBody = toSMT(e)(using bindings + (b.id -> id))

        SMTLet(
          VarBinding(id, value),
          Seq(),
          newBody)

      case s @ ADTSelector(e, id) =>
        val tpe @ ADTType(_, tps) = e.getType: @unchecked
        declareSort(tpe)
        val selector = selectors.toB(ADTCons(s.constructor.id, tps) -> s.selectorIndex)
        FunctionApplication(selector, Seq(toSMT(e)))

      case i @ IsConstructor(e, id) =>
        val tpe @ ADTType(_, tps) = e.getType: @unchecked
        declareSort(tpe)
        val tester = testers.toB(ADTCons(id, tps))
        FunctionApplication(tester, Seq(toSMT(e)))

      case adt @ ADT(id, tps, es) =>
        declareSort(adt.getType)
        val constructor = constructors.toB(ADTCons(id, tps.map(_.getType)))
        if (es.isEmpty) {
          constructor
        } else {
          FunctionApplication(constructor, es.map(toSMT))
        }

      case t @ Tuple(es) =>
        val tpe @ TupleType(tps) = t.getType: @unchecked
        declareSort(tpe)
        val constructor = constructors.toB(TupleCons(tps))
        FunctionApplication(constructor, es.map(toSMT))

      case ts @ TupleSelect(t, i) =>
        val tpe @ TupleType(tps) = t.getType: @unchecked
        declareSort(tpe)
        val selector = selectors.toB((TupleCons(tps), i - 1))
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
        val constructor = constructors.toB(TypeParameterCons(tpe))
        FunctionApplication(constructor, Seq(toSMT(IntegerLiteral(n))))

      /**
       * ===== Everything else =====
       */
      case ap @ Application(caller, args) =>
        caller match
          case v: Variable if predicates.containsA(v) =>
            val pred = predicateCalls.cachedB(caller) {
              caller match
                case pred @ Variable(id, FunctionType(from, to), flags) =>
                  val s = id2sym(id)
                  emit(DeclareFun(
                    s,
                    from.map(declareSort),
                    declareSort(to)
                  ))
                  s
            }
            FunctionApplication(pred, args.map(toSMT))
          case _ => // normal lambda
            val dyn = declareLambda(caller.getType.asInstanceOf[FunctionType])
            FunctionApplication(dyn, (caller +: args).map(toSMT))

      case Not(u) => Core.Not(toSMT(u))

      case UMinus(u) => u.getType match {
        case BVType(_,_)   => FixedSizeBitVectors.Neg(toSMT(u))
        case FPType(_, _)  => FloatingPoint.Neg(toSMT(u))
        case IntegerType() => Ints.Neg(toSMT(u))
        case RealType()    => Reals.Neg(toSMT(u))
      }

      case Equals(a, b)    => Core.Equals(toSMT(a), toSMT(b))
      case Implies(a, b)   => Core.Implies(toSMT(a), toSMT(b))
      case pl @ Plus(a, b)      =>
        val rec = flattenPlus(pl).map(toSMT)
        a.getType match {
          case BVType(_,_)   => FixedSizeBitVectors.Add(rec)
          case FPType(_, _)  => FloatingPoint.Add(FloatingPoint.RNE(), toSMT(a), toSMT(b))
          case IntegerType() => Ints.Add(rec)
          case RealType()    => Reals.Add(rec)
        }
      case Minus(a, b)     => a.getType match {
        case BVType(_,_)   => FixedSizeBitVectors.Sub(toSMT(a), toSMT(b))
        case FPType(_,_)   => FloatingPoint.Sub(FloatingPoint.RNE(), toSMT(a), toSMT(b))
        case IntegerType() => Ints.Sub(toSMT(a), toSMT(b))
        case RealType()    => Reals.Sub(toSMT(a), toSMT(b))
      }
      case tms @ Times(a, b)     =>
        val rec = flattenTimes(tms).map(toSMT)
        a.getType match {
          case BVType(_,_)   => FixedSizeBitVectors.Mul(rec)
          case FPType(_,_)   => FloatingPoint.Mul(FloatingPoint.RNE(), toSMT(a), toSMT(b))
          case IntegerType() => Ints.Mul(rec)
          case RealType()    => Reals.Mul(rec)
        }

      case Division(a, b)  => a.getType match {
        case BVType(true, _) => FixedSizeBitVectors.SDiv(toSMT(a), toSMT(b))
        case BVType(false, _) => FixedSizeBitVectors.UDiv(toSMT(a), toSMT(b))
        case FPType(_,_)   => FloatingPoint.Div(FloatingPoint.RNE(), toSMT(a), toSMT(b))
        case IntegerType() =>
          val ar = toSMT(a)
          val br = toSMT(b)
          Core.ITE(
            Ints.GreaterEquals(ar, Ints.NumeralLit(0)),
            Ints.Div(ar, br),
            Ints.Neg(Ints.Div(Ints.Neg(ar), br))
          )
        case RealType() => Reals.Div(toSMT(a), toSMT(b))
      }

      case Remainder(a, b) => a.getType match {
        case BVType(true, _) => FixedSizeBitVectors.SRem(toSMT(a), toSMT(b))
        case BVType(false, _) => FixedSizeBitVectors.URem(toSMT(a), toSMT(b))
        case FPType(_, _)     => FloatingPoint.Rem(toSMT(a), toSMT(b))
        case IntegerType() =>
          val q = toSMT(Division(a, b))
          Ints.Sub(toSMT(a), Ints.Mul(toSMT(b), q))
      }

      case Modulo(a, b) => a.getType match {
        case BVType(false, _) => FixedSizeBitVectors.URem(toSMT(a), toSMT(b))
        case BVType(true, size) => // we want x mod |y|
          val ar = toSMT(a)
          val br = toSMT(b)
          FixedSizeBitVectors.SMod(
            ar,
            Core.ITE(
              FixedSizeBitVectors.SLessThan(br, toSMT(BVLiteral(true, 0, size))),
              FixedSizeBitVectors.Neg(br),
              br
            )
          )

        case IntegerType() => Ints.Mod(toSMT(a), toSMT(b))
      }

      case LessThan(a, b) => a.getType match {
        case BVType(true, _)  => FixedSizeBitVectors.SLessThan(toSMT(a), toSMT(b))
        case BVType(false, _) => FixedSizeBitVectors.ULessThan(toSMT(a), toSMT(b))
        case FPType(_,_)      => FloatingPoint.LessThan(toSMT(a), toSMT(b))
        case IntegerType()    => Ints.LessThan(toSMT(a), toSMT(b))
        case RealType()       => Reals.LessThan(toSMT(a), toSMT(b))
        case CharType()       => FixedSizeBitVectors.ULessThan(toSMT(a), toSMT(b))
      }
      case LessEquals(a, b) => a.getType match {
        case BVType(true, _)  => FixedSizeBitVectors.SLessEquals(toSMT(a), toSMT(b))
        case BVType(false, _) => FixedSizeBitVectors.ULessEquals(toSMT(a), toSMT(b))
        case FPType(_,_)      => FloatingPoint.LessEquals(toSMT(a), toSMT(b))
        case IntegerType()    => Ints.LessEquals(toSMT(a), toSMT(b))
        case RealType()       => Reals.LessEquals(toSMT(a), toSMT(b))
        case CharType()       => FixedSizeBitVectors.ULessEquals(toSMT(a), toSMT(b))
      }
      case GreaterThan(a, b) => a.getType match {
        case BVType(true, _)   => FixedSizeBitVectors.SGreaterThan(toSMT(a), toSMT(b))
        case BVType(false, _)  => FixedSizeBitVectors.UGreaterThan(toSMT(a), toSMT(b))
        case FPType(_,_)      => FloatingPoint.GreaterThan(toSMT(a), toSMT(b))
        case IntegerType()     => Ints.GreaterThan(toSMT(a), toSMT(b))
        case RealType()        => Reals.GreaterThan(toSMT(a), toSMT(b))
        case CharType()        => FixedSizeBitVectors.UGreaterThan(toSMT(a), toSMT(b))
      }
      case GreaterEquals(a, b) => a.getType match {
        case BVType(true, _)  => FixedSizeBitVectors.SGreaterEquals(toSMT(a), toSMT(b))
        case BVType(false, _) => FixedSizeBitVectors.UGreaterEquals(toSMT(a), toSMT(b))
        case FPType(_,_)      => FloatingPoint.GreaterEquals(toSMT(a), toSMT(b))
        case IntegerType()    => Ints.GreaterEquals(toSMT(a), toSMT(b))
        case RealType()       => Reals.GreaterEquals(toSMT(a), toSMT(b))
        case CharType()       => FixedSizeBitVectors.UGreaterEquals(toSMT(a), toSMT(b))
      }

      case BVNot(u)                  => FixedSizeBitVectors.Not(toSMT(u))
      case BVAnd(a, b)               => FixedSizeBitVectors.And(toSMT(a), toSMT(b))
      case BVOr(a, b)                => FixedSizeBitVectors.Or(toSMT(a), toSMT(b))
      case BVXor(a, b)               => FixedSizeBitVectors.XOr(toSMT(a), toSMT(b))
      case BVShiftLeft(a, b)         => FixedSizeBitVectors.ShiftLeft(toSMT(a), toSMT(b))
      case BVAShiftRight(a, b)       => FixedSizeBitVectors.AShiftRight(toSMT(a), toSMT(b))
      case BVLShiftRight(a, b)       => FixedSizeBitVectors.LShiftRight(toSMT(a), toSMT(b))

      case c @ BVWideningCast(e, _)  =>
        val Some((from, to)) = c.cast: @unchecked
        val BVType(signed, _) = e.getType: @unchecked
        if (signed) FixedSizeBitVectors.SignExtend(to - from, toSMT(e))
        else FixedSizeBitVectors.ZeroExtend(to - from, toSMT(e))

      case c @ BVNarrowingCast(e, _) =>
        val Some((from, to)) = c.cast: @unchecked
        FixedSizeBitVectors.Extract(to - 1, 0, toSMT(e))

      case BVUnsignedToSigned(e) => toSMT(e)
      case BVSignedToUnsigned(e) => toSMT(e)

      case FPEquals(a, b) => FloatingPoint.Eq(toSMT(a), toSMT(b))
      case FPAdd(rm, a, b) => FloatingPoint.Add(toSMT(rm), toSMT(a), toSMT(b))
      case FPSub(rm, a, b) => FloatingPoint.Sub(toSMT(rm), toSMT(a), toSMT(b))
      case FPMul(rm, a, b) => FloatingPoint.Mul(toSMT(rm), toSMT(a), toSMT(b))
      case FPDiv(rm, a, b) => FloatingPoint.Div(toSMT(rm), toSMT(a), toSMT(b))
      case FPAbs(e)        => FloatingPoint.Abs(toSMT(e))
      case Sqrt(rm, e)     => FloatingPoint.Sqrt(toSMT(rm), toSMT(e))
      case FPCast(ne, ns, rm, e) => FloatingPoint.ToFP(ne, ns, toSMT(rm), toSMT(e))
      case FPIsInfinite(e) => FloatingPoint.IsInfinite(toSMT(e))
      case FPIsZero(e)     => FloatingPoint.IsZero(toSMT(e))
      case FPIsNaN(e)      => FloatingPoint.IsNaN(toSMT(e))
      case FPIsPositive(e) => FloatingPoint.IsPositive(toSMT(e))
      case FPIsNegative(e) => FloatingPoint.IsNegative(toSMT(e))

      case RoundTowardZero => FloatingPoint.RoundTowardZero()
      case RoundTowardNegative => FloatingPoint.RoundTowardNegative()
      case RoundTowardPositive => FloatingPoint.RoundTowardPositive()
      case RoundNearestTiesToAway => FloatingPoint.RoundNearestTiesToAway()
      case RoundNearestTiesToEven => FloatingPoint.RoundNearestTiesToEven()

      case And(sub)                  => SmtLibConstructors.and(sub.map(toSMT))
      case Or(sub)                   => SmtLibConstructors.or(sub.map(toSMT))
      case IfExpr(cond, thenn, elze) => Core.ITE(toSMT(cond), toSMT(thenn), toSMT(elze))
      case fi @ FunctionInvocation(id, tps, sub) =>
        val fun = declareFunction(getFunction(id, tps.map(_.getType)))
        if (sub.isEmpty) fun
        else FunctionApplication(fun, sub.map(toSMT))
      case Forall(vs, bd) =>
        quantifiedTerm(SMTForall.apply, vs, bd)(using Map())

      /** String operations */
      // FIXME: replace by Seq(BV(16)) once solvers can handle them
      case StringLiteral(v) =>
        declareSort(StringType())
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
    val smtVars: Map[SSymbol, Term],
    val functions: Map[SSymbol, DefineFun],
    val seen: Set[(BigInt, Type)] = Set.empty,
    private[SMTLIBTarget] val chooses: MutableMap[(BigInt, Type), Choose] = MutableMap.empty,
    private[SMTLIBTarget] val lambdas: MutableMap[(BigInt, Type), Lambda] = MutableMap.empty
  ) extends super.AbstractContext {
    def withSeen(n: (BigInt, Type)): Context = new Context(vars, smtVars, functions, seen + n, chooses, lambdas)
    def withVariable(sym: SSymbol, expr: Expr): Context = new Context(vars + (sym -> expr), smtVars, functions, seen, chooses, lambdas)
    def withSMTVariable(sym: SSymbol, term: Term): Context = new Context(vars, smtVars + (sym -> term), functions, seen, chooses, lambdas)
    def withSMTVariables(bindings: Seq[(SSymbol, Term)]): Context = bindings.foldLeft(this)((ctx, p) => ctx.withSMTVariable(p._1, p._2))

    def getFunction(sym: SSymbol, ft: FunctionType): Option[Lambda] = functions.get(sym).map {
      case df @ DefineFun(SMTFunDef(a, args, _, body)) =>
        val vds = (args zip ft.from).map(p => ValDef.fresh(p._1.name.name, p._2))
        val exBody = fromSMT(body, ft.to)(using withVariables(args.map(_.name) zip vds.map(_.toVariable)))
        Lambda(vds, exBody)
    }

    // If a stack overflow occurred during extraction, then we may end up in situations where
    // chooses don't have a corresponding lambda. In such cases, we discard the choose as it is
    // irrelevant to the final model (since it won't contain that lambda).
    def getChooses = chooses.toMap.flatMap { case (n, c) => lambdas.get(n).map(c -> _) }
  }

  override protected def fromSMT(sort: Sort)(using Context): Type = sorts.getA(sort) match {
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
  override protected def fromSMT(t: Term, otpe: Option[Type] = None)(using context: Context): Expr = {

    // Use as much information as there is, if there is an expected type, great, but it might not always be there
    (t, otpe) match {
      case (_, Some(UnitType())) =>
        UnitLiteral()

      case (FixedSizeBitVectors.BitVectorConstant(n, b), Some(CharType())) if b == BigInt(16) =>
        CharLiteral(n.toInt.toChar)

      case (SHexadecimal(h), Some(CharType())) =>
        CharLiteral(h.toInt.toChar)

      case (Num(i), Some(IntegerType())) =>
        IntegerLiteral(i)

      case (Num(i), Some(RealType())) =>
        exprOps.normalizeFraction(FractionLiteral(i, 1))

      case (Reals.Div(SNumeral(n1), SNumeral(n2)), Some(RealType())) =>
        exprOps.normalizeFraction(FractionLiteral(n1, n2))

      case (Ints.Neg(Reals.Div(SNumeral(n1), SNumeral(n2))), Some(RealType())) =>
        exprOps.normalizeFraction(FractionLiteral(-n1, n2))

      case (Ints.Neg(SDecimal(value)), Some(RealType())) =>
        exprOps.normalizeFraction(FractionLiteral(
          value.bigDecimal.movePointRight(value.scale).toBigInteger.negate,
          BigInt(10).pow(value.scale)))

      case (SString(v), _) =>
        StringLiteral(utils.StringUtils.decode(v))

      case (Num(n), Some(ft: FunctionType)) if context.seen(n -> ft) =>
        context.chooses.getOrElse(n -> ft, {
          val res = Choose(Variable.fresh("x", ft, true).toVal, BooleanLiteral(true))
          context.chooses(n -> ft) = res
          res
        })

      case (Num(n), Some(ft: FunctionType)) => context.lambdas.getOrElse(n -> ft, {
        val count = if (n < 0) -2 * n.toInt else 2 * n.toInt + 1
        val res = uniquateClosure(count, lambdas.getB(ft)
          .flatMap { dynLambda =>
            context.withSeen(n -> ft).getFunction(dynLambda, FunctionType(IntegerType() +: ft.from, ft.to))
          }.map {
            case Lambda(dispatcher +: args, body) =>
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
              Lambda(args, simpBody)
            case l@Lambda(_, _) =>
              unsupported(l, "woot? lambda without dispatcher")
          }.getOrElse(try {
            simplestValue(ft, allowSolver = false).asInstanceOf[Lambda]
          } catch {
            case _: NoSimpleValue =>
              val args = ft.from.map(tpe => ValDef.fresh("x", tpe, true))
              Lambda(args, Choose(ValDef.fresh("res", ft), BooleanLiteral(true)))
          }))

        context.lambdas(n -> ft) = res
        res
      })

      case (SimpleSymbol(s), _) if constructors.containsB(s) =>
        constructors.toA(s) match {
          case ADTCons(id, tps) =>
            ADT(id, tps, Nil)
          case t =>
            unsupported(t, "woot? for a single constructor for non-case-object")
        }

      case (FunctionApplication(SimpleSymbol(s), Seq(e)), _) if testers.containsB(s) =>
        testers.toA(s) match {
          case ac @ ADTCons(id, _) =>
            IsConstructor(fromSMT(e, ac.getType), id)
          case t =>
            unsupported(t, "woot? tester for non-adt type")
        }

      case (FunctionApplication(SimpleSymbol(s), Seq(e)), _) if selectors.containsB(s) =>
        selectors.toA(s) match {
          case (ac @ ADTCons(id, _), i) =>
            ADTSelector(fromSMT(e, ac.getType), getConstructor(id).fields(i).id)
          case (tc @ TupleCons(_), i) =>
            TupleSelect(fromSMT(e, tc.getType), i + 1)
          case (t, _) =>
            unsupported(t, "woot? selector for non-structural type")
        }

      case (FunctionApplication(SimpleSymbol(s), args), _) if constructors.containsB(s) =>
        constructors.toA(s) match {
          case ADTCons(id, tps) =>
            ADT(id, tps, (args zip getConstructor(id, tps).fields.map(_.getType)) map fromSMT)

          case TupleCons(tps) =>
            tupleWrap((args zip tps) map fromSMT)

          case TypeParameterCons(tp) =>
            val IntegerLiteral(n) = fromSMT(args(0), IntegerType()): @unchecked
            GenericValue(tp, n.toInt)

          case t =>
            unsupported(t, "Woot? structural type that is non-structural")
        }

      // @nv and @jad: hack to extract values with let-bindings from Z3 models
      case (QualifiedIdentifier(SimpleIdentifier(sym), None), _) if context.smtVars contains sym =>
        fromSMT(context.smtVars(sym), otpe)

      case (SMTLet(binding, bindings, term), _) =>
        fromSMT(term, otpe)(using context.withSMTVariables((binding +: bindings).map {
          case VarBinding(name, term) => name -> term
        }))

      // @nv: useful hack for dynLambda extraction
      case (Core.Equals(QualifiedIdentifier(SimpleIdentifier(sym), None), e), _)
      if (context.vars contains sym) && context.vars(sym).isTyped =>
        val v = context.vars(sym)
        Equals(v, fromSMT(e, v.getType))

      case (Core.Equals(e, QualifiedIdentifier(SimpleIdentifier(sym), None)), _)
      if (context.vars contains sym) && context.vars(sym).isTyped =>
        val v = context.vars(sym)
        Equals(fromSMT(e, v.getType), v)

      case _ => super.fromSMT(t, otpe)
    }
  }
}

abstract class ConcreteSMTLIBTarget(override val program: Program,
                                    override val context: inox.Context)
                                   (override val trees: program.trees.type,
                                    override val symbols: program.symbols.type,
                                    override val semantics: program.Semantics)
  extends SMTLIBTarget {
  def this(program: Program, context: inox.Context)(using semantics: program.Semantics) =
    this(program, context)(program.trees, program.symbols, semantics)
}