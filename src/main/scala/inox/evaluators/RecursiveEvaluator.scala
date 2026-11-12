/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package evaluators

import inox.ast.Trees
import inox.transformers.TreeTransformer

import inox.utils.CaseSplit.*

import scala.collection.immutable.BitSet

abstract class RecursiveEvaluator(override val program: Program,
                                  override val context: Context)
                                 (using override protected val semantics: program.Semantics)
  extends ContextualEvaluator
     with DeterministicEvaluator
     with SolvingEvaluator {

  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}
  import program.trees.exprOps._

  val name = "Recursive Evaluator"

  private def shift(b: BitSet, size: Int, i: Int): BitSet =
    b.filter(bit => bit + i >= 1 && bit + i <= size).map(_ + i)

  /** The number of positions a bitvector of `size` bits is shifted by `amount`.
    *
    * As in SMT-LIB, the amount is read as an unsigned value, whatever the signedness of its type, and
    * shifting by `size` or more vacates all the bits: the result is capped at `size`.
    */
  private def shiftAmount(amount: BVLiteral, size: Int): Int = {
    val unsigned = BVLiteral(false, amount.value, amount.size).toBigInt
    if (unsigned >= size) size else unsigned.toInt
  }

  protected def finiteSet(els: Iterable[Expr], tpe: Type): FiniteSet = {
    FiniteSet(els.toSeq.distinct.sortBy(_.toString), tpe)
  }

  protected def finiteBag(els: Iterable[(Expr, Expr)], tpe: Type): FiniteBag = {
    FiniteBag(els.toMap.toSeq.filter { case (_, IntegerLiteral(i)) => i > 0 case _ => false }.sortBy(_._1.toString), tpe)
  }

  // `max` and `min` follow SMT-LIB's fp.max and fp.min: a NaN operand is ignored unless both are
  // NaN. SMT-LIB leaves the result open for +0.0 and -0.0, which we order as the JVM does.
  private val roundingModes: Set[Expr] =
    Set(RoundNearestTiesToEven, RoundNearestTiesToAway, RoundTowardPositive, RoundTowardNegative, RoundTowardZero)

  /** Rounds `d` to an integral value with the rounding mode `rm`, keeping the sign of zeros. */
  private def roundToIntegral(d: Double, rm: Expr): Double = rm match {
    case RoundNearestTiesToEven => Math.rint(d)
    case RoundTowardPositive => Math.ceil(d)
    case RoundTowardNegative => Math.floor(d)
    case RoundTowardZero => if (d < 0) Math.ceil(d) else Math.floor(d)
    case RoundNearestTiesToAway =>
      if (d.isNaN || d.isInfinite) d
      else {
        val abs = Math.abs(d)
        val floor = Math.floor(abs)
        Math.copySign(if (abs - floor >= 0.5) floor + 1 else floor, d)
      }
    case _ => throw EvalError(s"Unexpected rounding mode $rm")
  }

  private def fpMax(a: Double, b: Double): Double = if (a.isNaN) b else if (b.isNaN) a else a.max(b)
  private def fpMin(a: Double, b: Double): Double = if (a.isNaN) b else if (b.isNaN) a else a.min(b)
  private def fpMax(a: Float, b: Float): Float = if (a.isNaN) b else if (b.isNaN) a else a.max(b)
  private def fpMin(a: Float, b: Float): Float = if (a.isNaN) b else if (b.isNaN) a else a.min(b)

  protected def finiteMap(els: Iterable[(Expr, Expr)], default: Expr, from: Type, to: Type): FiniteMap = {
    FiniteMap(els.toMap.toSeq.filter { case (_, value) => value != default }.sortBy(_._1.toString), default, from, to)
  }

  private lazy val functionEquality = options.findOptionOrDefault(solvers.unrolling.optFunctionEquality)

  /** Equality between the values `v1` and `v2` (see [[solvers.unrolling.optFunctionEquality]]).
    *
    * - Under `intensional` equality, functions are compared structurally.
    * - Under `none`, comparing functions is an evaluation error. Extracted models never compare
    *   functions, and queries that do are rejected by the solvers.
    * - Under `extensional` equality, structurally distinct functions are equal iff they agree on every
    *   input. They are told apart by their results on the closed subexpressions of the right type
    *   that they contain (for extracted models, the inputs that tell them apart), and their equality
    *   is undecidable otherwise. */
  protected def valuesEqual(v1: Expr, v2: Expr)(using rctx: RC, gctx: GC): Boolean = (v1, v2) match {
    case _ if functionEquality == solvers.unrolling.FunctionEquality.Intensional => v1 == v2
    case (ADT(id1, _, args1), ADT(id2, _, args2)) =>
      id1 == id2 && (args1 zip args2).forall(valuesEqual)
    case (Tuple(es1), Tuple(es2)) =>
      (es1 zip es2).forall(valuesEqual)
    case (l1: Lambda, l2: Lambda) if functionEquality == solvers.unrolling.FunctionEquality.None =>
      throw EvalError(s"Functions can't be compared under --function-equality=none: ${l1.asString} and ${l2.asString}")
    case _ if v1 == v2 => true
    case (l1: Lambda, l2: Lambda) =>
      def candidates(tpe: Type): Seq[Expr] = (Seq(l1, l2).flatMap { l =>
        exprOps.collect[Expr] {
          case c if c.getType == tpe && exprOps.variablesOf(c).isEmpty => Set(c)
          case _ => Set.empty
        } (l.body)
      } ++ scala.util.Try(simplestValue(tpe, allowSolver = false)).toOption).distinct

      val inputs = l1.params.foldRight(Seq(Seq.empty[Expr])) { (vd, rest) =>
        for (arg <- candidates(vd.getType); args <- rest) yield arg +: args
      }.take(100)

      def differOn(args: Seq[Expr]): Boolean = scala.util.Try {
        val values = args.map(e)
        !valuesEqual(e(Application(l1, values)), e(Application(l2, values)))
      }.getOrElse(false)

      if (inputs.exists(differOn)) false
      else throw EvalError(s"Can't decide whether ${l1.asString} and ${l2.asString} are equal")
    case _ => false
  }

  /** Evaluates `expr`.
    *
    * The cases are split by theory into the `eCore`, `eArithmetic`, ... methods below, which are
    * tried in order (see [[utils.CaseSplit]]). Subclasses can override `e` itself, or a single family.
    */
  protected[evaluators] def e(expr: Expr)(using rctx: RC, gctx: GC): Expr = {
    // The solvers evaluate the values of their models, which can be huge, with evaluators whose
    // context is interrupted along with them (see `Z3Solver` and `AbstractUnrollingSolver`)
    if (interruptManager.isInterrupted) throw RuntimeError("Evaluation interrupted")
    eCore(expr) otherwise eArithmetic(expr) otherwise eStrings(expr) otherwise eBitVectors(expr) otherwise
      eFloatingPoint(expr) otherwise eCollections(expr) otherwise unexpected(expr)
  }

  protected def unexpected(expr: Expr): Nothing =
    throw EvalError("Unhandled case in Evaluator : [" + expr.getClass + "] " + expr.asString)

  /** Variables, functions, booleans, ADTs, lambdas, quantifiers and literals. */
  protected def eCore(expr: Expr)(using rctx: RC, gctx: GC): Expr = expr match {
    case v: Variable =>
      rctx.mappings.get(v.toVal) match {
        case Some(v) => v
        case None => throw EvalError("No value for variable " + v + " in mapping " + rctx.mappings)
      }

    case Application(callee, args) =>
      e(callee) match {
        case l @ Lambda(params, body) =>
          val newArgs = args.map(e)
          val mapping = l.paramSubst(newArgs)
          e(body)(using rctx.withNewVars(mapping), gctx)
        case f =>
          throw EvalError("Cannot apply non-lambda function " + f.asString)
      }

    case Tuple(ts) =>
      val tsRec = ts.map(e)
      Tuple(tsRec)

    case TupleSelect(t, i) =>
      val Tuple(rs) = e(t): @unchecked
      rs(i-1)

    case Let(i,ex,b) =>
      val first = e(ex)
      e(b)(using rctx.withNewVar(i, first), gctx)

    case Assume(cond, body) =>
      if (!ignoreContractsOn(expr) && e(cond) != BooleanLiteral(true))
        throw RuntimeError("Assumption did not hold @" + expr.getPos)
      e(body)

    case IfExpr(cond, thenn, elze) =>
      val first = e(cond)
      first match {
        case BooleanLiteral(true) => e(thenn)
        case BooleanLiteral(false) => e(elze)
        case _ => throw EvalError(typeErrorMsg(first, BooleanType()))
      }

    case FunctionInvocation(id, tps, args) =>
      if (gctx.stepsLeft < 0) {
        throw RuntimeError("Exceeded number of allocated methods calls ("+gctx.maxSteps+")")
      }
      gctx.stepsLeft -= 1

      val tfd = getFunction(id, tps)
      val evArgs = args map e

      // build a mapping for the function...
      val frame = rctx.withNewVars(tfd.paramSubst(evArgs)).newTypes(tps)

      e(tfd.fullBody)(using frame, gctx)

    case And(Seq(e1, e2)) => e(e1) match {
      case BooleanLiteral(false) => BooleanLiteral(false)
      case BooleanLiteral(true) => e(e2)
      case le => throw EvalError("Unexpected operation (" + le.asString + ") && (" + e2.asString + ")")
    }

    case And(args) =>
      e(And(args.head, And(args.tail)))

    case Or(Seq(e1, e2)) => e(e1) match {
      case BooleanLiteral(true) => BooleanLiteral(true)
      case BooleanLiteral(false) => e(e2)
      case le => throw EvalError("Unexpected operation (" + le.asString + ") || (" + e2.asString + ")")
    }

    case Or(args) =>
      e(Or(args.head, Or(args.tail)))

    case Not(arg) =>
      e(arg) match {
        case BooleanLiteral(v) => BooleanLiteral(!v)
        case other => throw EvalError(typeErrorMsg(other, BooleanType()))
      }

    case Implies(l,r) =>
      e(l) match {
        case BooleanLiteral(false) => BooleanLiteral(true)
        case BooleanLiteral(true) => e(r)
        case le => throw EvalError(typeErrorMsg(le, BooleanType()))
      }

    case Equals(le,re) =>
      BooleanLiteral(valuesEqual(e(le), e(re)))

    case ADT(id, tps, args) =>
      val cc = ADT(id, tps.map(_.getType), args.map(e))
      if (!ignoreContractsOn(expr)) {
        val sort = cc.getConstructor.sort
        sort.invariant.foreach { tfd =>
          val v = Variable.fresh("x", ADTType(sort.id, sort.tps), true)
          e(tfd.applied(Seq(v)))(using rctx.withNewVar(v.toVal, cc), gctx) match {
            case BooleanLiteral(true) =>
            case BooleanLiteral(false) =>
              throw RuntimeError("ADT invariant violation for " + cc.asString)
            case other =>
              throw RuntimeError("Invariant type error: " + typeErrorMsg(other, BooleanType()))
          }
        }
      }
      cc

    case IsConstructor(expr, id) => e(expr) match {
      case ADT(`id`, _, _) => BooleanLiteral(true)
      case _ => BooleanLiteral(false)
    }

    case ADTSelector(expr, sel) =>
      e(expr) match {
        case adt @ ADT(id, tps, args) =>
          if (adt.getConstructor.fields.exists(_.id == sel))
            args(adt.getConstructor.definition.selectorID2Index(sel))
          else throw EvalError(s"Constructor ${id.asString} has no field ${sel.asString}")
        case le =>
          throw EvalError(typeErrorMsg(le, expr.getType))
      }

    case l @ Lambda(_, _) =>
      def normalizeLambda(l: Lambda, onlySimple: Boolean = false): Lambda = {
        val (nl, deps) = normalizeStructure(l, onlySimple = onlySimple)
        val newCtx = deps.foldLeft(rctx) {
          case (rctx, (v, dep, conds)) =>
            if (conds.forall(e(_)(using rctx, gctx) == BooleanLiteral(true)))
              rctx.withNewVar(v.toVal, e(dep)(using rctx, gctx))
            else rctx
        }
        val mapping = variablesOf(nl).map(v => v -> newCtx.mappings(v.toVal)).toMap
        replaceFromSymbols(mapping, nl).asInstanceOf[Lambda]
      }

      // We start by normalizing the structure of the lambda as in the solver to
      // evaluate all normalizable ground expressions within its body. The values of its free
      // variables are substituted first, so that the result doesn't depend on whether the lambda
      // refers to a value through a variable or directly: `x => l.head.f(x)` with `l` bound to
      // `Cons(g, Nil())` must give the same lambda as `x => Cons(g, Nil()).head.f(x)`, in which
      // the selection is ground and therefore evaluated.
      val closed = replaceFromSymbols(variablesOf(l).flatMap(v => rctx.mappings.get(v.toVal).map(v -> _)).toMap, l)
      val ground = normalizeLambda(closed.asInstanceOf[Lambda])

      // Then, in order for nested lambdas to have fresh variables in their argument
      // lists and let bindings, we re-normalize the identifiers by passing
      // `onlySimple = true` to the call to `normalizeStructure` (this avoids lifting
      // ground lambdas out in the deps).
      val normalized = normalizeLambda(ground, onlySimple = true)
      simplifyTrivialApps(normalized)

    case f: Forall => onForallInvocation(
      replaceFromSymbols(variablesOf(f).map(v => v -> e(v)).toMap, f).asInstanceOf[Forall], rctx.interpretations)

    case Error(_, msg) =>
      throw RuntimeError("Error reached in evaluation: " + msg)

    // The model gives uninterpreted functions as functions of their arguments
    case UninterpretedCall(id, tps, args, tpe) =>
      val evArgs = args map e
      rctx.interpretations.get(id -> tps) match {
        case Some(l: Lambda) if l.params.size == evArgs.size =>
          e(l.body)(using rctx.withNewVars(l.paramSubst(evArgs)), gctx)
        case _ => throw EvalError(s"Cannot call uninterpreted function ${id.asString} that the model doesn't define")
      }

    case gl: GenericValue => gl
    case fl : FractionLiteral => normalizeFraction(fl)
    case l : Literal[_] => l

    case _ => unhandled
  }

  /** Integer, real and bit-vector arithmetic and comparisons. */
  protected def eArithmetic(expr: Expr)(using rctx: RC, gctx: GC): Expr = expr match {
    case Plus(l,r) =>
      (e(l), e(r)) match {
        case (BVLiteral(sig1, i1, s1), BVLiteral(sig2, i2, s2)) if sig1 == sig2 && s1 == s2 =>
          BVLiteral(sig1, (1 to s1).foldLeft((BitSet.empty, false)) { case ((res, carry), i) =>
            val (b1, b2) = (i1(i), i2(i))
            val nextCarry = (b1 && b2) || (b1 && carry) || (b2 && carry)
            val ri = b1 ^ b2 ^ carry
            (if (ri) res + i else res, nextCarry)
          }._1, s1)
        case (IntegerLiteral(i1), IntegerLiteral(i2)) => IntegerLiteral(i1 + i2)
        case (FractionLiteral(ln, ld), FractionLiteral(rn, rd)) =>
          normalizeFraction(FractionLiteral(ln * rd + rn * ld, ld * rd))
        case (le,re) => throw EvalError("Unexpected operation: (" + le.asString + ") + (" + re.asString + ")")
      }

    case Minus(l,r) =>
      (e(l), e(r)) match {
        case (b1: BVLiteral, b2: BVLiteral) => e(Plus(b1, UMinus(b2)))
        case (IntegerLiteral(i1), IntegerLiteral(i2)) => IntegerLiteral(i1 - i2)
        case (FractionLiteral(ln, ld), FractionLiteral(rn, rd)) =>
          normalizeFraction(FractionLiteral(ln * rd - rn * ld, ld * rd))
        case (le,re) => throw EvalError("Unexpected operation: (" + le.asString + ") - (" + re.asString + ")")
      }

    case UMinus(ex) =>
      e(ex) match {
        case b @ BVLiteral(sig, _, s) =>
          BVLiteral(sig, if (sig) -b.toBigInt else BigInt(2).pow(s) - b.toBigInt, s)
        case IntegerLiteral(i) => IntegerLiteral(-i)
        case FractionLiteral(n, d) => FractionLiteral(-n, d)
        case re => throw EvalError("Unexpected operation: -(" + re.asString + ")")
      }

    case Times(l,r) =>
      (e(l), e(r)) match {
        case (BVLiteral(sig1, i1, s1), BVLiteral(sig2, i2, s2)) if sig1 == sig2 && s1 == s2 =>
          i1.foldLeft(BVLiteral(sig1, 0, s1): Expr) { case (res, i) =>
            e(Plus(res, BVLiteral(sig1, shift(i2, s2, i-1), s1)))
          }
        case (IntegerLiteral(i1), IntegerLiteral(i2)) => IntegerLiteral(i1 * i2)
        case (FractionLiteral(ln, ld), FractionLiteral(rn, rd)) =>
          normalizeFraction(FractionLiteral((ln * rn), (ld * rd)))
        case (le,re) => throw EvalError("Unexpected operation: (" + le.asString + ") * (" + re.asString + ")")
      }

    case Division(l,r) =>
      (e(l), e(r)) match {
        case (b1 @ BVLiteral(sig1, _, s1), b2 @ BVLiteral(sig2, _, s2)) if sig1 == sig2 && s1 == s2 =>
          val (bi1, bi2) = (b1.toBigInt, b2.toBigInt)
          // As in SMT-LIB, `bvudiv` by zero sets all the bits, and `bvsdiv` by zero gives -1 for a
          // non-negative dividend and 1 for a negative one
          if (bi2 != 0) BVLiteral(sig1, bi1 / bi2, s1)
          else if (!sig1) BVLiteral(false, BigInt(2).pow(s1) - 1, s1)
          else BVLiteral(true, if (bi1 >= 0) -1 else 1, s1)
        case (IntegerLiteral(i1), IntegerLiteral(i2)) =>
          // SMT-LIB's euclidean division, and leaves division by zero unspecified
          if(i2 != BigInt(0)) IntegerLiteral(utils.euclideanDivision(i1, i2)) else throw RuntimeError("Division by 0.")
        case (FractionLiteral(ln, ld), FractionLiteral(rn, rd)) =>
          if (rn != 0)
            normalizeFraction(FractionLiteral(ln * rd, ld * rn))
          else throw RuntimeError("Division by 0.")
        case (le,re) => throw EvalError("Unexpected operation: (" + le.asString + ") / (" + re.asString + ")")
      }

    case Remainder(l,r) =>
      (e(l), e(r)) match {
        case (b1 @ BVLiteral(sig1, _, s1), b2 @ BVLiteral(sig2, _, s2)) if sig1 == sig2 && s1 == s2 =>
          // As in SMT-LIB, the remainder of a division by zero is the dividend
          val bi2 = b2.toBigInt
          if (bi2 != 0) BVLiteral(sig1, b1.toBigInt % bi2, s1) else b1
        case (IntegerLiteral(i1), IntegerLiteral(i2)) =>
          // the remainder of the euclidean division, which is SMT-LIB's `mod`
          if(i2 != BigInt(0)) IntegerLiteral(i1 mod i2.abs) else throw RuntimeError("Remainder of division by 0.")
        case (le,re) => throw EvalError("Unexpected operation: (" + le.asString + ") rem (" + re.asString + ")")
      }

    case Modulo(l,r) =>
      (e(l), e(r)) match {
        case (b1 @ BVLiteral(sig1, _, s1), b2 @ BVLiteral(sig2, _, s2)) if sig1 == sig2 && s1 == s2 =>
          // SMT-LIB's `bvsmod` (or `bvurem`): the result has the sign of the divisor, and the modulo by zero
          // is the dividend
          val bi2 = b2.toBigInt
          if (bi2 == 0) b1
          else {
            val r = b1.toBigInt mod bi2.abs
            BVLiteral(sig1, if (bi2 < 0 && r != 0) r + bi2 else r, s1)
          }
        case (IntegerLiteral(i1), IntegerLiteral(i2)) =>
          if(i2 < 0)
            IntegerLiteral(i1 mod (-i2))
          else if(i2 != BigInt(0))
            IntegerLiteral(i1 mod i2)
          else
            throw RuntimeError("Modulo of division by 0.")
        case (le,re) => throw EvalError("Unexpected operation: (" + le.asString + ") % (" + re.asString + ")")
      }

    case LessThan(l,r) =>
      (e(l), e(r)) match {
        case (b1 @ BVLiteral(sig1, _, s1), b2 @ BVLiteral(sig2, _, s2)) if sig1 == sig2 && s1 == s2 =>
          BooleanLiteral(b1.toBigInt < b2.toBigInt)
        case (IntegerLiteral(i1), IntegerLiteral(i2)) => BooleanLiteral(i1 < i2)
        case (a @ FractionLiteral(_, _), b @ FractionLiteral(_, _)) =>
          val FractionLiteral(n, _) = e(Minus(a, b)): @unchecked
          BooleanLiteral(n < 0)
        case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 < c2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type()))
      }

    case GreaterThan(l,r) =>
      (e(l), e(r)) match {
        case (b1 @ BVLiteral(sig1, _, s1), b2 @ BVLiteral(sig2, _, s2)) if sig1 == sig2 && s1 == s2 =>
          BooleanLiteral(b1.toBigInt > b2.toBigInt)
        case (IntegerLiteral(i1), IntegerLiteral(i2)) => BooleanLiteral(i1 > i2)
        case (a @ FractionLiteral(_, _), b @ FractionLiteral(_, _)) =>
          val FractionLiteral(n, _) = e(Minus(a, b)): @unchecked
          BooleanLiteral(n > 0)
        case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 > c2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type()))
      }

    case LessEquals(l,r) =>
      (e(l), e(r)) match {
        case (b1 @ BVLiteral(sig1, _, s1), b2 @ BVLiteral(sig2, _, s2)) if sig1 == sig2 && s1 == s2 =>
          BooleanLiteral(b1.toBigInt <= b2.toBigInt)
        case (IntegerLiteral(i1), IntegerLiteral(i2)) => BooleanLiteral(i1 <= i2)
        case (a @ FractionLiteral(_, _), b @ FractionLiteral(_, _)) =>
          val FractionLiteral(n, _) = e(Minus(a, b)): @unchecked
          BooleanLiteral(n <= 0)
        case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 <= c2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type()))
      }

    case GreaterEquals(l,r) =>
      (e(l), e(r)) match {
        case (b1 @ BVLiteral(sig1, _, s1), b2 @ BVLiteral(sig2, _, s2)) if sig1 == sig2 && s1 == s2 =>
          BooleanLiteral(b1.toBigInt >= b2.toBigInt)
        case (IntegerLiteral(i1), IntegerLiteral(i2)) => BooleanLiteral(i1 >= i2)
        case (a @ FractionLiteral(_, _), b @ FractionLiteral(_, _)) =>
          val FractionLiteral(n, _) = e(Minus(a, b)): @unchecked
          BooleanLiteral(n >= 0)
        case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 >= c2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type()))
      }

    case _ => unhandled
  }

  protected def eStrings(expr: Expr)(using rctx: RC, gctx: GC): Expr = expr match {
    case StringConcat(l, r) =>
      (e(l), e(r)) match {
        case (i1: StringLiteral, i2: StringLiteral) => StringLiteral(i1.value ++ i2.value)
        case (le,re) => throw EvalError(typeErrorMsg(le, StringType()))
      }

    case StringLength(a) => e(a) match {
      case a: StringLiteral => IntegerLiteral(a.value.length)
      case res => throw EvalError(typeErrorMsg(res, Int32Type()))
    }

    case SubString(a, start, end) => (e(a), e(start), e(end)) match {
      // Like SMT-LIB's str.substr, out of bounds indices give an empty or truncated string
      case (s: StringLiteral, IntegerLiteral(b), IntegerLiteral(c))  =>
        val a = s.value
        if (b < 0 || b >= a.length || c <= b) StringLiteral(Seq())
        else StringLiteral(a.slice(b.toInt, (c min a.length).toInt))
      case res => throw EvalError(typeErrorMsg(res._1, StringType()))
    }

    case _ => unhandled
  }

  /** Bit-vector specific operations and conversions. */
  protected def eBitVectors(expr: Expr)(using rctx: RC, gctx: GC): Expr = expr match {
    case BVNot(b) =>
      e(b) match {
        case BVLiteral(signed, bs, s) =>
          BVLiteral(signed, BitSet.empty ++ (1 to s).flatMap(i => if (bs(i)) None else Some(i)), s)
        case other => throw EvalError("Unexpected operation: ~(" + other.asString + ")")
      }

    case BVAnd(l, r) =>
      (e(l), e(r)) match {
        case (BVLiteral(sig1, i1, s1), BVLiteral(sig2, i2, s2)) if sig1 == sig2 && s1 == s2 => BVLiteral(sig1, i1 & i2, s1)
        case (le, re) => throw EvalError("Unexpected operation: (" + le.asString + ") & (" + re.asString + ")")
      }

    case BVOr(l, r) =>
      (e(l), e(r)) match {
        case (BVLiteral(sig1, i1, s1), BVLiteral(sig2, i2, s2)) if sig1 == sig2 && s1 == s2 => BVLiteral(sig1, i1 | i2, s1)
        case (le, re) => throw EvalError("Unexpected operation: (" + le.asString + ") | (" + re.asString + ")")
      }

    case BVXor(l,r) =>
      (e(l), e(r)) match {
        case (BVLiteral(sig1, i1, s1), BVLiteral(sig2, i2, s2)) if sig1 == sig2 && s1 == s2 => BVLiteral(sig1, i1 ^ i2, s1)
        case (le,re) => throw EvalError("Unexpected operation: (" + le.asString + ") ^ (" + re.asString + ")")
      }

    case BVShiftLeft(l,r) =>
      (e(l), e(r)) match {
        case (BVLiteral(sig1, i1, s1), b2 @ BVLiteral(sig2, _, s2)) if sig1 == sig2 && s1 == s2 =>
          BVLiteral(sig1, shift(i1, s1, shiftAmount(b2, s1)), s1)
        case (le,re) => throw EvalError("Unexpected operation: (" + le.asString + ") << (" + re.asString + ")")
      }

    case BVAShiftRight(l,r) =>
      (e(l), e(r)) match {
        case (BVLiteral(sig1, i1, s1), b2 @ BVLiteral(sig2, _, s2)) if sig1 == sig2 && s1 == s2 =>
          val amount = shiftAmount(b2, s1)
          val shifted = shift(i1, s1, -amount)
          // the vacated bits are copies of the most significant bit, as for SMT-LIB `bvashr`
          BVLiteral(sig1, if (i1(s1)) shifted ++ ((s1 - amount + 1) to s1) else shifted, s1)
        case (le,re) => throw EvalError("Unexpected operation: (" + le.asString + ") >> (" + re.asString + ")")
      }

    case BVLShiftRight(l,r) =>
      (e(l), e(r)) match {
        case (BVLiteral(sig1, i1, s1), b2 @ BVLiteral(sig2, _, s2)) if s1 == s2 && sig1 == sig2 =>
          BVLiteral(sig1, shift(i1, s1, -shiftAmount(b2, s1)), s1)
        case (le,re) => throw EvalError("Unexpected operation: (" + le.asString + ") >>> (" + re.asString + ")")
      }

    case BVNarrowingCast(expr, bvt) =>
      e(expr) match {
        case bv @ BVLiteral(signed, _, _) => BVLiteral(signed, bv.toBigInt, bvt.size)
        case x => throw EvalError(typeErrorMsg(x, BVType(bvt.signed, bvt.size + 1))) // or any larger BVType
      }

    case BVWideningCast(expr, bvt) =>
      e(expr) match {
        case bv @ BVLiteral(signed, _, _) => BVLiteral(signed, bv.toBigInt, bvt.size)
        case x => throw EvalError(typeErrorMsg(x, BVType(bvt.signed, bvt.size - 1))) // or any smaller BVType
      }

    case BVUnsignedToSigned(expr) =>
      e(expr) match {
        case BVLiteral(false, bits, size) => BVLiteral(true, bits, size)
        case x => throw EvalError("Expected unsigned bitvector type")
      }

    case BVSignedToUnsigned(expr) =>
      e(expr) match {
        case BVLiteral(true, bits, size) => BVLiteral(false, bits, size)
        case x => throw EvalError("Expected signed bitvector type")
      }

    case BVToInt(expr) =>
      e(expr) match {
        case bv: BVLiteral => IntegerLiteral(bv.toBigInt)
        case x => throw EvalError("Expected bitvector type")
      }

    case IntToBV(size, signed, expr) =>
      e(expr) match {
        case IntegerLiteral(value) => BVLiteral(signed, value mod BigInt(2).pow(size), size)
        case x => throw EvalError(typeErrorMsg(x, IntegerType()))
      }

    case _ => unhandled
  }

  protected def eFloatingPoint(expr: Expr)(using rctx: RC, gctx: GC): Expr = expr match {
    case FPEquals(lhs, rhs) =>
      (e(lhs), e(rhs)) match {
        case (Float32Literal(l1), Float32Literal(l2)) => BooleanLiteral(l1 == l2)
        case (Float64Literal(l1), Float64Literal(l2)) => BooleanLiteral(l1 == l2)
        case _ => throw EvalError("Unexpected operation: (" + lhs.asString + ") == (" + rhs.asString + ")")
      }

    case FPAdd(RoundNearestTiesToEven, lhs, rhs) =>
      (e(lhs), e(rhs)) match {
        case (Float32Literal(l1), Float32Literal(l2)) => Float32Literal(l1 + l2)
        case (Float64Literal(l1), Float64Literal(l2)) => Float64Literal(l1 + l2)
        case _ => throw EvalError("Unexpected operation: (" + lhs.asString + ") + (" + rhs.asString + ")")
      }

    case FPSub(RoundNearestTiesToEven, lhs, rhs) =>
      (e(lhs), e(rhs)) match {
        case (Float32Literal(l1), Float32Literal(l2)) => Float32Literal(l1 - l2)
        case (Float64Literal(l1), Float64Literal(l2)) => Float64Literal(l1 - l2)
        case _ => throw EvalError("Unexpected operation: (" + lhs.asString + ") - (" + rhs.asString + ")")
      }

    case FPMul(RoundNearestTiesToEven, lhs, rhs) =>
      (e(lhs), e(rhs)) match {
        case (Float32Literal(l1), Float32Literal(l2)) => Float32Literal(l1 * l2)
        case (Float64Literal(l1), Float64Literal(l2)) => Float64Literal(l1 * l2)
        case _ => throw EvalError("Unexpected operation: (" + lhs.asString + ") * (" + rhs.asString + ")")
      }

    case FPDiv(RoundNearestTiesToEven, lhs, rhs) =>
      (e(lhs), e(rhs)) match {
        case (Float32Literal(l1), Float32Literal(l2)) => Float32Literal(l1 / l2)
        case (Float64Literal(l1), Float64Literal(l2)) => Float64Literal(l1 / l2)
        case _ => throw EvalError("Unexpected operation: (" + lhs.asString + ") / (" + rhs.asString + ")")
      }

    case FPFMA(RoundNearestTiesToEven, e1, e2, e3) =>
      (e(e1), e(e2), e(e3)) match {
        case (Float32Literal(l1), Float32Literal(l2), Float32Literal(l3)) => Float32Literal(java.lang.Math.fma(l1, l2, l3))
        case (Float64Literal(l1), Float64Literal(l2), Float64Literal(l3)) => Float64Literal(java.lang.Math.fma(l1, l2, l3))
        case _ => throw EvalError(f"Unexpected operation: FMA($e1, $e2, $e3)")
      }

    case FPUMinus(expr) =>
      e(expr) match {
        case Float32Literal(l) => Float32Literal(-l)
        case Float64Literal(l) => Float64Literal(-l)
        case _ => throw EvalError("Unexpected operation: -" + expr.asString)
      }

    case FPAbs(expr) =>
      e(expr) match {
        case Float32Literal(l) => Float32Literal(Math.abs(l))
        case Float64Literal(l) => Float64Literal(Math.abs(l))
        case _ => throw EvalError("Unexpected operation: Math.abs(" + expr.asString + ")")
      }

    case FPMin(lhs, rhs) =>
      (e(lhs), e(rhs)) match {
        case (Float32Literal(l1), Float32Literal(l2)) => Float32Literal(fpMin(l1, l2))
        case (Float64Literal(l1), Float64Literal(l2)) => Float64Literal(fpMin(l1, l2))
        case _ => throw EvalError(f"Unexpected operation: min($lhs, $rhs)")
      }

    case FPMax(lhs, rhs) =>
      (e(lhs), e(rhs)) match {
        case (Float32Literal(l1), Float32Literal(l2)) => Float32Literal(fpMax(l1, l2))
        case (Float64Literal(l1), Float64Literal(l2)) => Float64Literal(fpMax(l1, l2))
        case _ => throw EvalError(f"Unexpected operation: max($lhs, $rhs)")
      }

    case FPRound(rm, expr) if roundingModes.contains(rm) =>
      e(expr) match {
        case Float32Literal(l) => Float32Literal(roundToIntegral(l.toDouble, rm).toFloat)
        case Float64Literal(l) => Float64Literal(roundToIntegral(l, rm))
        case _ => throw EvalError(f"Unexpected operation: round($expr)")
      }

    case Sqrt(RoundNearestTiesToEven, expr) =>
      e(expr) match {
        // The square root of a float, computed in double precision, rounds to the correctly
        // rounded float square root.
        case Float32Literal(l) => Float32Literal(Math.sqrt(l.toDouble).toFloat)
        case Float64Literal(l) => Float64Literal(Math.sqrt(l))
        case _ => throw EvalError("Unexpected operation: Math.sqrt(" + expr.asString + ")")
      }

    case FPToBV(size, signed, rm, expr) if roundingModes.contains(rm) =>
      val d = e(expr) match {
        case Float32Literal(l) => l.toDouble
        case Float64Literal(l) => l
        case _ => throw EvalError("Unexpected operation: fp.to_bv(" + expr.asString + ")")
      }
      val r = roundToIntegral(d, rm)
      // SMT-LIB leaves the conversion of NaN, infinities and out-of-range values unspecified
      if (r.isNaN || r.isInfinite) throw RuntimeError(s"Unspecified conversion of $d to a bitvector.")
      val i = BigDecimal(r).toBigInt
      val (lo, hi) =
        if (signed) (-BigInt(2).pow(size - 1), BigInt(2).pow(size - 1) - 1)
        else (BigInt(0), BigInt(2).pow(size) - 1)
      if (i < lo || i > hi) throw RuntimeError(s"Unspecified conversion of $d to a bitvector of $size bits.")
      BVLiteral(signed, i, size)

    case FPToReal(expr) =>
      val d = e(expr) match {
        case Float32Literal(l) => l.toDouble
        case Float64Literal(l) => l
        case _ => throw EvalError("Unexpected operation: fp.to_real(" + expr.asString + ")")
      }
      // SMT-LIB leaves the real value of NaN and infinities unspecified
      if (d.isNaN || d.isInfinite) throw RuntimeError(s"Unspecified conversion of $d to a real.")
      val exact = new java.math.BigDecimal(d)
      val unscaled = BigInt(exact.unscaledValue)
      normalizeFraction(
        if (exact.scale >= 0) FractionLiteral(unscaled, BigInt(10).pow(exact.scale))
        else FractionLiteral(unscaled * BigInt(10).pow(-exact.scale), 1)
      )

    case FPFromBinary(11, 53, expr) =>
      e(expr) match {
        case Int64Literal(l)   => Float64Literal(java.lang.Double.longBitsToDouble(l))
        case _ => throw EvalError("Unexpected operation:" + expr.asString + ".toBinaryFP")
      }

    case FPFromBinary(8, 24, expr) =>
      e(expr) match {
        case Int32Literal(l)   => Float32Literal(java.lang.Float.intBitsToFloat(l))
        case _ => throw EvalError("Unexpected operation:" + expr.asString + ".toBinaryFP")
      }

    case ToDouble(expr) =>
      e(expr) match {
        case Int8Literal(l)    => Float64Literal(l.toDouble)
        case Int16Literal(l)   => Float64Literal(l.toDouble)
        case Int32Literal(l)   => Float64Literal(l.toDouble)
        case Int64Literal(l)   => Float64Literal(l.toDouble)
        case Float32Literal(l) => Float64Literal(l.toDouble)
        case Float64Literal(l) => Float64Literal(l)
        // `BigInt.toDouble` and `BigInt.toFloat` round to the nearest value, ties to even
        case bv @ BVLiteral(false, _, _) => Float64Literal(bv.toBigInt.toDouble)
        case _ => throw EvalError("Unexpected operation:" + expr.asString + ".toDouble")
      }

    case ToFloat(expr) =>
      e(expr) match {
        case Int8Literal(l)    => Float32Literal(l.toFloat)
        case Int16Literal(l)   => Float32Literal(l.toFloat)
        case Int32Literal(l)   => Float32Literal(l.toFloat)
        case Int64Literal(l)   => Float32Literal(l.toFloat)
        case Float32Literal(l) => Float32Literal(l)
        case Float64Literal(l) => Float32Literal(l.toFloat)
        case bv @ BVLiteral(false, _, _) => Float32Literal(bv.toBigInt.toFloat)
        case _ => throw EvalError("Unexpected operation:" + expr.asString + ".toFloat")
      }

    case FPLessThan(lhs, rhs) =>
      (e(lhs), e(rhs)) match {
        case (Float32Literal(l1), Float32Literal(l2)) => BooleanLiteral(l1 < l2)
        case (Float64Literal(l1), Float64Literal(l2)) => BooleanLiteral(l1 < l2)
        case _ => throw EvalError("Unexpected operation: (" + lhs.asString + ") < (" + rhs.asString + ")")
      }

    case FPGreaterThan(lhs, rhs) =>
      (e(lhs), e(rhs)) match {
        case (Float32Literal(l1), Float32Literal(l2)) => BooleanLiteral(l1 > l2)
        case (Float64Literal(l1), Float64Literal(l2)) => BooleanLiteral(l1 > l2)
        case _ => throw EvalError("Unexpected operation: (" + lhs.asString + ") > (" + rhs.asString + ")")
      }

    case FPLessEquals(lhs, rhs) =>
      (e(lhs), e(rhs)) match {
        case (Float32Literal(l1), Float32Literal(l2)) => BooleanLiteral(l1 <= l2)
        case (Float64Literal(l1), Float64Literal(l2)) => BooleanLiteral(l1 <= l2)
        case _ => throw EvalError("Unexpected operation: (" + lhs.asString + ") <= (" + rhs.asString + ")")
      }

    case FPGreaterEquals(lhs, rhs) =>
      (e(lhs), e(rhs)) match {
        case (Float32Literal(l1), Float32Literal(l2)) => BooleanLiteral(l1 >= l2)
        case (Float64Literal(l1), Float64Literal(l2)) => BooleanLiteral(l1 >= l2)
        case _ => throw EvalError("Unexpected operation: (" + lhs.asString + ") >= (" + rhs.asString + ")")
      }

    case FPIsZero(expr) =>
      e(expr) match {
        case Float32Literal(l) => BooleanLiteral(l == 0)
        case Float64Literal(l) => BooleanLiteral(l == 0)
        case _ => throw EvalError("Unexpected operation: (" + expr.asString + ") == 0")
      }

    case FPIsInfinite(expr) =>
      e(expr) match {
        case Float32Literal(l) => BooleanLiteral(l.isInfinite)
        case Float64Literal(l) => BooleanLiteral(l.isInfinite)
        case _ => throw EvalError("Unexpected operation: (" + expr.asString + ").isInfinite")
      }

    case FPIsNaN(expr) =>
      e(expr) match {
        case Float32Literal(l) => BooleanLiteral(l.isNaN)
        case Float64Literal(l) => BooleanLiteral(l.isNaN)
        case _ => throw EvalError("Unexpected operation: (" + expr.asString + ").isNaN")
      }

    case FPIsPositive(expr) =>
      e(expr) match {
        case Float32Literal(l) => BooleanLiteral(l > 0f || l.equals(+0.0f))
        case Float64Literal(l) => BooleanLiteral(l > 0d || l.equals(+0.0d))
        case _ => throw EvalError("Unexpected operation: (" + expr.asString + ").isPositive")
      }

    case FPIsNormal(expr) =>
      e(expr) match {
        case Float32Literal(l) => BooleanLiteral(!l.isNaN && !l.isInfinite && Math.abs(l) >= java.lang.Float.MIN_NORMAL)
        case Float64Literal(l) => BooleanLiteral(!l.isNaN && !l.isInfinite && Math.abs(l) >= java.lang.Double.MIN_NORMAL)
        case _ => throw EvalError("Unexpected operation: (" + expr.asString + ").isNormal")
      }

    case FPIsSubnormal(expr) =>
      e(expr) match {
        case Float32Literal(l) => BooleanLiteral(l != 0 && Math.abs(l) < java.lang.Float.MIN_NORMAL)
        case Float64Literal(l) => BooleanLiteral(l != 0 && Math.abs(l) < java.lang.Double.MIN_NORMAL)
        case _ => throw EvalError("Unexpected operation: (" + expr.asString + ").isSubnormal")
      }

    case FPIsNegative(expr) =>
      e(expr) match {
        case Float32Literal(l) => BooleanLiteral(l < 0f || l.equals(-0.0f))
        case Float64Literal(l) => BooleanLiteral(l < 0d || l.equals(-0.0d))
        case _ => throw EvalError("Unexpected operation: (" + expr.asString + ").isNegative")
      }

    case _ => unhandled
  }

  /** Sets, bags and maps. */
  protected def eCollections(expr: Expr)(using rctx: RC, gctx: GC): Expr = expr match {
    case SetAdd(s1, elem) =>
      (e(s1), e(elem)) match {
        case (FiniteSet(els1, tpe), evElem) => finiteSet(els1 :+ evElem, tpe)
        case (le, re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case SetUnion(s1,s2) =>
      (e(s1), e(s2)) match {
        case (FiniteSet(els1, tpe), FiniteSet(els2, _)) => finiteSet(els1 ++ els2, tpe)
        case (le, re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case SetIntersection(s1,s2) =>
      (e(s1), e(s2)) match {
        case (FiniteSet(els1, tpe), FiniteSet(els2, _)) => finiteSet(els1 intersect els2, tpe)
        case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case SetDifference(s1,s2) =>
      (e(s1), e(s2)) match {
        case (FiniteSet(els1, tpe), FiniteSet(els2, _)) => finiteSet(els1.toSet -- els2, tpe)
        case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case MapMerge(cond, map1, map2) =>
      (e(cond), e(map1), e(map2)) match {
        case (FiniteSet(keys, kT), FiniteMap(kvs1, dflt1, _, vT), FiniteMap(kvs2, dflt2, _, _)) =>
          val fromFstMap = keys.map(_ -> dflt1).toMap ++ kvs1.toMap.view.filterKeys(keys.contains(_)).toMap
          val fromSndMap = kvs2.toMap -- keys
          finiteMap((fromFstMap ++ fromSndMap).toSeq, dflt2, kT, vT)
        case (c, m1, m2) =>
          throw EvalError(typeErrorMsg(c, cond.getType))
      }

    case ElementOfSet(el,s) => (e(el), e(s)) match {
      case (e, FiniteSet(els, _)) => BooleanLiteral(els.contains(e))
      case (l,r) => throw EvalError(typeErrorMsg(r, SetType(l.getType)))
    }

    case SubsetOf(s1,s2) => (e(s1), e(s2)) match {
      case (FiniteSet(els1, _),FiniteSet(els2, _)) => BooleanLiteral(els1.toSet.subsetOf(els2.toSet))
      case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
    }

    case f @ FiniteSet(els, base) =>
      finiteSet(els.map(e), base.getType)

    case BagAdd(bag, elem) => (e(bag), e(elem)) match {
      case (FiniteBag(els, tpe), evElem) =>
        val (matching, rest) = els.partition(_._1 == evElem)
        finiteBag(rest :+ (evElem -> matching.lastOption.map {
          case (_, IntegerLiteral(i)) => IntegerLiteral(i + 1)
          case (_, e) => throw EvalError(typeErrorMsg(e, IntegerType()))
        }.getOrElse(IntegerLiteral(1))), tpe)

      case (le, re) => throw EvalError(typeErrorMsg(le, bag.getType))
    }

    case MultiplicityInBag(elem, bag) => (e(elem), e(bag)) match {
      case (evElem, FiniteBag(els, tpe)) =>
        els.collect { case (k,v) if k == evElem => v }.lastOption.getOrElse(IntegerLiteral(0))
      case (le, re) => throw EvalError(typeErrorMsg(re, bag.getType))
    }

    case BagIntersection(b1, b2) => (e(b1), e(b2)) match {
      case (FiniteBag(els1, tpe), FiniteBag(els2, _)) =>
        val map2 = els2.toMap
        finiteBag(els1.flatMap { case (k, v) =>
          val i = (v, map2.getOrElse(k, IntegerLiteral(0))) match {
            case (IntegerLiteral(i1), IntegerLiteral(i2)) => i1 min i2
            case (le, re) => throw EvalError(typeErrorMsg(le, IntegerType()))
          }

          if (i <= 0) None else Some(k -> IntegerLiteral(i))
        }, tpe)

      case (le, re) => throw EvalError(typeErrorMsg(le, b1.getType))
    }

    case BagUnion(b1, b2) => (e(b1), e(b2)) match {
      case (FiniteBag(els1, tpe), FiniteBag(els2, _)) =>
        val (map1, map2) = (els1.toMap, els2.toMap)
        finiteBag((map1.keys ++ map2.keys).toSet.map { (k: Expr) =>
          k -> ((map1.getOrElse(k, IntegerLiteral(0)), map2.getOrElse(k, IntegerLiteral(0))) match {
            case (IntegerLiteral(i1), IntegerLiteral(i2)) => IntegerLiteral(i1 + i2)
            case (le, re) => throw EvalError(typeErrorMsg(le, IntegerType()))
          })
        }.toSeq, tpe)

      case (le, re) => throw EvalError(typeErrorMsg(le, b1.getType))
    }

    case BagDifference(b1, b2) => (e(b1), e(b2)) match {
      case (FiniteBag(els1, tpe), FiniteBag(els2, _)) =>
        val map2 = els2.toMap
        finiteBag(els1.flatMap { case (k, v) =>
          val i = (v, map2.getOrElse(k, IntegerLiteral(0))) match {
            case (IntegerLiteral(i1), IntegerLiteral(i2)) => i1 - i2
            case (le, re) => throw EvalError(typeErrorMsg(le, IntegerType()))
          }

          if (i <= 0) None else Some(k -> IntegerLiteral(i))
        }, tpe)

      case (le, re) => throw EvalError(typeErrorMsg(le, b1.getType))
    }

    case FiniteBag(els, base) =>
      finiteBag(els.map { case (k, v) => (e(k), e(v)) }, base.getType)

    case f @ FiniteMap(ss, dflt, kT, vT) =>
      finiteMap(ss.map{ case (k, v) => (e(k), e(v)) }, e(dflt), kT.getType, vT.getType)

    case g @ MapApply(m,k) => (e(m), e(k)) match {
      case (FiniteMap(ss, dflt, _, _), e) =>
        ss.toMap.getOrElse(e, dflt)
      case (l,r) =>
        throw EvalError(typeErrorMsg(l, MapType(r.getType, g.getType)))
    }

    case g @ MapUpdated(m, k, v) => (e(m), e(k), e(v)) match {
      case (FiniteMap(ss, dflt, kT, vT), ek, ev) =>
        finiteMap((ss.toMap + (ek -> ev)).toSeq, dflt, kT, vT)
      case (m,l,r) =>
        throw EvalError("Unexpected operation: " + m.asString +
          ".updated(" + l.asString + ", " + r.asString + ")")
    }

    case _ => unhandled
  }

  /**
    * Simplifies "trivial" lambdas appearing within `expr`.
    * In this context, a "trivial lambda" is one that does not make use of its formal parameters.
    * Example:
    *   The expression:
    *     (x: BigInt) => ((y: BigInt) => 0)(x)
    *   is simplified into:
    *     (x: BigInt) => 0
    */
  private def simplifyTrivialApps(expr: Expr)(using rctx: RC, gctx: GC): Expr = {
    def isLambdaTrivial(l: Lambda): Boolean =
      l.params.forall(vd => !occursIn(vd, l.body))

    val transformer = new ConcreteSelfTreeTransformer {
      override def transform(expr: Expr): Expr = expr match {
        case Application(l@Lambda(_, body), _) if isLambdaTrivial(l) =>
          body
        case Application(v: Variable, _) =>
          rctx.mappings.get(v.toVal) match {
            case Some(l@Lambda(_, body)) if isLambdaTrivial(l) =>
              body
            case _ =>
              // Fallback to recursive transformation of the *original* expression
              super.transform(expr)
          }
        case _ => super.transform(expr)
      }
    }
    transformer.transform(expr)
  }
}

object RecursiveEvaluator {
  def apply(p: InoxProgram, ctx: Context): RecursiveEvaluator { val program: p.type } = {
    class Impl(override val program: p.type)(using override val semantics: p.Semantics)
      extends RecursiveEvaluator(program, ctx) with HasDefaultGlobalContext with HasDefaultRecContext
    new Impl(p)(using p.getSemantics)
  }
}
