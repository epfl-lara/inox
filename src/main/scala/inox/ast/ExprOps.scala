/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

import transformers._
import scala.collection.mutable.{Map => MutableMap}

/** Provides functions to manipulate [[Expressions.Expr]].
  *
  * This object provides a few generic operations on Inox expressions,
  * as well as some common operations.
  *
  * The generic operations lets you apply operations on a whole tree
  * expression. You can look at:
  *   - [[GenTreeOps.fold foldRight]]
  *   - [[GenTreeOps.preTraversal preTraversal]]
  *   - [[GenTreeOps.postTraversal postTraversal]]
  *   - [[GenTreeOps.preMap preMap]]
  *   - [[GenTreeOps.postMap postMap]]
  *   - [[GenTreeOps.genericTransform genericTransform]]
  *
  * These operations usually take a higher order function that gets applied to the
  * expression tree in some strategy. They provide an expressive way to build complex
  * operations on Inox expressions.
  *
  */
class ExprOps private(val trees: Trees)
                     (override val sourceTrees: trees.type,
                      override val targetTrees: trees.type)
  extends GenTreeOps { self =>

  def this(trees: Trees) = this(trees)(trees, trees)

  import trees._

  type Source = Expr
  type Target = Expr

  val Deconstructor = Operator

  /** Replaces bottom-up variables by looking up for them in a map */
  def replaceFromSymbols[V <: VariableSymbol](substs: Map[V, Expr], expr: Expr)(using VariableConverter[V]): Expr = {
    new ConcreteSelfTreeTransformer {
      override def transform(expr: Expr): Expr = expr match {
        case v: Variable => substs.getOrElse(v.to[V], super.transform(v))
        case _ => super.transform(expr)
      }
    }.transform(expr)
  }

  object VariableExtractor {
    def unapply(e: Expr): Option[Set[Variable]] = {
      val (_, vs, _, _, _, _) = deconstructor.deconstruct(e)
      Some(vs.toSet)
    }
  }

  /** Returns the set of free variables in an expression */
  def variablesOf(expr: Expr): Set[Variable] = expr match {
    case v: Variable => Set(v)
    case _ =>
      val (_, vs, es, tps, _, _) = deconstructor.deconstruct(expr)
      vs.foldRight(es.flatMap(variablesOf).toSet ++ tps.flatMap(typeOps.variablesOf)) {
        case (v, vars) => vars - v ++ typeOps.variablesOf(v.tpe)
      }
  }

  /** A choice of a value of `res` that satisfies `pred`: the call of the uninterpreted function
    * `res.id`, at the type parameters of the choice and over the variables in its `scope` and its
    * free variables, whose result is refined by `pred`. The same choice at the same values of these
    * variables gives the same value, and a path where no value satisfies `pred` is infeasible.
    *
    * The scope of a choice are the variables bound where it occurs, such as the parameters of the
    * function whose body it is in, so that it may give different values for different values of
    * these variables even when `pred` doesn't refer to them.
    */
  def choose(res: ValDef, pred: Expr, scope: Seq[Variable] = Seq.empty): UninterpretedCall = {
    val result = RefinementType(res, pred)

    // The free variables of the choice, with those that their types refer to
    def close(vs: Set[Variable]): Set[Variable] = {
      val next = vs ++ vs.flatMap(v => typeOps.variablesOf(v.tpe))
      if (next == vs) vs else close(next)
    }

    // A variable comes after the variables that its type refers to
    def order(todo: Seq[Variable], done: Seq[Variable]): Seq[Variable] = {
      val (ready, rest) = todo.partition(v => (typeOps.variablesOf(v.tpe) -- done - v).isEmpty)
      if (ready.isEmpty) done ++ rest else order(rest, done ++ ready)
    }

    val args = order(close(typeOps.variablesOf(result) ++ scope).toSeq.sortBy(_.id.globalId), Seq.empty)
    val tpe = if (args.isEmpty) FunctionType(Seq.empty, result) else PiType(args.map(_.toVal), result)
    val tps = typeOps.typeParamsOf(tpe).toSeq.sortBy(_.id.globalId)
    UninterpretedCall(res.id, tps, args, tpe).copiedFrom(pred)
  }

  /** Views an uninterpreted call whose result type is refined as a choice of a value of the result
    * that satisfies the refinement, at the arguments of the call (see [[choose]]). */
  object Choice {
    def unapply(e: Expr): Option[(ValDef, Expr)] = e match {
      case UninterpretedCall(_, _, args, tpe) => tpe match {
        case FunctionType(Seq(), RefinementType(vd, pred)) => Some((vd, pred))
        case PiType(params, to) if params.size == args.size =>
          typeOps.replaceFromSymbols((params zip args).toMap, to) match {
            case RefinementType(vd, pred) => Some((vd, pred))
            case _ => None
          }
        case _ => None
      }
      case _ => None
    }
  }

  /** The body of a function without definition: the call of a fresh uninterpreted function over
    * the parameters of the function, at its type parameters. */
  def uninterpretedBody(name: String, tparams: Seq[TypeParameterDef], params: Seq[ValDef], returnType: Type): UninterpretedCall =
    UninterpretedCall(FreshIdentifier(name), tparams.map(_.tp), params.map(_.toVariable),
      if (params.isEmpty) FunctionType(Seq.empty, returnType) else PiType(params, returnType))

  /** Freshens all local variables */
  protected class Freshener extends ConcreteSelfTransformer {
    type Env = Map[Identifier, Identifier]

    override def transform(id: Identifier, env: Env): Identifier = {
      env.getOrElse(id, id)
    }

    override def transform(e: Expr, env: Env): Expr = e match {
      case Let(vd, v, b) =>
        val freshVd = vd.freshen
        Let(transform(freshVd, env), transform(v, env), transform(b, env.updated(vd.id, freshVd.id))).copiedFrom(e)

      case Lambda(params, b) =>
        val (sparams, senv) = params.foldLeft((Seq[t.ValDef](), env)) {
          case ((sparams, env), vd) =>
            val freshVd = vd.freshen
            (sparams :+ transform(freshVd, env), env.updated(vd.id, freshVd.id))
        }
        Lambda(sparams, transform(b, senv)).copiedFrom(e)

      case Forall(params, b) =>
        val (sparams, senv) = params.foldLeft((Seq[t.ValDef](), env)) {
          case ((sparams, env), vd) =>
            val freshVd = vd.freshen
            (sparams :+ transform(freshVd, env), env.updated(vd.id, freshVd.id))
        }
        Forall(sparams, transform(b, senv)).copiedFrom(e)

      case _ =>
        super.transform(e, env)
    }

    override def transform(tpe: s.Type, env: Env): t.Type = tpe match {
      case RefinementType(vd, prop) =>
        val freshVd = vd.freshen
        RefinementType(transform(freshVd, env), transform(prop, env.updated(vd.id, freshVd.id))).copiedFrom(tpe)

      case PiType(params, to) =>
        val (sparams, senv) = params.foldLeft((Seq[t.ValDef](), env)) {
          case ((sparams, env), vd) =>
            val freshVd = vd.freshen
            (sparams :+ transform(freshVd, env), env.updated(vd.id, freshVd.id))
        }
        PiType(sparams, transform(to, senv)).copiedFrom(tpe)

      case SigmaType(params, to) =>
        val (sparams, senv) = params.foldLeft((Seq[t.ValDef](), env)) {
          case ((sparams, env), vd) =>
            val freshVd = vd.freshen
            (sparams :+ transform(freshVd, env), env.updated(vd.id, freshVd.id))
        }
        SigmaType(sparams, transform(to, senv)).copiedFrom(tpe)

      case _ => super.transform(tpe, env)
    }
  }

  def freshenLocals(expr: Expr): Expr = {
    new Freshener().transform(expr, Map.empty[Identifier, Identifier])
  }

  /** Returns true if the expression contains a function call */
  def containsFunctionCalls(expr: Expr): Boolean = {
    exists{
      case _: FunctionInvocation => true
      case _ => false
    }(expr)
  }

  /** Returns all Function calls found in the expression */
  def functionCallsOf(expr: Expr): Set[FunctionInvocation] = {
    collect[FunctionInvocation] {
      case f: FunctionInvocation => Set(f)
      case _ => Set()
    }(expr)
  }

  /** Returns '''true''' if the formula is Ground,
    * which means that it does not contain any variables
    * ([[variablesOf]] e is empty)
    */
  def isGround(e: Expr): Boolean = variablesOf(e).isEmpty

  /** Returns '''true''' if the formula is simple,
    * which means that it requires no special encoding for an
    * unrolling solver. See implementation for what this means exactly.
    */
  def isSimple(e: Expr): Boolean = !exists {
    case (_: Assume) | (_: Forall) | (_: Lambda) | (_: Error) |
         (_: FunctionInvocation) | (_: UninterpretedCall) | (_: Application) => true
    case _ => false
  } (e)

  /* Checks if a given expression is 'real' and does not contain generic
   * values. */
  def isRealExpr(v: Expr): Boolean = {
    !exists {
      case gv: GenericValue => true
      case _ => false
    }(v)
  }

  def preTraversalWithParent(f: (Expr, Option[Tree]) => Unit, initParent: Option[Tree] = None)(e: Expr): Unit = {
    val rec: Expr => Unit = preTraversalWithParent(f, Some(e))

    f(e, initParent)

    val Operator(es, _) = e: @unchecked
    es.foreach(rec)
  }

  /** Simple, local optimization on string */
  def simplifyString(expr: Expr): Expr = {
    def simplify0(expr: Expr): Expr = (expr match {
      case StringConcat(a: StringLiteral, b) if a.value.isEmpty => b
      case StringConcat(b, a: StringLiteral) if a.value.isEmpty => b
      case StringConcat(a: StringLiteral, b: StringLiteral) => StringLiteral(a.value ++ b.value)
      case StringLength(a: StringLiteral) => IntegerLiteral(a.value.length)
      case SubString(a: StringLiteral, IntegerLiteral(start), IntegerLiteral(end))
          if 0 <= start && start <= end && end <= a.value.length =>
        StringLiteral(a.value.slice(start.toInt, end.toInt))
      case _ => expr
    }).copiedFrom(expr)

    utils.fixpoint(simplePostTransform(simplify0))(expr)
  }

  /** Computes the negation of a boolean formula, with some simplifications. */
  def negate(expr: Expr) : Expr = {
    (expr match {
      case Let(i,b,e) => Let(i,b,negate(e))
      case Not(e) => e
      case Implies(e1,e2) => and(e1, negate(e2))
      case Or(exs) => and(exs map negate*)
      case And(exs) => or(exs map negate*)
      case LessThan(e1,e2) => GreaterEquals(e1,e2)
      case LessEquals(e1,e2) => GreaterThan(e1,e2)
      case GreaterThan(e1,e2) => LessEquals(e1,e2)
      case GreaterEquals(e1,e2) => LessThan(e1,e2)
      case IfExpr(c,e1,e2) => IfExpr(c, negate(e1), negate(e2))
      case BooleanLiteral(b) => BooleanLiteral(!b)
      case e => Not(e)
    }).setPos(expr)
  }

  /** Simple, local simplification on arithmetic
    *
    * You should not assume anything smarter than some constant folding and
    * simple cancellation. To avoid infinite cycle we only apply simplification
    * that reduce the size of the tree. The only guarantee from this function is
    * to not augment the size of the expression and to be sound.
    */
  def simplifyArithmetic(expr: Expr)(using Symbols): Expr = {
    // Extractor for BigInt and BV literals.
    sealed trait ExIntegerLit {
      def unapply(e: Expr): Option[BigInt]
    }
    case object ExBigIntLit extends ExIntegerLit {
      override def unapply(e: Expr): Option[BigInt] = e match {
        case IntegerLiteral(i) => Some(i)
        case _ => None
      }
    }
    case object ExBVLit extends ExIntegerLit {
      override def unapply(e: Expr): Option[BigInt] = e match {
        case bv@BVLiteral(_, _, _) => Some(bv.toBigInt)
        case _ => None
      }
    }

    def integerArithSimp(exLit: ExIntegerLit, ctor: BigInt => Expr)(expr: Expr): Option[Expr] = expr match {
      case Plus(exLit(i1), exLit(i2)) =>
        Some(ctor(i1 + i2))
      case Plus(exLit(zero), e) if zero == BigInt(0) => Some(e)
      case Plus(e, exLit(zero)) if zero == BigInt(0) => Some(e)
      case Plus(e1, UMinus(e2)) => Some(Minus(e1, e2))
      case Plus(Plus(e, exLit(i1)), exLit(i2)) =>
        Some(Plus(e, ctor(i1 + i2)))
      case Plus(Plus(exLit(i1), e), exLit(i2)) =>
        Some(Plus(ctor(i1 + i2), e))

      case Minus(e, exLit(zero)) if zero == BigInt(0) => Some(e)
      case Minus(exLit(zero), e) if zero == BigInt(0) => Some(UMinus(e))
      case Minus(exLit(i1), exLit(i2)) =>
        Some(ctor(i1 - i2))
      case Minus(e1, UMinus(e2)) => Some(Plus(e1, e2))
      case Minus(e1, Minus(UMinus(e2), e3)) => Some(Plus(e1, Plus(e2, e3)))

      case UMinus(exLit(x)) => Some(ctor(-x))
      case UMinus(UMinus(x)) => Some(x)
      case UMinus(Plus(UMinus(e1), e2)) => Some(Plus(e1, UMinus(e2)))
      case UMinus(Minus(e1, e2)) => Some(Minus(e2, e1))

      case Times(exLit(i1), exLit(i2)) =>
        Some(ctor(i1 * i2))
      case Times(exLit(one), e) if one == BigInt(1) => Some(e)
      case Times(exLit(mone), e) if mone == BigInt(-1) => Some(UMinus(e))
      case Times(e, exLit(one)) if one == BigInt(1) => Some(e)
      case Times(exLit(zero), _) if zero == BigInt(0) => Some(ctor(0))
      case Times(_, exLit(zero)) if zero == BigInt(0) => Some(ctor(0))
      case Times(exLit(i1), Times(exLit(i2), t)) =>
        Some(Times(ctor(i1 * i2), t))
      case Times(exLit(i1), Times(t, exLit(i2))) =>
        Some(Times(ctor(i1 * i2), t))
      case Times(exLit(i), UMinus(e)) => Some(Times(ctor(-i), e))
      case Times(UMinus(e), exLit(i)) => Some(Times(e, ctor(-i)))

      case d @ Division(exLit(i1), exLit(i2)) if i2 != BigInt(0) =>
        // integer division is euclidean, as in SMT-LIB, and bit-vector division rounds toward zero
        Some(ctor(if (exLit == ExBigIntLit) utils.euclideanDivision(i1, i2) else i1 / i2))
      case Division(e, exLit(one)) if one == BigInt(1) => Some(e)

      case _ => None
    }

    object ExIntegerArithSimp {
      def unapply(e: Expr): Option[Expr] = e.getType match {
        case IntegerType() => integerArithSimp(ExBigIntLit, IntegerLiteral.apply)(e)
        case BVType(signed, size) => integerArithSimp(ExBVLit, BVLiteral(signed, _, size))(e)
        case _ => None
      }
    }

    object Zero {
      def unapply(e: Expr): Option[Expr] = e.getType match {
        case IntegerType() => Some(IntegerLiteral(0))
        case BVType(signed, size) => Some(BVLiteral(signed, 0, size))
        case RealType() => Some(FractionLiteral(0, 1))
        case _ => None
      }
    }

    def simplify0(expr: Expr): Expr = (expr match {
      case ExIntegerArithSimp(e) => e

      //here we put more expensive rules
      //btw, I know those are not the most general rules, but they lead to good optimizations :)
      case Plus(UMinus(Plus(e1, e2)), e3) if e1 == e3 => UMinus(e2)
      case Plus(UMinus(Plus(e1, e2)), e3) if e2 == e3 => UMinus(e1)
      case m @ Minus(e1, e2) if e1 == e2 => Zero.unapply(m).getOrElse(m)
      case m @ Minus(Plus(e1, e2), Plus(e3, e4)) if e1 == e4 && e2 == e3 => Zero.unapply(m).getOrElse(m)
      case Minus(Plus(e1, e2), Plus(Plus(e3, e4), e5)) if e1 == e4 && e2 == e3 => UMinus(e5)

      case StringConcat(e: StringLiteral, a) if e.value.isEmpty => a
      case StringConcat(a, e: StringLiteral) if e.value.isEmpty => a
      case StringConcat(a: StringLiteral, b: StringLiteral) => StringLiteral(a.value ++ b.value)
      case StringConcat(a: StringLiteral, StringConcat(b: StringLiteral, c)) => StringConcat(StringLiteral(a.value ++ b.value), c)
      case StringConcat(StringConcat(c, a: StringLiteral), b: StringLiteral) => StringConcat(c, StringLiteral(a.value ++ b.value))
      case StringConcat(a, StringConcat(b, c)) => StringConcat(StringConcat(a, b), c)
      //default
      case e => e
    }).copiedFrom(expr)

    utils.fixpoint(simplePostTransform(simplify0))(expr)
  }

  /**
    * Some helper methods for FractionLiterals
    */
  def normalizeFraction(fl: FractionLiteral) = {
    val FractionLiteral(num, denom) = fl
    val modNum = if (num < 0) -num else num
    val modDenom = if (denom < 0) -denom else denom
    val divisor = modNum.gcd(modDenom)
    val simpNum = num / divisor
    val simpDenom = denom / divisor
    if (simpDenom < 0)
      FractionLiteral(-simpNum, -simpDenom)
    else
      FractionLiteral(simpNum, simpDenom)
  }

  val realzero = FractionLiteral(0, 1)
  def floor(fl: FractionLiteral): FractionLiteral = {
    val FractionLiteral(n, d) = normalizeFraction(fl)
    if (d == 0) throw new IllegalStateException("denominator zero")
    if (n == 0) realzero
    else if (n > 0) {
      //perform integer division
      FractionLiteral(n / d, 1)
    } else {
      //here the number is negative
      if (n % d == 0)
        FractionLiteral(n / d, 1)
      else {
        //perform integer division and subtract 1
        FractionLiteral(n / d - 1, 1)
      }
    }
  }

  def toCNF(e: Expr): Seq[Expr] = e match {
    case Let(i, e, b) => toCNF(b).map(b => Let(i, e, b))
    case And(es) => es.flatMap(toCNF)
    case Or(es) => es.map(toCNF).foldLeft(Seq[Expr](BooleanLiteral(false))) {
      case (clauses, es) => es.flatMap(e => clauses.map(c => or(c, e)))
    }
    case IfExpr(c, t, e) => toCNF(and(implies(c, t), implies(not(c), e)))
    case Implies(l, r) => toCNF(or(not(l), r))
    case Not(Or(es)) => toCNF(andJoin(es.map(not)))
    case Not(Implies(l, r)) => toCNF(and(l, not(r)))
    case Not(Not(e)) => toCNF(e)
    case Not(e) => Seq(not(e))
    case e => Seq(e)
  }

  /**
    * Does `vd` occurs free in the expression `e`?
    */
  def occursIn(vd: ValDef, e: Expr): Boolean = {
    class OccursIn(override val trees: self.trees.type, var occurs: Boolean) extends Traverser {
      override type Env = Unit

      override def traverse(vd2: trees.ValDef, env: Unit): Unit =
        occurs |= vd == vd2

      override def traverse(e: trees.Expr, env: Unit): Unit = {
        if (occurs) return

        e match {
          case Lambda(params, _) if params.contains(vd) => ()
          case Forall(params, _) if params.contains(vd) => ()
          case Let(binder, _, _) if binder == vd => ()
          case _ => super.traverse(e, ())
        }
      }
    }
    val occ = new OccursIn(self.trees, false)
    occ.traverse(e, ())
    occ.occurs
  }
}
