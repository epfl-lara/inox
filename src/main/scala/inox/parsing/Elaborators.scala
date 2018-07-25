/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

import scala.util.parsing.input._

import scala.language.implicitConversions

/** Contains description of (type-checking) constraints and
 *  and constrained values.
 */
trait Elaborators
  extends IRs
     with ExpressionDeconstructors
     with TypeDeconstructors
     with ExpressionElaborators
     with TypeElaborators
     with ConstraintSolvers {

  import trees.Type

  class ElaborationException(errors: Seq[ErrorLocation])
    extends Exception(errors.map(_.toString).mkString("\n\n"))

  trait Elaborator
    extends ExpressionDeconstructor
       with TypeDeconstructor
       with ExpressionElaborator
       with TypeElaborator {

    lazy val solver = new Solver

    def elaborate[A](c: Constrained[A]): A = c match {
      case Unsatisfiable(es) => throw new ElaborationException(es)
      case WithConstraints(ev, constraints) =>
        implicit val u = solver.solveConstraints(constraints)
        ev
    }
  }

  /** Represents a meta type-parameter. */
  class Unknown(val param: BigInt) extends trees.Type with Positional {
    override def toString: String = pos + "@MetaParam(" + param + ")"
  }

  object Unknown {
    def fresh(implicit position: Position): Unknown = new Unknown(next).setPos(position)

    private var i: BigInt = 0

    def next: BigInt = synchronized {
      val ret = i
      i += 1
      ret
    }
  }

  sealed abstract class TypeClass {
    def &(that: TypeClass) = (this, that) match {
      case (Bits, _) => Bits
      case (_, Bits) => Bits
      case (Integral, _) => Integral
      case (_, Integral) => Integral
      case (Numeric, _) => Numeric
      case (_, Numeric) => Numeric
      case _ => Comparable
    }

    def hasInstance(tpe: Type): Boolean
  }
  case object Comparable extends TypeClass {
    override def hasInstance(tpe: Type) = {
      tpe == trees.CharType() || Numeric.hasInstance(tpe)
    }
  }
  case object Numeric extends TypeClass {
    override def hasInstance(tpe: Type) = {
      tpe == trees.RealType() || Integral.hasInstance(tpe)
    }
  }
  case object Integral extends TypeClass {
    override def hasInstance(tpe: Type) = {
      tpe == trees.IntegerType() || Bits.hasInstance(tpe)
    }
  }
  case object Bits extends TypeClass {
    override def hasInstance(tpe: Type) =
      tpe.isInstanceOf[trees.BVType]
  }

  /** Maps meta type-parameters to actual types. */
  class Unifier(subst: Map[Unknown, Type]) {

    val instantiator = new trees.SelfTreeTransformer {
      override def transform(tpe: Type) = tpe match {
        case u: Unknown => subst.getOrElse(u, u)
        case _ => super.transform(tpe)
      }
    }

    def apply(tpe: trees.Type): trees.Type = instantiator.transform(tpe)
    def apply(expr: trees.Expr): trees.Expr = instantiator.transform(expr)
    def apply(vd: trees.ValDef): trees.ValDef = instantiator.transform(vd)
    def apply(c: Constraint): Constraint = c match {
      case Equal(a, b) => Equal(instantiator.transform(a), instantiator.transform(b)).setPos(c.pos)
      case HasClass(a, cl) => HasClass(instantiator.transform(a), cl).setPos(c.pos)
      case AtIndexEqual(a, b, idx) => AtIndexEqual(instantiator.transform(a), instantiator.transform(b), idx).setPos(c.pos)
    }
  }

  /** Constraint on type(s). */
  abstract class Constraint(val types: Seq[Type]) extends Positional
  case class Equal(a: Type, b: Type) extends Constraint(Seq(a, b))
  case class HasClass(a: Type, c: TypeClass) extends Constraint(Seq(a))
  case class AtIndexEqual(tup: Type, mem: Type, idx: Int) extends Constraint(Seq(tup, mem))

  object Constraint {
    def exist(a: Unknown)(implicit position: Position): Constraint = Equal(a, a).setPos(position)
    def equal(a: Type, b: Type)(implicit position: Position): Constraint = Equal(a, b).setPos(position)
    def isNumeric(a: Type)(implicit position: Position): Constraint = HasClass(a, Numeric).setPos(position)
    def isIntegral(a: Type)(implicit position: Position): Constraint = HasClass(a, Integral).setPos(position)
    def isComparable(a: Type)(implicit position: Position): Constraint = HasClass(a, Comparable).setPos(position)
    def isBitVector(a: Type)(implicit position: Position): Constraint = HasClass(a, Bits).setPos(position)
    def atIndex(tup: Type, mem: Type, idx: Int)(implicit position: Position) = AtIndexEqual(tup, mem, idx).setPos(position)
  }

  case class Eventual[+A](fun: Unifier => A)

  implicit def eventualToValue[A](e: Eventual[A])(implicit unifier: Unifier): A = e.fun(unifier)

  case class Store(store: Map[String, (Identifier, Type, Eventual[Type])]) {
    def apply(name: String): (Identifier, Type, Eventual[Type]) = store(name)
    def contains(name: String): Boolean = store contains name

    def +(p: (String, Identifier, Type, Eventual[Type])): Store = this + (p._1, p._2, p._3, p._4)
    def +(name: String, id: Identifier, simple: Type, tpe: Eventual[Type]): Store =
      Store(store + (name -> ((id, simple, tpe))))
  }

  def getIdentifier(id: ExprIR.Identifier): Identifier = id match {
    case ExprIR.IdentifierIdentifier(i) => i
    case ExprIR.IdentifierName(name) => inox.FreshIdentifier(name)
    case ExprIR.IdentifierHole(_) => throw new Error("Expression contains holes.")
  }

  object Store {
    def empty: Store = Store(Map())
  }

  /** Represents a set of constraints with a value.
   *
   * The value contained is not directly available,
   * but can be obtained from a `Unifier`.
   *
   * Such a `Unifier` should be obtained by solving the constraints.
   *
   * This class offers an applicative functor interface.
   */
  sealed abstract class Constrained[+A] {

    def map[B](f: A => (Unifier => B)): Constrained[B] = this match {
      case Unsatisfiable(es) => Unsatisfiable(es)
      case WithConstraints(v, cs) => WithConstraints(Eventual(implicit u => f(v)(u)), cs)
    }

    def flatMap[B](f: (Eventual[A]) => Constrained[B]): Constrained[B] = this match {
      case Unsatisfiable(es) => Unsatisfiable(es)
      case WithConstraints(fA, csA) => f(fA) match {
        case Unsatisfiable(fs) => Unsatisfiable(fs)
        case WithConstraints(fB, csB) => WithConstraints(fB, csA ++ csB)
      }
    }

    def transform[B](f: A => B): Constrained[B] = this match {
      case Unsatisfiable(es) => Unsatisfiable(es)
      case WithConstraints(v, cs) => WithConstraints(Eventual(implicit u => f(v)), cs)
    }

    def combine[B, C](that: Constrained[B])(f: (A, B) => C): Constrained[C] = (this, that) match {
      case (WithConstraints(vA, csA), WithConstraints(vB, csB)) => WithConstraints(Eventual(implicit u => f(vA, vB)), csA ++ csB)
      case (Unsatisfiable(es), Unsatisfiable(fs)) => Unsatisfiable(es ++ fs)
      case (Unsatisfiable(es), _) => Unsatisfiable(es)
      case (_, Unsatisfiable(fs)) => Unsatisfiable(fs)
    }

    def app[B, C](that: Constrained[B])(implicit ev: A <:< (B => C)): Constrained[C] =
      this.combine(that)((f: A, x: B) => ev(f)(x))

    def get(implicit unifier: Unifier): A = this match {
      case WithConstraints(vA, cs) => vA
      case Unsatisfiable(_) => throw new Exception("Unsatisfiable.get")
    }

    def addConstraint(constraint: => Constraint): Constrained[A] = addConstraints(Seq(constraint))

    def addConstraints(constraints: => Seq[Constraint]): Constrained[A] = this match {
      case WithConstraints(vA, cs) => WithConstraints(vA, constraints ++ cs)
      case Unsatisfiable(es) => Unsatisfiable(es)
    }
    def checkImmediate(condition: Boolean, error: String, location: Position): Constrained[A] = this match {
      case Unsatisfiable(es) if (!condition) => Unsatisfiable(es :+ ErrorLocation(error, location))
      case WithConstraints(_, _) if (!condition) => Unsatisfiable(Seq(ErrorLocation(error, location)))
      case _ => this
    }
  }
  case class Unsatisfiable(errors: Seq[ErrorLocation]) extends Constrained[Nothing]
  case class WithConstraints[A](value: Eventual[A], constraints: Seq[Constraint]) extends Constrained[A]

  object Constrained {
    def fail(error: String, location: Position) = Unsatisfiable(Seq(ErrorLocation(error, location)))
    def fail(errors: Seq[(String, Position)]) = {
      assert(!errors.isEmpty)
      Unsatisfiable(errors.map({ case (error, location) => ErrorLocation(error, location)}))
    }
    def pure[A](x: A): Constrained[A] = WithConstraints(Eventual(implicit u => x), Seq())
    def unify[A](f: Unifier => A): Constrained[A] = WithConstraints(Eventual(f), Seq())

    def sequence[A](cs: Seq[Constrained[A]]): Constrained[Seq[A]] = {
      val zero: Constrained[Seq[A]] = pure(Seq[A]())
      val cons: (A, Seq[A]) => Seq[A] = (x: A, xs: Seq[A]) => x +: xs

      cs.foldRight(zero) {
        case (c, acc) => c.combine(acc)(cons)
      }
    }
  }
}
