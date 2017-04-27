/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

import scala.util.parsing.input._

/** Contains description of (type-checking) constraints and
 *  and constrained values.
 */
trait Constraints { self: Interpolator =>

  import trees.Type

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

  sealed abstract class TypeClass extends Positional {
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
      tpe == trees.CharType || Numeric.hasInstance(tpe)
    }
  }
  case object Numeric extends TypeClass {
    override def hasInstance(tpe: Type) = {
      tpe == trees.RealType || Integral.hasInstance(tpe)
    }
  }
  case object Integral extends TypeClass {
    override def hasInstance(tpe: Type) = {
      tpe == trees.IntegerType || Bits.hasInstance(tpe)
    }
  }
  case object Bits extends TypeClass {
    override def hasInstance(tpe: Type) =
      tpe.isInstanceOf[trees.BVType]
  }

  /** Maps meta type-parameters to actual types. */
  class Unifier(mappings: Map[Unknown, Type]) {

    val instantiator = new trees.SelfTreeTransformer {
      override def transform(tpe: Type) = tpe match {
        case u: Unknown => if (mappings.contains(u)) mappings(u) else u
        case _ => super.transform(tpe)
      }
    }

    def apply(tpe: Type): Type = instantiator.transform(tpe)
    def apply(c: Constraint): Constraint = c match {
      case Equal(a, b) => Equal(instantiator.transform(a), instantiator.transform(b)).setPos(c.pos)
      case Subtype(a, b) => Subtype(instantiator.transform(a), instantiator.transform(b)).setPos(c.pos)
      case HasClass(a, cl) => HasClass(instantiator.transform(a), cl).setPos(c.pos)
      case AtIndexEqual(a, b, idx) => AtIndexEqual(instantiator.transform(a), instantiator.transform(b), idx).setPos(c.pos)
    }
  }

  /** Constraint on type(s). */
  abstract class Constraint(val types: Seq[Type]) extends Positional
  case class Equal(a: Type, b: Type) extends Constraint(Seq(a, b))
  case class Subtype(sub: Type, sup: Type) extends Constraint(Seq(sub, sup))
  case class HasClass(a: Type, c: TypeClass) extends Constraint(Seq(a))
  case class AtIndexEqual(tup: Type, mem: Type, idx: Int) extends Constraint(Seq(tup, mem))

  object Constraint {
    def equal(a: Type, b: Type)(implicit position: Position): Constraint = Equal(a, b).setPos(position)
    def subtype(a: Type, b: Type)(implicit position: Position): Constraint = Subtype(a, b).setPos(position)
    def isNumeric(a: Type)(implicit position: Position): Constraint = HasClass(a, Numeric.setPos(position)).setPos(position)
    def isIntegral(a: Type)(implicit position: Position): Constraint = HasClass(a, Integral.setPos(position)).setPos(position)
    def isComparable(a: Type)(implicit position: Position): Constraint = HasClass(a, Comparable.setPos(position)).setPos(position)
    def isBitVector(a: Type)(implicit position: Position): Constraint = HasClass(a, Bits.setPos(position)).setPos(position)
    def atIndex(tup: Type, mem: Type, idx: Int)(implicit position: Position) = AtIndexEqual(tup, mem, idx).setPos(position)
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

    def map[B](f: A => B): Constrained[B] = this match {
      case WithConstraints(v, cs) => WithConstraints(v andThen f, cs)
      case Unsatifiable(es) => Unsatifiable(es)
    }

    def combine[B, C](that: Constrained[B])(f: (A, B) => C): Constrained[C] = (this, that) match {
      case (WithConstraints(vA, csA), WithConstraints(vB, csB)) => WithConstraints((u: Unifier) => f(vA(u), vB(u)), csA ++ csB)
      case (Unsatifiable(es), Unsatifiable(fs)) => Unsatifiable(es ++ fs)
      case (Unsatifiable(es), _) => Unsatifiable(es)
      case (_, Unsatifiable(fs)) => Unsatifiable(fs)
    }

    def app[B, C](that: Constrained[B])(implicit ev: A <:< (B => C)): Constrained[C] =
      this.combine(that)((f: A, x: B) => ev(f)(x))

    def get(implicit unifier: Unifier): A = this match {
      case WithConstraints(vA, cs) => vA(unifier)
      case Unsatifiable(_) => throw new Exception("Unsatifiable.get")
    }

    def addConstraint(constraint: => Constraint): Constrained[A] = addConstraints(Seq(constraint))

    def addConstraints(constraints: => Seq[Constraint]): Constrained[A] = this match {
      case WithConstraints(vA, cs) => WithConstraints(vA, constraints ++ cs)
      case Unsatifiable(es) => Unsatifiable(es)
    }
    def checkImmediate(condition: Boolean, error: String, location: Position): Constrained[A] = this match {
      case Unsatifiable(es) if (!condition) => Unsatifiable(es :+ ErrorLocation(error, location))
      case WithConstraints(_, _) if (!condition) => Unsatifiable(Seq(ErrorLocation(error, location)))
      case _ => this
    }
  }
  case class Unsatifiable(errors: Seq[ErrorLocation]) extends Constrained[Nothing]
  case class WithConstraints[A](value: Unifier => A, constraints: Seq[Constraint]) extends Constrained[A]

  object Constrained {
    def fail(error: String, location: Position) = Unsatifiable(Seq(ErrorLocation(error, location)))
    def fail(errors: Seq[(String, Position)]) = {
      assert(!errors.isEmpty)
      Unsatifiable(errors.map({ case (error, location) => ErrorLocation(error, location)}))
    }
    def pure[A](x: A): Constrained[A] = WithConstraints((u: Unifier) => x, Seq())
    def withUnifier[A](f: Unifier => A) = WithConstraints(f, Seq())

    def sequence[A](cs: Seq[Constrained[A]]): Constrained[Seq[A]] = {
      val zero: Constrained[Seq[A]] = pure(Seq[A]())
      val cons: (A, Seq[A]) => Seq[A] = (x: A, xs: Seq[A]) => x +: xs

      cs.foldRight(zero) {
        case (c, acc) => c.combine(acc)(cons)
      }
    }
  }
}