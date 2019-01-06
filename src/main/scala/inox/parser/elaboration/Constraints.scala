package inox
package parser
package elaboration

import scala.util.parsing.input.Position

trait Constraints { self: IRs with SimpleTypes with ElaborationErrors =>

  import SimpleTypes._
  import TypeClasses._
  import Constraints._

  sealed trait Constraint
  object Constraints {
    case class Exists(elem: Type) extends Constraint
    case class Equals(left: Type, right: Type) extends Constraint
    case class HasClass(elem: Type, typeClass: TypeClass) extends Constraint
    case class OneOf(tpe: Type, typeOptions: Seq[Type]) extends Constraint
  }

  object Constraint {
    def exist(elem: Unknown): Constraint = Exists(elem)
    def equal(left: Type, right: Type): Constraint = Equals(left, right)
    def isNumeric(elem: Type): Constraint = HasClass(elem, Numeric)
    def isIntegral(elem: Type): Constraint = HasClass(elem, Integral)
    def isComparable(elem: Type): Constraint = HasClass(elem, Comparable)
    def isBits(elem: Type, lower: Option[Int] = None, upper: Option[Int] = None, signed: Boolean = true) =
      HasClass(elem, Bits(signed, (lower, upper) match {
        case (None, None) => NoSpec
        case (Some(l), None) => GreaterEquals(l)
        case (None, Some(u)) => LessEquals(u)
        case (Some(l), Some(u)) => Between(l, u).validate.getOrElse {
          throw new IllegalArgumentException("Invalid bounds.")
        }
      }))
    def atIndexIs(scrutinee: Type, index: Int, value: Type): Constraint =
      HasClass(scrutinee, WithIndices(Map(index -> value)))
    def hasFields(elem: Type, fields: Set[String], sorts: Seq[(inox.Identifier, Type => Seq[Constraint])]): Constraint = {
      val mapping = sorts.foldLeft(Map[inox.Identifier, Type => Seq[Constraint]]()) {
        case (acc, (id, f)) => acc.get(id) match {
          case None => acc + (id -> f)
          case Some(f2) => acc + (id -> { (t: Type) => f2(t) ++ f(t) })
        }
      }
      HasClass(elem, WithFields(fields, mapping))
    }
    def oneOf(tpe: Type, typeOptions: Seq[Type]): Constraint =
      OneOf(tpe, typeOptions)
  }

  class Eventual[+A] private(private val fun: Unifier => A) {
    def get(implicit unifier: Unifier): A = fun(unifier)

    def map[B](f: A => B): Eventual[B] =
      new Eventual(fun andThen f)

    def flatMap[B](f: A => Eventual[B]): Eventual[B] =
      new Eventual((u: Unifier) => f(fun(u)).fun(u))
  }

  object Eventual {
    def pure[A](x: A): Eventual[A] = new Eventual((u: Unifier) => x)
    def withUnifier[A](f: Unifier => A) = new Eventual(f)
    def sequence[A](eventuals: Seq[Eventual[A]]): Eventual[Seq[A]] =
      new Eventual((u: Unifier) => eventuals.map(_.get(u)))
    def sequence[K, A](eventuals: Map[K, Eventual[A]]): Eventual[Map[K, A]] =
      new Eventual((u: Unifier) => eventuals.mapValues(_.get(u)))
    def unify[A](value: A)(implicit ev: Unifiable[A]): Eventual[A] =
      ev.unify(value)
  }

  class Unifier private(mapping: Map[Unknown, Type]) {
    def get(unknown: Unknown): Type = mapping.getOrElse(unknown, unknown)

    def +(pair: (Unknown, Type)): Unifier =
      new Unifier(Unifier(pair)(mapping) + pair)

    def apply[A](value: A)(implicit unifiable: Unifiable[A]): A =
      unifiable.unify(value).get(this)
  }
  object Unifier {
    def apply(pair: (Unknown, Type)): Unifier = new Unifier(Map(pair))
    def empty: Unifier = new Unifier(Map())
  }

  trait Unifiable[A] {
    def unify(value: A): Eventual[A]
  }

  object Unifiable {
    def apply[A](fun: A => Eventual[A]): Unifiable[A] = new Unifiable[A] {
      override def unify(value: A): Eventual[A] = fun(value)
    }
  }

  implicit lazy val simpleTypeUnifiable: Unifiable[Type] = Unifiable {
    case u: Unknown => Eventual.withUnifier(_.get(u))
    case FunctionType(froms, to) => for {
      fs <- Eventual.unify(froms)
      t  <- Eventual.unify(to)
    } yield FunctionType(fs, t)
    case MapType(from, to) => for {
      f <- Eventual.unify(from)
      t <- Eventual.unify(to)
    } yield MapType(f, t)
    case SetType(elem) => for {
      e <- Eventual.unify(elem)
    } yield SetType(e)
    case BagType(elem) => for {
      e <- Eventual.unify(elem)
    } yield BagType(e)
    case TupleType(elems) => for {
      es <- Eventual.unify(elems)
    } yield TupleType(es)
    case ADTType(identifier, args) => for {
      as <- Eventual.unify(args)
    } yield ADTType(identifier, as)
    case tpe => Eventual.pure(tpe)
  }

  implicit lazy val constraintUnifiable: Unifiable[Constraint] = Unifiable {
    case Constraints.Exists(elem) => for {
      e <- Eventual.unify(elem)
    } yield Constraints.Exists(e)
    case Constraints.Equals(left, right) => for {
      l <- Eventual.unify(left)
      r <- Eventual.unify(right)
    } yield Constraints.Equals(l, r)
    case Constraints.HasClass(elem, typeClass) => for {
      e <- Eventual.unify(elem)
      t <- Eventual.unify(typeClass)
    } yield Constraints.HasClass(e, t)
    case OneOf(tpe, typeOptions) =>
      for {
        t <- Eventual.unify(tpe)
        goal <- Eventual.sequence(typeOptions.map(Eventual.unify(_)))
      } yield Constraints.OneOf(t, goal)
  }


  implicit lazy val typeClassUnifiable: Unifiable[TypeClass] = Unifiable {
    case WithFields(fields, sorts) => for {
      ss <- Eventual.sequence(sorts.mapValues { (function: Type => Seq[Constraint]) =>
        Eventual.withUnifier { (unifier: Unifier) =>
          function andThen (_.map(unifier(_)))
        }
      }.view.force)
    } yield WithFields(fields, ss)
    case WithIndices(indices) => for {
      is <- Eventual.sequence(indices.mapValues(Eventual.unify(_)).view.force)
    } yield WithIndices(is)
    case x => Eventual.pure(x)
  }

  implicit lazy val typeSequenceUnifiable: Unifiable[Seq[SimpleTypes.Type]] = Unifiable {
    a: Seq[SimpleTypes.Type] => for {
      ss <- Eventual.sequence(a.map(tpe => Eventual.withUnifier { implicit unifier => unifier(tpe) }))
    } yield ss.distinct
  }

  implicit def seqUnifiable[A](implicit inner: Unifiable[A]): Unifiable[Seq[A]] = Unifiable { xs: Seq[A] =>
    Eventual.sequence(xs.map(inner.unify(_)))
  }

  implicit def mapUnifiable[K, A](implicit inner: Unifiable[A]): Unifiable[Map[K, A]] = Unifiable { xs: Map[K, A] =>
    Eventual.sequence(xs.mapValues(inner.unify(_)).view.force)
  }

  class Constrained[+A] private(val get: Either[ErrorMessage, (A, Seq[Constraint])]) {
    def map[B](f: A => B): Constrained[B] =
      new Constrained(get.right.map { case (v, cs) => (f(v), cs) })

    def flatMap[B](f: A => Constrained[B]): Constrained[B] =
      new Constrained(get.right.flatMap { case (v1, cs1) =>
        val other = f(v1).get
        other.right.map { case (v2, cs2) => (v2, cs1 ++ cs2) }
      })

    def addConstraint(constraint: Constraint): Constrained[A] =
      new Constrained(get.right.map { case (v, cs) => (v, cs :+ constraint) })

    def addConstraints(constraints: Seq[Constraint]): Constrained[A] =
      constraints.foldLeft(this) { case (acc, c) => acc.addConstraint(c) }

    def checkImmediate(condition: Boolean, error: => ErrorMessage): Constrained[A] =
      if (condition) this else Constrained.fail(error)

    def checkImmediate(condition: A => Boolean, error: => ErrorMessage): Constrained[A] =
      flatMap { x =>
        if (condition(x)) Constrained.pure(x) else Constrained.fail(error)
      }

    def checkImmediate(condition: Boolean, where: IR, error: Position => String): Constrained[A] =
      if (condition) this else Constrained.fail(error(where.pos))

    def checkImmediate(condition: A => Boolean, where: IR, error: A => Position => String): Constrained[A] =
      flatMap { x =>
        if (condition(x)) Constrained.pure(x) else Constrained.fail(error(x)(where.pos))
      }

    def withFilter(pred: A => Boolean): Constrained[A] = new Constrained(get match {
      case Right((a, _)) if !pred(a) => Left(filterError)
      case _ => get
    })
  }

  object Constrained {
    def apply(constraints: Constraint*): Constrained[Unit] = {
      constraints.foldLeft(pure(())) {
        case (acc, constraint) => acc.addConstraint(constraint)
      }
    }

    def pure[A](x: A): Constrained[A] = {
      new Constrained(Right((x, Seq())))
    }
    def fail(error: ErrorMessage): Constrained[Nothing] =
      new Constrained(Left(error))

    def sequence[A](constraineds: Seq[Constrained[A]]): Constrained[Seq[A]] = {
      constraineds.foldLeft(Constrained.pure(Seq[A]())) {
        case (acc, constrained) => for {
          xs <- acc
          x <- constrained
        } yield xs :+ x
      }
    }

    def attempt[A](opt: Option[A], error: => ErrorMessage): Constrained[A] = opt match {
      case Some(x) => Constrained.pure(x)
      case None => Constrained.fail(error)
    }

    def attempt[A](opt: Option[A], where: IR, error: Position => ErrorMessage): Constrained[A] = opt match {
      case Some(x) => Constrained.pure(x)
      case None => Constrained.fail(error(where.pos))
    }

    def checkImmediate(condition: Boolean, error: => ErrorMessage): Constrained[Unit] =
      if (condition) Constrained.pure(()) else Constrained.fail(error)

    def checkImmediate(condition: Boolean, where: IR, error: Position => String): Constrained[Unit] =
      if (condition) Constrained.pure(()) else Constrained.fail(error(where.pos))
  }

  object TypeClasses {

    sealed abstract class SizeSpec {
      def combine(that: SizeSpec): Option[SizeSpec]

      def accepts(value: Int) = this match {
        case LessEquals(upper) => value <= upper
        case GreaterEquals(lower) => value >= lower
        case Between(lower, upper) => value >= lower && value <= upper
        case NoSpec => true
      }
    }
    case object NoSpec extends SizeSpec {
      override def combine(that: SizeSpec): Option[SizeSpec] = Some(that)
    }
    case class LessEquals(value: Int) extends SizeSpec {
      override def combine(that: SizeSpec): Option[SizeSpec] = that match {
        case LessEquals(other) => Some(LessEquals(Math.min(value, other)))
        case GreaterEquals(other) => Between(value, other).validate
        case Between(low, high) => Between(low, Math.min(value, high)).validate
        case NoSpec => Some(this)
      }
    }
    case class GreaterEquals(value: Int) extends SizeSpec {
      override def combine(that: SizeSpec): Option[SizeSpec] = that match {
        case LessEquals(other) => Between(other, value).validate
        case GreaterEquals(other) => Some(GreaterEquals(Math.max(value, other)))
        case Between(low, high) => Between(Math.max(value, low), high).validate
        case NoSpec => Some(this)
      }
    }
    case class Between(low: Int, high: Int) extends SizeSpec {
      def validate: Option[Between] = if (high >= low) Some(this) else None

      override def combine(that: SizeSpec): Option[SizeSpec] = that match {
        case LessEquals(other) => Between(low, Math.min(high, other)).validate
        case GreaterEquals(other) => Between(Math.max(low, other), high).validate
        case Between(otherLow, otherHigh) => Between(Math.max(low, otherLow), Math.min(high, otherHigh)).validate
        case NoSpec => Some(this)
      }
    }

    sealed abstract class TypeClass {

      def combine(that: TypeClass)(tpe: Type): Option[Seq[Constraint]] = (this, that) match {
        case (WithFields(fs1, s1), WithFields(fs2, s2)) => {
          val intersect: Seq[inox.Identifier] = s1.keySet.intersect(s2.keySet).toSeq

          val size = intersect.size
          if (size == 0) {
            None
          }
          if (size == 1) {
            val id = intersect.head
            Some(s1(id)(tpe) ++ s2(id)(tpe))
          }
          else {
            Some(Seq(HasClass(tpe, WithFields(fs1 union fs2, intersect.map { id =>
              id -> ((t: Type) => s1(id)(t) ++ s2(id)(t))
            }.toMap))))
          }
        }
        case (_, WithFields(_, _)) => None
        case (WithFields(_, _), _) => None
        case (WithIndices(is1), WithIndices(is2)) => {
          val union: Seq[Int] = is1.keySet.union(is2.keySet).toSeq
          val intersect: Seq[Int] = is1.keySet.intersect(is2.keySet).toSeq

          val is3 = union.map { k =>
            k -> is1.getOrElse(k, is2(k))
          }.toMap

          Some(HasClass(tpe, WithIndices(is3)) +: intersect.map { (i: Int) => Equals(is1(i), is2(i)) })
        }
        case (_, WithIndices(_)) => None
        case (WithIndices(_), _) => None
        case (Bits(signed1, _), Bits(signed2, _)) if signed1 != signed2 => None
        case (Bits(signed, size1), Bits(_, size2)) => size1.combine(size2).map {
          case Between(low, high) if low == high => Seq(Equals(tpe, BitVectorType(signed, low)))
          case s3 => Seq(HasClass(tpe, Bits(signed, s3)))
        }
        case (b: Bits, _) => Some(Seq(HasClass(tpe, b)))
        case (_, b: Bits) => Some(Seq(HasClass(tpe, b)))
        case (Integral, _) => Some(Seq(HasClass(tpe, Integral)))
        case (_, Integral) => Some(Seq(HasClass(tpe, Integral)))
        case (Numeric, _) => Some(Seq(HasClass(tpe, Numeric)))
        case (_, Numeric) => Some(Seq(HasClass(tpe, Numeric)))
        case _ => Some(Seq(HasClass(tpe, Comparable)))
      }

      def accepts(tpe: Type): Option[Seq[Constraint]]
    }

    case class WithFields(fields: Set[String], sorts: Map[inox.Identifier, Type => Seq[Constraint]]) extends TypeClass {
      override def accepts(tpe: Type) = tpe match {
        case ADTType(id, _) => sorts.get(id).map{_.apply(tpe)}
        case _ => None
      }
    }

    case class WithIndices(indices: Map[Int, Type]) extends TypeClass {
      override def accepts(tpe: Type) = tpe match {
        case TupleType(es) => indices.toSeq.map { case (k, v) =>
          if (es.size < k) None else Some(Equals(es(k - 1), v))
        }.foldLeft(Option(Seq[Constraint]())) {
          case (acc, constraint) => acc.flatMap { xs => constraint.map { x => xs :+ x }}
        }
        case _ => None
      }
    }

    case object Comparable extends TypeClass {
      override def accepts(tpe: Type) = tpe match {
        case CharType() => Some(Seq())
        case _ => Numeric.accepts(tpe)
      }
    }
    case object Numeric extends TypeClass {
      override def accepts(tpe: Type) = tpe match {
        case RealType() => Some(Seq())
        case _ => Integral.accepts(tpe)
      }
    }
    case object Integral extends TypeClass {
      override def accepts(tpe: Type) = tpe match {
        case IntegerType() => Some(Seq())
        case _ => Bits(true, NoSpec).accepts(tpe).orElse(Bits(false, NoSpec).accepts(tpe))
      }
    }
    case class Bits(signed: Boolean, size: SizeSpec) extends TypeClass {
      override def accepts(tpe: Type) = tpe match {
        case BitVectorType(`signed`, value) => if (size.accepts(value)) Some(Seq()) else None
        case _ => None
      }
    }
  }
}