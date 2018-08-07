package inox
package parser
package elaboration

trait Constraints { self: IRs with SimpleTypes =>

  import SimpleTypes._
  import TypeClasses.TypeClass
  import Constraints._

  sealed trait Constraint
  object Constraints {
    case class Exists(elem: Type) extends Constraint
    case class Equals(left: Type, right: Type) extends Constraint
    case class HasClass(elem: Type, typeClass: TypeClass) extends Constraint
    case class HasSortIn(sorts: Seq[(inox.Identifier, Type => Seq[Constraint])]) extends Constraint
    case class AtIndexIs(scrutinee: Type, index: Int, value: Type) extends Constraint
  }

  object Constraint {
    def exist(elem: Unknown): Constraint = Exists(elem)
    def equal(left: Type, right: Type): Constraint = Equals(left, right)
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
    def unify[A](value: A)(implicit ev: Unifiable[A]): Eventual[A] =
      ev.unify(value)
  }

  class Unifier(mapping: Map[Unknown, Type]) {
    def get(unknown: Unknown): Type = mapping(unknown)

    def +(pair: (Unknown, Type)): Unifier =
      new Unifier(mapping + pair)

    def apply[A](value: A)(implicit unifiable: Unifiable[A]): A =
      unifiable.unify(value).get(this)
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
    case Exists(elem) => for {
      e <- Eventual.unify(elem)
    } yield Exists(e)
    case Equals(left, right) => for {
      l <- Eventual.unify(left)
      r <- Eventual.unify(right)
    } yield Equals(l, r)
    case HasClass(elem, typeClass) => for {
      e <- Eventual.unify(elem)
    } yield HasClass(e, typeClass)
    case HasSortIn(sorts) => for {
      ss <- Eventual.sequence(sorts.map {
        case (identifier, function) => Eventual.withUnifier {
          (unifier: Unifier) => (identifier, function andThen (_.map(unifier(_))))
        }
      })
    } yield HasSortIn(ss)
    case AtIndexIs(scrutinee, index, value) => for {
      s <- Eventual.unify(scrutinee)
      v <- Eventual.unify(value)
    } yield AtIndexIs(s, index, v)
  }

  implicit def seqUnifiable[A](implicit inner: Unifiable[A]): Unifiable[Seq[A]] = Unifiable { xs: Seq[A] =>
    Eventual.sequence(xs.map(inner.unify(_)))
  }

  type Error = String

  class Constrained[+A] private(private val get: Either[Error, (A, Seq[Constraint])]) {
    def map[B](f: A => B): Constrained[B] =
      new Constrained(get.right.map { case (v, cs) => (f(v), cs) })

    def flatMap[B](f: A => Constrained[B]): Constrained[B] =
      new Constrained(get.right.flatMap { case (v1, cs1) =>
        val other = f(v1).get
        other.right.map { case (v2, cs2) => (v2, cs1 ++ cs2) }
      })

    def addConstraint(constraint: Constraint): Constrained[A] =
      new Constrained(get.right.map { case (v, cs) => (v, cs :+ constraint) })

    def checkImmediate(condition: Boolean, error: => Error): Constrained[A] =
      if (condition) this else Constrained.fail(error)

    def withFilter(pred: A => Boolean): Constrained[A] = new Constrained(get match {
      case Right((a, _)) if !pred(a) => Left("TODO: Error.")
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
    def fail(error: Error): Constrained[Nothing] =
      new Constrained(Left(error))

    def sequence[A](constraineds: Seq[Constrained[A]]): Constrained[Seq[A]] = {
      constraineds.foldLeft(Constrained.pure(Seq[A]())) {
        case (acc, constrained) => for {
          xs <- acc
          x <- constrained
        } yield xs :+ x
      }
    }

    def attempt[A](opt: Option[A], error: => Error): Constrained[A] = opt match {
      case Some(x) => Constrained.pure(x)
      case None => Constrained.fail(error)
    }

    def checkImmediate(condition: Boolean, error: => Error): Constrained[Unit] =
      if (condition) Constrained.pure(()) else Constrained.fail(error)
  }

  object TypeClasses {

    sealed abstract class TypeClass {
      val name: String

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
      override val name = "Comparable"

      override def hasInstance(tpe: Type) = {
        tpe == CharType() || Numeric.hasInstance(tpe)
      }
    }
    case object Numeric extends TypeClass {
      override val name = "Numeric"

      override def hasInstance(tpe: Type) = {
        tpe == RealType() || Integral.hasInstance(tpe)
      }
    }
    case object Integral extends TypeClass {
      override val name = "Integral"

      override def hasInstance(tpe: Type) = {
        tpe == IntegerType() || Bits.hasInstance(tpe)
      }
    }
    case object Bits extends TypeClass {
      override val name = "Bits"

      override def hasInstance(tpe: Type) = tpe match {
        case BitVectorType(_) => true
        case _ => false
      }
    }
  }
}