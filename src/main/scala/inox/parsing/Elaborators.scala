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
     with DefinitionElaborators
     with ConstraintSolvers {

  import trees.Type
  import trees.ADTSort

  class ElaborationException(errors: Seq[ErrorLocation])
    extends Exception(errors.map(_.toString).mkString("\n\n"))

  trait Elaborator
    extends ExpressionDeconstructor
       with TypeDeconstructor
       with ExpressionElaborator
       with DefinitionElaborator
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
  case class HasSortIn(a: Type, sorts: Map[ADTSort, Type => Seq[Constraint]]) extends Constraint(Seq(a))

  object Constraint {
    def exist(a: Unknown)(implicit position: Position): Constraint = Equal(a, a).setPos(position)
    def equal(a: Type, b: Type)(implicit position: Position): Constraint = Equal(a, b).setPos(position)
    def isNumeric(a: Type)(implicit position: Position): Constraint = HasClass(a, Numeric).setPos(position)
    def isIntegral(a: Type)(implicit position: Position): Constraint = HasClass(a, Integral).setPos(position)
    def isComparable(a: Type)(implicit position: Position): Constraint = HasClass(a, Comparable).setPos(position)
    def isBitVector(a: Type)(implicit position: Position): Constraint = HasClass(a, Bits).setPos(position)
    def atIndex(tup: Type, mem: Type, idx: Int)(implicit position: Position) = AtIndexEqual(tup, mem, idx).setPos(position)
    def hasSortIn(a: Type, sorts: (ADTSort, Type => Seq[Constraint])*)(implicit position: Position) = HasSortIn(a, sorts.toMap).setPos(position)
  }

  case class Eventual[+A](fun: Unifier => A)

  implicit def eventualToValue[A](e: Eventual[A])(implicit unifier: Unifier): A = e.fun(unifier)

  class Store private(
    variables: Map[String, (Identifier, Type, Eventual[Type])],
    types: Map[String, trees.TypeParameter],
    functions: Map[String, trees.FunDef],
    constructors: Map[String, (trees.ADTSort, trees.ADTConstructor)],
    fields: Map[String, Seq[(trees.ADTSort, trees.ADTConstructor, trees.ValDef)]],
    sorts: Map[String, trees.ADTSort]) {

    def getVariable(name: String): (Identifier, Type, Eventual[Type]) = variables(name)
    def isVariable(name: String): Boolean = variables contains name

    def getTypeParameter(name: String): trees.TypeParameter = types(name)
    def isTypeParameter(name: String): Boolean = types contains name

    def getFunction(name: String): trees.FunDef = functions(name)
    def isFunction(name: String): Boolean = functions contains name

    def getConstructor(name: String): (trees.ADTSort, trees.ADTConstructor) = constructors(name)
    def isConstructor(name: String): Boolean = constructors contains name

    def getFields(name: String): Seq[(trees.ADTSort, trees.ADTConstructor, trees.ValDef)] = fields(name)
    def isField(name: String): Boolean = fields contains name

    def getSort(name: String): trees.ADTSort = sorts(name)
    def isSort(name: String): Boolean = sorts contains name

    def +(p: (String, Identifier, Type, Eventual[Type])): Store = this + (p._1, p._2, p._3, p._4)
    def +(name: String, id: Identifier, simple: Type, tpe: Eventual[Type]): Store =
      new Store(variables + (name -> ((id, simple, tpe))), types, functions, constructors, fields, sorts)

    def +(name: String, tp: trees.TypeParameter): Store =
      new Store(variables, types + (name -> tp), functions, constructors, fields, sorts)

    def +(name: String, fd: trees.FunDef): Store =
      new Store(variables, types, functions + (name -> fd), constructors, fields, sorts)
    def +(name: String, sort: trees.ADTSort, cons: trees.ADTConstructor): Store =
      new Store(variables, types, functions, constructors + (name -> ((sort, cons))), fields, sorts)
    def +(name: String, sort: trees.ADTSort, cons: trees.ADTConstructor, vd: trees.ValDef): Store =
      new Store(variables, types, functions, constructors,
        fields + (name -> (fields.getOrElse(name, Seq()) :+ ((sort, cons, vd)))), sorts)
    def +(name: String, sort: trees.ADTSort): Store =
      new Store(variables, types, functions, constructors, fields, sorts + (name -> sort))
  }

  def getIdentifier(id: ExprIR.Identifier): Identifier = id match {
    case ExprIR.IdentifierIdentifier(i) => i
    case ExprIR.IdentifierName(name) => inox.FreshIdentifier(name)
    case ExprIR.IdentifierHole(_) => throw new Error("Expression contains holes.")
  }

  object Store {
    def empty: Store = new Store(Map(), Map(), Map(), Map(), Map(), Map())
  }

  class HoleValues(args: Seq[Any]) {
    private val get: Int => Option[Any] = args.lift

    def getIdentifier(i: Int): Option[inox.Identifier] = for {
      id <- get(i)
      if id.isInstanceOf[inox.Identifier]
    } yield id.asInstanceOf[inox.Identifier]

    def getExpression(i: Int): Option[trees.Expr] = for {
      e <- get(i)
      if e.isInstanceOf[trees.Expr]
    } yield e.asInstanceOf[trees.Expr]

    def getType(i: Int): Option[trees.Type] = for {
      t <- get(i)
      if t.isInstanceOf[trees.Type]
    } yield t.asInstanceOf[trees.Type]

    def getExpressionSeq(i: Int): Option[Seq[trees.Expr]] = for {
      es <- get(i)
      if es.isInstanceOf[Iterable[_]]
      if es.asInstanceOf[Iterable[_]].forall(_.isInstanceOf[trees.Expr])
    } yield es.asInstanceOf[Iterable[trees.Expr]].toSeq

    def getTypeSeq(i: Int): Option[Seq[trees.Type]] = for {
      ts <- get(i)
      if ts.isInstanceOf[Iterable[_]]
      if ts.asInstanceOf[Iterable[_]].forall(_.isInstanceOf[trees.Type])
    } yield ts.asInstanceOf[Iterable[trees.Type]].toSeq
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
    def checkImmediate(condition: Boolean, error: => String, location: => Position): Constrained[A] = this match {
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
