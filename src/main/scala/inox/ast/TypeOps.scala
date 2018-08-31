/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

import utils.Position

import scala.reflect._
import scala.collection.immutable.HashMap

trait TypeOps {
  protected val trees: Trees
  import trees._

  protected implicit val symbols: Symbols
  import symbols._

  class TypeErrorException(msg: String, val obj: Expr, val pos: Position) extends Exception(msg)

  object TypeErrorException {
    def apply(obj: Expr, tpes: Seq[Type]): TypeErrorException =
      new TypeErrorException(
        s"""Type error: $obj, expected ${tpes.mkString(" or ")}, 
           |found ${obj.getType}
           |
           |Typing explanation:
           |${explainTyping(obj)(new PrinterOptions())}""".stripMargin, 
        obj, 
        obj.getPos
      )

    def apply(obj: Expr, tpe: Type): TypeErrorException = apply(obj, Seq(tpe))
  }

  def typeParamsOf(expr: Expr): Set[TypeParameter] = {
    exprOps.collect(e => typeOps.typeParamsOf(e.getType))(expr)
  }

  def leastUpperBound(tp1: Type, tp2: Type): Type = if (tp1 == tp2) tp1 else Untyped

  def leastUpperBound(tps: Seq[Type]): Type =
    if (tps.isEmpty) Untyped else tps.reduceLeft(leastUpperBound)

  def greatestLowerBound(tp1: Type, tp2: Type): Type = if (tp1 == tp2) tp1 else Untyped

  def greatestLowerBound(tps: Seq[Type]): Type =
    if (tps.isEmpty) Untyped else tps.reduceLeft(greatestLowerBound)

  def isSubtypeOf(t1: Type, t2: Type): Boolean = t1 == t2

  private type Instantiation = Map[TypeParameter, Type]
  def instantiation(from: Type, to: Type): Option[Instantiation] = {
    class Failure extends RuntimeException

    def unify(m1: Instantiation, m2: Instantiation): Instantiation = {
      (m1.keys.toSet ++ m2.keys).map(k => (k, m1.get(k), m2.get(k))).map {
        case (k, Some(v1), Some(v2)) if v1 == v2 => k -> v1
        case (k, Some(v1), None) => k -> v1
        case (k, None, Some(v2)) => k -> v2
        case _ => throw new Failure
      }.toMap
    }

    def rec(from: Type, to: Type): Instantiation = (from, to) match {
      case (_, Untyped) => throw new Failure
      case (Untyped, _) => throw new Failure
      case (adt: ADTType, _) if adt.lookupSort.isEmpty => throw new Failure
      case (_, adt: ADTType) if adt.lookupSort.isEmpty => throw new Failure
      case (tp: TypeParameter, _) => Map(tp -> to)
      case (adt1: ADTType, adt2: ADTType) =>
        if (adt1.id != adt2.id || adt1.tps.size != adt2.tps.size) throw new Failure
        (adt1.tps zip adt2.tps).foldLeft[Instantiation](Map.empty) {
          case (inst, (tp1, tp2)) => unify(inst, rec(tp1, tp2))
        }
      case typeOps.Same(NAryType(ts1, _), NAryType(ts2, _)) if ts1.size == ts2.size =>
        (ts1 zip ts2).foldLeft[Instantiation](Map.empty) {
          case (inst, (tp1, tp2)) => unify(inst, rec(tp1, tp2))
        }
      case _ => throw new Failure
    }

    try {
      Some(rec(from, to))
    } catch {
      case _: Failure => None
    }
  }

  def typeCheck(obj: Expr, exps: Type*) = {
    val res = exps.exists(e => isSubtypeOf(obj.getType, e))

    if (!res) {
      throw TypeErrorException(obj, exps.toList)
    }
  }

  private def flattenCardinalities(ints: Seq[Option[Int]]): Option[Seq[Int]] = {
    if (ints.forall(_.isDefined)) {
      Some(ints.map(_.get))
    } else {
      None
    }
  }

  def constructorCardinality(cons: TypedADTConstructor): Option[Int] = {
    flattenCardinalities(cons.fields.map(vd => typeCardinality(vd.getType))).map(_.product)
  }

  def typeCardinality(tp: Type): Option[Int] = tp match {
    case Untyped => Some(0)
    case BooleanType() => Some(2)
    case UnitType() => Some(1)
    // TODO BVType => 2^size
    case TupleType(tps) => flattenCardinalities(tps.map(typeCardinality)).map(_.product)
    case SetType(base) =>
      typeCardinality(base).map(b => Math.pow(2, b).toInt)
    case FunctionType(Seq(), to) => typeCardinality(to)
    case FunctionType(_, to) if typeCardinality(to) == Some(0) => Some(0)
    case MapType(from, to) =>
      for {
        t <- typeCardinality(to)
        f <- typeCardinality(from)
      } yield Math.pow(t, f).toInt
    case BagType(base) => typeCardinality(base) match {
      case Some(x) if x <= 1 => Some(1)
      case _ => None
    }
    case adt: ADTType =>
      val sort = adt.getSort
      if (sort.definition.isInductive) None
      else flattenCardinalities(sort.constructors.map(constructorCardinality)).map(_.sum)
    case _ => None
  }

  def typeDependencies(tpe: Type): Map[Type, Set[Type]] = {
    var dependencies: Map[Type, Set[Type]] = Map.empty

    def rec(tpe: Type): Unit = if (!dependencies.isDefinedAt(tpe)) {
      val next = tpe match {
        case adt: ADTType =>
          val sort = adt.getSort
          sort.constructors.flatMap(_.fields).map(_.getType)
        case NAryType(tps, _) =>
          tps
      }

      dependencies += tpe -> next.toSet
      next.foreach(rec)
    }

    rec(tpe)
    dependencies
  }
}
