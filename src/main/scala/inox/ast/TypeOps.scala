/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

import utils.Position

import scala.reflect._
import scala.collection.immutable.HashMap

trait TypeOps {
  protected val trees: Trees
  import trees._

  protected val symbols: Symbols
  import symbols.{given, _}

  class TypeErrorException(msg: String, val obj: Expr, val pos: Position) extends Exception(msg)

  object TypeErrorException {
    def apply(obj: Expr, tpes: Seq[Type]): TypeErrorException =
      new TypeErrorException(
        s"""Type error: $obj, expected ${tpes.mkString(" or ")},
           |found ${obj.getType}
           |
           |Typing explanation:
           |${symbols.explainTyping(obj)(using new PrinterOptions())}""".stripMargin,
        obj,
        obj.getPos
      )

    def apply(obj: Expr, tpe: Type): TypeErrorException = apply(obj, Seq(tpe))
  }

  def leastUpperBound(tp1: Type, tp2: Type): Type = bound(tp1, tp2, lower = false)

  def leastUpperBound(tps: Seq[Type]): Type =
    if (tps.isEmpty) Untyped else tps.reduceLeft(leastUpperBound)

  def greatestLowerBound(tp1: Type, tp2: Type): Type = bound(tp1, tp2, lower = true)

  def greatestLowerBound(tps: Seq[Type]): Type =
    if (tps.isEmpty) Untyped else tps.reduceLeft(greatestLowerBound)

  private def bound(tp1: Type, tp2: Type, lower: Boolean): Type =
    (tp1, tp2) match
      case (RefinementType(vd1, p1), RefinementType(vd2, p2)) =>
        val underlying = bound(vd1.getType, vd2.getType, lower)
        // express both predicates over the binder of the first refinement
        val p2v1 = exprOps.replaceFromSymbols(Map(vd2 -> vd1.toVariable), p2)
        val joinedProp = if (p1 == p2v1) p1 else if (lower) And(Seq(p1, p2v1)) else Or(Seq(p1, p2v1))
        if (underlying == Untyped) Untyped else RefinementType(vd1.copy(tpe = underlying), joinedProp)
      case (_, RefinementType(vd, prop)) if lower =>
        val underlying = bound(tp1, vd.getType, lower)
        if (underlying == Untyped) Untyped else RefinementType(vd.copy(tpe = underlying), prop)
      case (RefinementType(vd, prop), _) if lower =>
        val underlying = bound(vd.getType, tp2, lower)
        if (underlying == Untyped) Untyped else RefinementType(vd.copy(tpe = underlying), prop)
      case (_, RefinementType(vd, _)) => bound(tp1, vd.getType, lower)
      case (RefinementType(vd, _), _) => bound(vd.getType, tp2, lower)
      case (adt1: ADTType, adt2: ADTType) if adt1.id == adt2.id && adt1.tps.size == adt2.tps.size =>
        val underlying = (adt1.tps zip adt2.tps).map { case (tp1, tp2) => bound(tp1, tp2, lower) }
        if (underlying.exists(_ == Untyped)) Untyped else ADTType(adt1.id, underlying)
      case (SetType(base1), SetType(base2)) => 
        val underlying = bound(base1, base2, lower)
        if (underlying == Untyped) Untyped else SetType(underlying)
      case (FunctionType(from1, to1), FunctionType(from2, to2)) if from1.size == from2.size =>
        val from = (from1 zip from2).map { case (tp1, tp2) => bound(tp2, tp1, !lower) }
        val to = bound(to1, to2, lower)
        if (from.exists(_ == Untyped) || to == Untyped) Untyped else FunctionType(from, to)
      case (MapType(from1, to1), MapType(from2, to2)) =>
        val from = bound(from1, from2, !lower)
        val to = bound(to1, to2, lower)
        if (from == Untyped || to == Untyped) Untyped else MapType(from, to)
      case (BagType(base1), BagType(base2)) => 
        val underlying = bound(base1, base2, lower)
        if (underlying == Untyped) Untyped else BagType(underlying)
      case (t1, t2) if t1 == t2 => t1
      case _ => Untyped

  def isSubtypeOf(t1: Type, t2: Type): Boolean = 
    t1.getType == Untyped || t2.getType == Untyped || t1.getType == t2.getType

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
      // `from` has no refinements (see below), so its components match the base types of `to`'s,
      // or their erasures when they depend on the bound variables
      case (_, RefinementType(vd, _)) => rec(from, vd.tpe)
      case (TupleType(tps), SigmaType(params, elem)) if tps.size == params.size + 1 =>
        recDependent(tps, params, params.map(_.tpe) :+ elem)
      case (FunctionType(args, res), PiType(params, piRes)) if args.size == params.size =>
        recDependent(args :+ res, params, params.map(_.tpe) :+ piRes)
      case typeOps.Same(NAryType(ts1, _), NAryType(ts2, _)) if ts1.size == ts2.size =>
        (ts1 zip ts2).foldLeft[Instantiation](Map.empty) {
          case (inst, (tp1, tp2)) => unify(inst, rec(tp1, tp2))
        }
      case _ => throw new Failure
    }

    def recDependent(froms: Seq[Type], params: Seq[ValDef], tos: Seq[Type]): Instantiation = {
      val vars = params.map(_.toVariable).toSet
      (froms zip tos).foldLeft[Instantiation](Map.empty) { case (inst, (tp1, tp2)) =>
        unify(inst, rec(tp1, if ((typeOps.variablesOf(tp2) & vars).nonEmpty) tp2.getType else tp2))
      }
    }

    try {
      // The refinements of `from` don't constrain the instantiation
      Some(rec(from.getType, to))
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

  // cardinalities that don't fit in an Int are unknown
  private def checkedCardinality(c: BigInt): Option[Int] = if (c.isValidInt) Some(c.toInt) else None

  private def productCardinality(ints: Seq[Option[Int]]): Option[Int] =
    flattenCardinalities(ints).flatMap(cs => checkedCardinality(cs.map(BigInt(_)).product))

  private def powerCardinality(base: Int, exponent: Int): Option[Int] =
    if (base <= 1 || exponent == 0) Some(if (exponent == 0) 1 else base)
    else if (exponent >= 32) None
    else checkedCardinality(BigInt(base).pow(exponent))

  def constructorCardinality(cons: TypedADTConstructor): Option[Int] = {
    productCardinality(cons.fields.map(vd => typeCardinality(vd.getType)))
  }

  def typeCardinality(tp: Type): Option[Int] = tp match {
    case Untyped => Some(0)
    case BooleanType() => Some(2)
    case UnitType() => Some(1)
    // TODO BVType => 2^size
    case TupleType(tps) => productCardinality(tps.map(typeCardinality))
    case SetType(base) =>
      typeCardinality(base).flatMap(b => powerCardinality(2, b))
    case FunctionType(Seq(), to) => typeCardinality(to)
    case FunctionType(_, to) if typeCardinality(to) == Some(0) => Some(0)
    case MapType(from, to) =>
      for {
        t <- typeCardinality(to)
        f <- typeCardinality(from)
        c <- powerCardinality(t, f)
      } yield c
    // a bag can hold each of its elements any number of times
    case BagType(base) => typeCardinality(base) match {
      case Some(0) => Some(1)
      case _ => None
    }
    case adt: ADTType =>
      val sort = adt.getSort
      if (sort.definition.isInductive) None
      else flattenCardinalities(sort.constructors.map(constructorCardinality))
        .flatMap(cs => checkedCardinality(cs.map(BigInt(_)).sum))
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
