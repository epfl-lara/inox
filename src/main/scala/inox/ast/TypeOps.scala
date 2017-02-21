/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

trait TypeOps {
  protected val trees: Trees
  import trees._
  protected implicit val symbols: Symbols

  object typeOps extends {
    protected val sourceTrees: trees.type = trees
    protected val targetTrees: trees.type = trees
  } with GenTreeOps {
    type Source = trees.Type
    type Target = trees.Type
    lazy val Deconstructor = NAryType
  }

  class TypeErrorException(msg: String) extends Exception(msg)

  object TypeErrorException {
    def apply(obj: Expr, tpes: Seq[Type]): TypeErrorException =
      new TypeErrorException(s"Type error: $obj, expected ${tpes.mkString(" or ")}, found ${obj.getType}")
    def apply(obj: Expr, tpe: Type): TypeErrorException = apply(obj, Seq(tpe))
  }

  def typeParamsOf(t: Type): Set[TypeParameter] = t match {
    case tp: TypeParameter => Set(tp)
    case NAryType(subs, _) =>
      subs.flatMap(typeParamsOf).toSet
  }

  private class Unsolvable extends Exception
  protected def unsolvable = throw new Unsolvable

  /** Represents a sub-(or super if `!isUpper`)-typing constraint between
    * type parameter `tp` with bound `bound` */
  protected case class Subtyping(tp: TypeParameter, bound: Type, isUpper: Boolean)

  /** Collects the constraints that need to be solved for `instantiation_<:>`.
    * Note: this is an override point. */
  protected def instantiationConstraints(toInst: Type, bound: Type, isUpper: Boolean): Seq[Subtyping] = (toInst, bound) match {
    case (_, Untyped) => unsolvable
    case (Untyped, _) => unsolvable
    case (tp: TypeParameter, _) => Seq(Subtyping(tp, bound, isUpper))
    case (adt: ADTType, _) if adt.lookupADT.isEmpty => unsolvable
    case (_, adt: ADTType) if adt.lookupADT.isEmpty => unsolvable
    case (adt1: ADTType, adt2: ADTType) =>
      val def1 = adt1.getADT.definition
      val def2 = adt2.getADT.definition
      val (al, ah) = if (isUpper) (def1, def2) else (def2, def1)
      if (!((al == ah) || (al.root == ah))) unsolvable
      else {
        for {
          (tp, (t1, t2)) <- def1.typeArgs zip (adt1.tps zip adt2.tps)
          variance <- if (tp.isCovariant) Seq(isUpper) else if (tp.isContravariant) Seq(!isUpper) else Seq(true, false)
          constr <- instantiationConstraints(t1, t2, variance)
        } yield constr
      }

    case (FunctionType(from1, to1), FunctionType(from2, to2)) if from1.size == from2.size =>
      val in = (from1 zip from2).flatMap { case (tp1, tp2) =>
        instantiationConstraints(tp1, tp2, !isUpper) // Contravariant args
      }
      val out = instantiationConstraints(to1, to2, isUpper) // Covariant result
      in ++ out

    case (TupleType(ts1), TupleType(ts2)) if ts1.size == ts2.size =>
      (ts1 zip ts2).flatMap { case (tp1, tp2) =>
        instantiationConstraints(tp1, tp2, isUpper) // Covariant tuples
      }

    case typeOps.Same(NAryType(ts1, _), NAryType(ts2, _)) if ts1.size == ts2.size =>
      for {
        (t1, t2) <- ts1 zip ts2
        variance <- Seq(true, false)
        constr <- instantiationConstraints(t1, t2, variance)
      } yield constr

    case _ => unsolvable
  }

  /** Solves the constraints collected by [[instantiationConstraints]].
    * Note: this is an override point. */
  protected def instantiationSolution(constraints: Seq[Subtyping]): Map[TypeParameter, Type] = {
    val flattened = constraints.groupBy(_.tp)
    flattened.mapValues { cons =>
      val (supers, subs) = cons.partition(_.isUpper)
      // Lub of the variable will be the glb of its upper bounds
      val lub = leastUpperBound(subs.map(_.bound))
      // Glb of the variable will be the lub of its lower bounds
      val glb = greatestLowerBound(supers.map(_.bound))

      if (subs.isEmpty) glb        // No lower bounds
      else if (supers.isEmpty) lub // No upper bounds
      else if (isSubtypeOf(glb, lub)) lub // Both lower and upper bounds. If they are compatible, randomly return lub
      else unsolvable                     // Note: It is enough to use isSubtypeOf because lub and glb contain no type variables (of toInst)
    }.view.force
  }

  /** Produces an instantiation for a type so that it respects a type bound (upper or lower). */
  private def instantiation_<:>(toInst: Type, bound: Type, isUpper: Boolean): Option[Map[TypeParameter, Type]] = {
    try {
      Some(instantiationSolution(instantiationConstraints(toInst, bound, isUpper)))
    } catch {
      case _: Unsolvable => None
    }
  }

  /** Computes the tightest bound (upper or lower) of two types.
    * Note: this is an override point. */
  protected def typeBound(tp1: Type, tp2: Type, upper: Boolean): Type = (tp1, tp2) match {
    case (adt: ADTType, _) if adt.lookupADT.isEmpty => Untyped
    case (_, adt: ADTType) if adt.lookupADT.isEmpty => Untyped
    case (adt1: ADTType, adt2: ADTType) =>
      if (adt1.tps.size != adt2.tps.size) Untyped
      else {
        val def1 = adt1.getADT.definition
        val def2 = adt2.getADT.definition
        val an1 = Seq(def1, def1.root)
        val an2 = Seq(def2, def2.root)

        val tps = (def1.typeArgs zip (adt1.tps zip adt2.tps)).map { case (tp, (t1, t2)) =>
          if (tp.isCovariant) typeBound(t1, t2, upper)
          else if (tp.isContravariant) typeBound(t1, t2, !upper)
          else if (t1 == t2) t1
          else Untyped
        }

        val bound = if (upper) {
          // Upper bound
          (an1.reverse zip an2.reverse)
            .takeWhile(((_: ADTDefinition) == (_: ADTDefinition)).tupled)
            .lastOption.map(_._1)
        } else {
          // Lower bound
          if (an1 contains def2) Some(def1)
          else if (an2 contains def1) Some(def2)
          else None
        }

        bound.map(_.typed(tps).toType).getOrElse(Untyped).unveilUntyped
      }

    case (FunctionType(from1, to1), FunctionType(from2, to2)) =>
      if (from1.size != from2.size) Untyped
      else {
        val in = (from1 zip from2).map { case (tp1, tp2) =>
          typeBound(tp1, tp2, !upper) // Contravariant args
        }
        val out = typeBound(to1, to2, upper) // Covariant result
        FunctionType(in, out).unveilUntyped
      }

    case (TupleType(ts1), TupleType(ts2)) =>
      if (ts1.size != ts2.size) Untyped
      else {
        val ts = (ts1 zip ts2).map { case (tp1, tp2) =>
          typeBound(tp1, tp2, upper) // Covariant tuples
        }
        TupleType(ts).unveilUntyped
      }

    case (t1, t2) =>
      // Everything else is invariant
      if (t1 == t2) t1.unveilUntyped else Untyped
  }

  /** Computes the tightest bound (upper or lower) of a sequence of types */
  private def typeBound(tps: Seq[Type], upper: Boolean): Type = {
    if (tps.isEmpty) Untyped
    else tps.reduceLeft(typeBound(_, _, upper))
  }

  def leastUpperBound(tp1: Type, tp2: Type): Type =
    typeBound(tp1, tp2, true)

  def leastUpperBound(tps: Seq[Type]): Type =
    typeBound(tps, true)

  def greatestLowerBound(tp1: Type, tp2: Type): Type =
    typeBound(tp1, tp2, false)

  def greatestLowerBound(tps: Seq[Type]): Type =
    typeBound(tps, false)

  def isSubtypeOf(t1: Type, t2: Type): Boolean = {
    leastUpperBound(t1, t2) == t2
  }

  def typesCompatible(t1: Type, t2s: Type*) = {
    leastUpperBound(t1 +: t2s) != Untyped
  }

  /** Instantiates a type so that it is subtype of another type */
  def instantiation_<:(subT: Type, superT: Type) =
    instantiation_<:>(subT, superT, isUpper = true)

  /** Instantiates a type so that it is supertype of another type */
  def instantiation_>:(superT: Type, subT: Type) =
    instantiation_<:>(superT, subT, isUpper = false)

  /** Collects the constraints that need to be solved for [[unify]].
    * Note: this is an override point. */
  protected def unificationConstraints(t1: Type, t2: Type, free: Seq[TypeParameter]): List[(TypeParameter, Type)] = (t1, t2) match {
    case _ if t1 == t2 => Nil
    case (tp: TypeParameter, _) if !(typeParamsOf(t2) contains tp) && (free contains tp) => List(tp -> t2)
    case (_, tp: TypeParameter) if !(typeParamsOf(t1) contains tp) && (free contains tp) => List(tp -> t1)
    case (_: TypeParameter, _) => unsolvable
    case (_, _: TypeParameter) => unsolvable
    case (adt: ADTType, _) if adt.lookupADT.isEmpty => unsolvable
    case (_, adt: ADTType) if adt.lookupADT.isEmpty => unsolvable
    case (adt1: ADTType, adt2: ADTType) if adt1.getADT.definition == adt2.getADT.definition =>
      (adt1.tps zip adt2.tps).toList flatMap (p => unificationConstraints(p._1, p._2, free))
    case typeOps.Same(NAryType(ts1, _), NAryType(ts2, _)) if ts1.size == ts2.size =>
      (ts1 zip ts2).toList flatMap (p => unificationConstraints(p._1, p._2, free))
    case _ => unsolvable
  }

  /** Solves the constraints collected by [[unificationConstraints]].
    * Note: this is an override point. */
  protected def unificationSolution(const: List[(Type, Type)]): List[(TypeParameter, Type)] = const match {
    case Nil => Nil
    case (tp: TypeParameter, t) :: tl =>
      val replaced = tl map { case (t1, t2) =>
        (instantiateType(t1, Map(tp -> t)), instantiateType(t2, Map(tp -> t)))
      }
      (tp -> t) :: unificationSolution(replaced)
    case (adt: ADTType, _) :: tl if adt.lookupADT.isEmpty => unsolvable
    case (_, adt: ADTType) :: tl if adt.lookupADT.isEmpty => unsolvable
    case (adt1: ADTType, adt2: ADTType) :: tl if adt1.getADT.definition == adt2.getADT.definition =>
      unificationSolution((adt1.tps zip adt2.tps).toList ++ tl)
    case typeOps.Same(NAryType(ts1, _), NAryType(ts2, _)) :: tl if ts1.size == ts2.size =>
      unificationSolution((ts1 zip ts2).toList ++ tl)
    case _ =>
      unsolvable
  }

  /** Unifies two types, under a set of free variables */
  def unify(t1: Type, t2: Type, free: Seq[TypeParameter]): Option[List[(TypeParameter, Type)]] = {
    try {
      Some(unificationSolution(unificationConstraints(t1, t2, free)))
    } catch {
      case _: Unsolvable => None
    }
  }

  def instantiateType(tpe: Type, tps: Map[TypeParameter, Type]): Type = {
    if (tps.isEmpty) {
      tpe
    } else {
      typeOps.postMap {
        case tp: TypeParameter => tps.get(tp)
        case _ => None
      } (tpe)
    }
  }

  def typeCheck(obj: Expr, exps: Type*) = {
    val res = exps.exists(e => isSubtypeOf(obj.getType, e))

    if (!res) {
      throw TypeErrorException(obj, exps.toList)
    }
  }

  def bestRealType(t: Type): Type = t match {
    case (adt: ADTType) => ADTType(adt.getADT.definition.root.id, adt.tps map bestRealType)
    case NAryType(tps, builder) => builder(tps map bestRealType)
  }

  def bestRealParameters(t: Type): Type = t match {
    case ADTType(id, tps) => ADTType(id, tps map bestRealType)
    case NAryType(tps, builder) => builder(tps map bestRealType)
  }

  def isParametricType(tpe: Type): Boolean = tpe match {
    case (tp: TypeParameter) => true
    case NAryType(tps, builder) => tps.exists(isParametricType)
  }

  def typeCardinality(tp: Type): Option[Int] = {
    def cards(tps: Seq[Type]): Option[Seq[Int]] = {
      val cardinalities = tps.flatMap(typeCardinality)
      if (cardinalities.size == tps.size) {
        Some(cardinalities)
      } else {
        None
      }
    }

    tp match {
      case Untyped => Some(0)
      case BooleanType => Some(2)
      case UnitType => Some(1)
      case TupleType(tps) => cards(tps).map(_.product)
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
      case adt: ADTType => adt.getADT match {
        case tcons: TypedADTConstructor =>
          cards(tcons.fieldsTypes).map(_.product)

        case tsort: TypedADTSort =>
          if (tsort.definition.isInductive) None else {
            cards(tsort.constructors.map(_.toType)).map(_.sum)
          }
      }
      case _ => None
    }
  }

  def typeDependencies(tpe: Type): Map[Type, Set[Type]] = {
    var dependencies: Map[Type, Set[Type]] = Map.empty

    def rec(tpe: Type): Unit = if (!dependencies.isDefinedAt(tpe)) {
      val next = tpe match {
        case adt: ADTType => adt.getADT match {
          case tsort: TypedADTSort =>
            tsort.constructors.map(_.toType)
          case tcons: TypedADTConstructor =>
            tcons.fieldsTypes ++ tcons.sort.map(_.toType)
        }
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
