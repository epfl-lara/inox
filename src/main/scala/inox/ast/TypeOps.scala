/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

trait TypeOps {
  private[ast] val trees: Trees
  import trees._
  implicit val symbols: Symbols

  object typeOps extends GenTreeOps {
    val trees: TypeOps.this.trees.type = TypeOps.this.trees
    import trees._

    type SubTree = Type
    val Deconstructor = NAryType
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

  /** Generic type bounds between two types. Serves as a base for a set of subtyping/unification functions.
    * It will allow subtyping between classes (but type parameters are invariant).
    * It will also allow a set of free parameters to be unified if needed.
    *
    * @param allowSub Allow subtyping for class types
    * @param freeParams The unifiable type parameters
    * @param isLub Whether the bound calculated is the LUB
    * @return An optional pair of (type, map) where type the resulting type bound
    *         (with type parameters instantiated as needed)
    *         and map the assignment of type variables.
    *         Result is empty if types are incompatible.
    * @see [[leastUpperBound]], [[greatestLowerBound]], [[isSubtypeOf]], [[typesCompatible]], [[unify]]
    */
  def typeBound(t1: Type, t2: Type, isLub: Boolean, allowSub: Boolean)
               (implicit freeParams: Seq[TypeParameter]): Option[(Type, Map[TypeParameter, Type])] = {

    def flatten(res: Seq[Option[(Type, Map[TypeParameter, Type])]]): Option[(Seq[Type], Map[TypeParameter, Type])] = {
      val (tps, subst) = res.map(_.getOrElse(return None)).unzip
      val flat = subst.flatMap(_.toSeq).groupBy(_._1)
      Some((tps, flat.mapValues { vs =>
        vs.map(_._2).distinct match {
          case Seq(unique) => unique
          case _ => return None
        }
      }))
    }

    (t1, t2) match {
      case (_: TypeParameter, _: TypeParameter) if t1 == t2 =>
        Some((t1, Map()))

      case (t, tp1: TypeParameter) if (freeParams contains tp1) && !(typeParamsOf(t) contains tp1) =>
        Some((t, Map(tp1 -> t)))

      case (tp1: TypeParameter, t) if (freeParams contains tp1) && !(typeParamsOf(t) contains tp1) =>
        Some((t, Map(tp1 -> t)))

      case (_: TypeParameter, _) =>
        None

      case (_, _: TypeParameter) =>
        None

      case (ct1: ClassType, ct2: ClassType) =>
        val cd1 = ct1.tcd.cd
        val cd2 = ct2.tcd.cd
        val bound: Option[ClassDef] = if (allowSub) {
          val an1 = Seq(cd1, cd1.root)
          val an2 = Seq(cd2, cd2.root)
          if (isLub) {
            (an1.reverse zip an2.reverse)
              .takeWhile(((_: ClassDef) == (_: ClassDef)).tupled)
              .lastOption.map(_._1)
          } else {
            // Lower bound
            if(an1.contains(cd2)) Some(cd1)
            else if (an2.contains(cd1)) Some(cd2)
            else None
          }
        } else {
          (cd1 == cd2).option(cd1)
        }
        for {
          cd <- bound
          (subs, map) <- flatten((ct1.tps zip ct2.tps).map { case (tp1, tp2) =>
            // Class types are invariant!
            typeBound(tp1, tp2, isLub, allowSub = false)
          })
        } yield (cd.typed(subs).toType, map)

      case (FunctionType(from1, to1), FunctionType(from2, to2)) =>
        if (from1.size != from2.size) None
        else {
          val in = (from1 zip from2).map { case (tp1, tp2) =>
            typeBound(tp1, tp2, !isLub, allowSub) // Contravariant args
          }
          val out = typeBound(to1, to2, isLub, allowSub) // Covariant result
          flatten(out +: in) map {
            case (Seq(newTo, newFrom@_*), map) =>
              (FunctionType(newFrom, newTo), map)
          }
        }

      case typeOps.Same(t1, t2) =>
        // Only tuples are covariant
        def allowVariance = t1 match {
          case _ : TupleType => true
          case _ => false
        }
        val NAryType(ts1, recon) = t1
        val NAryType(ts2, _) = t2
        if (ts1.size == ts2.size) {
          flatten((ts1 zip ts2).map { case (tp1, tp2) =>
            typeBound(tp1, tp2, isLub, allowSub = allowVariance)
          }).map { case (subs, map) => (recon(subs), map) }
        } else None

      case _ =>
        None
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

  def unify(tp1: Type, tp2: Type, freeParams: Seq[TypeParameter]) =
    typeBound(tp1, tp2, isLub = true, allowSub = false)(freeParams).map(_._2)

  /** Will try to instantiate subT and superT so that subT <: superT
    *
    * @return Mapping of instantiations
    */
  private def subtypingInstantiation(subT: Type, superT: Type, free: Seq[TypeParameter]) =
    typeBound(subT, superT, isLub = true, allowSub = true)(free) collect {
      case (tp, map) if instantiateType(superT, map) == tp => map
    }

  def canBeSubtypeOf(subT: Type, superT: Type) = {
    subtypingInstantiation(subT, superT, (typeParamsOf(subT) -- typeParamsOf(superT)).toSeq)
  }

  def canBeSupertypeOf(superT: Type, subT: Type) = {
    subtypingInstantiation(subT, superT, (typeParamsOf(superT) -- typeParamsOf(subT)).toSeq)
  }

  def leastUpperBound(tp1: Type, tp2: Type): Option[Type] =
    typeBound(tp1, tp2, isLub = true, allowSub = true)(Seq()).map(_._1)

  def greatestLowerBound(tp1: Type, tp2: Type): Option[Type] =
    typeBound(tp1, tp2, isLub = false, allowSub = true)(Seq()).map(_._1)

  def leastUpperBound(ts: Seq[Type]): Option[Type] = {
    def olub(ot1: Option[Type], t2: Option[Type]): Option[Type] = ot1 match {
      case Some(t1) => leastUpperBound(t1, t2.get)
      case None => None
    }

    if (ts.isEmpty) {
      None
    } else {
      ts.map(Some(_)).reduceLeft(olub)
    }
  }

  def isSubtypeOf(t1: Type, t2: Type): Boolean = {
    leastUpperBound(t1, t2) == Some(t2)
  }

  def typesCompatible(t1: Type, t2s: Type*) = {
    leastUpperBound(t1 +: t2s).isDefined
  }

  def typeCheck(obj: Expr, exps: Type*) {
    val res = exps.exists(e => isSubtypeOf(obj.getType, e))

    if (!res) {
      throw TypeErrorException(obj, exps.toList)
    }
  }

  def bestRealType(t: Type): Type = t match {
    case (c: ClassType) => c.tcd.root.toType
    case NAryType(tps, builder) => builder(tps.map(bestRealType))
  }

  def isParametricType(tpe: Type): Boolean = tpe match {
    case (tp: TypeParameter) => true
    case NAryType(tps, builder) => tps.exists(isParametricType)
  }

  def typeCardinality(tp: Type): Option[Int] = {
    def cards(tps: Seq[Type]): Option[Seq[Int]] = {
      val cardinalities = tps.map(typeCardinality).flatten
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
      case FunctionType(from, to) =>
        for {
          t <- typeCardinality(to)
          f <- cards(from).map(_.product)
        } yield Math.pow(t, f).toInt
      case MapType(from, to) =>
        for {
          t <- typeCardinality(to)
          f <- typeCardinality(from)
        } yield Math.pow(t + 1, f).toInt
      case ct: ClassType => ct.tcd match {
        case tccd: TypedCaseClassDef =>
          cards(tccd.fieldsTypes).map(_.product)

        case accd: TypedAbstractClassDef =>
          val possibleChildTypes = utils.fixpoint((tpes: Set[Type]) => {
            tpes.flatMap(tpe => 
              Set(tpe) ++ (tpe match {
                case ct: ClassType => ct.tcd match {
                  case tccd: TypedCaseClassDef => tccd.fieldsTypes
                  case tacd: TypedAbstractClassDef => (Set(tacd) ++ tacd.descendants).map(_.toType)
                }
                case _ => Set.empty
              })
            )
          })(accd.descendants.map(_.toType).toSet)

          if (possibleChildTypes(accd.toType)) {
            None
          } else {
            cards(accd.descendants.map(_.toType)).map(_.sum)
          }
      }
      case _ => None
    }
  }

}
