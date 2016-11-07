/* Copyright 2009-2015 EPFL, Lausanne */

package inox
package solvers
package theories

trait BagEncoder extends TheoryEncoder {
  import trees._
  import trees.dsl._

  val evaluator: evaluators.DeterministicEvaluator {
    val program: sourceProgram.type
  }

  val BagID = FreshIdentifier("Bag")
  val keys = FreshIdentifier("keys")
  val f = FreshIdentifier("f")

  val bagADT = mkConstructor(BagID)("T")(None) {
    case Seq(aT) => Seq(ValDef(keys, SetType(aT)), ValDef(f, aT =>: IntegerType))
  }

  val Bag = T(BagID)

  private def get(bag: Expr, x: Expr): Expr = {
    if_ (bag.getField(keys) contains x) {
      bag.getField(f)(x)
    } else_ {
      E(BigInt(0))
    }
  }

  val GetID = FreshIdentifier("get")
  val Get = mkFunDef(GetID)("T") { case Seq(aT) => (
    Seq("bag" :: Bag(aT), "x" :: aT),
    IntegerType, { case Seq(bag, x) => get(bag, x) })
  }

  val AddID = FreshIdentifier("add")
  val Add = mkFunDef(AddID)("T") { case Seq(aT) => (
    Seq("bag" :: Bag(aT), "x" :: aT),
    Bag(aT), { case Seq(bag, x) => Bag(aT)(
      bag.getField(keys) insert x,
      \("y" :: aT)(y => get(bag, y) + {
        if_ (y === x) { E(BigInt(1)) } else_ { E(BigInt(0)) }
      }))
    })
  }

  val UnionID = FreshIdentifier("union")
  val Union = mkFunDef(UnionID)("T") { case Seq(aT) => (
    Seq("b1" :: Bag(aT), "b2" :: Bag(aT)),
    Bag(aT), { case Seq(b1, b2) => Bag(aT)(
      b1.getField(keys) ++ b2.getField(keys),
      \("y" :: aT)(y => get(b1, y) + get(b2, y)))
    })
  }

  val DifferenceID = FreshIdentifier("difference")
  val Difference = mkFunDef(DifferenceID)("T") { case Seq(aT) => (
    Seq("b1" :: Bag(aT), "b2" :: Bag(aT)),
    Bag(aT), { case Seq(b1, b2) => Bag(aT)(
      b1.getField(keys),
      \("y" :: aT)(y => let("res" :: IntegerType, get(b1, y) - get(b2, y)) {
        res => if_ (res < E(BigInt(0))) { E(BigInt(0)) } else_ { res }
      }))
    })
  }

  val IntersectID = FreshIdentifier("intersect")
  val Intersect = mkFunDef(IntersectID)("T") { case Seq(aT) => (
    Seq("b1" :: Bag(aT), "b2" :: Bag(aT)),
    Bag(aT), { case Seq(b1, b2) => Bag(aT)(
      b1.getField(keys) & b2.getField(keys),
      \("y" :: aT)(y => let("r1" :: IntegerType, get(b1, y)) { r1 =>
        let("r2" :: IntegerType, get(b2, y)) { r2 =>
          if_ (r1 > r2) { r2 } else_ { r1 }
        }
      }))
    })
  }

  val EqualsID = FreshIdentifier("equals")
  val BagEquals = mkFunDef(EqualsID)("T") { case Seq(aT) => (
    Seq("b1" :: Bag(aT), "b2" :: Bag(aT)),
    BooleanType, { case Seq(b1, b2) =>
      forall("x" :: aT) { x =>
        let("f1x" :: IntegerType, b1.getField(f)(x)) { f1x =>
          let("f2x" :: IntegerType, b2.getField(f)(x)) { f2x =>
            f1x === f2x ||
            (!(b1.getField(keys) contains x) && f2x === E(BigInt(0))) ||
            (f1x === E(BigInt(0)) && !(b2.getField(keys) contains x)) ||
            (!(b1.getField(keys) contains x) && !(b2.getField(keys) contains x))
          }
        }
      }
    })
  }

  override val extraFunctions = Seq(Get, Add, Union, Difference, Intersect, BagEquals)
  override val extraADTs = Seq(bagADT)

  protected object encoder extends SelfTreeTransformer {
    import sourceProgram._

    override def transform(e: Expr): Expr = e match {
      case FiniteBag(elems, tpe) =>
        val newTpe = transform(tpe)
        Bag(newTpe)(
          FiniteSet(elems.map(_._1), newTpe),
          \("x" :: newTpe)(x => elems.foldRight[Expr](IntegerLiteral(0).copiedFrom(e)) {
            case ((k, v), ite) => IfExpr(x === transform(k), transform(v), ite).copiedFrom(e)
          })
        ).copiedFrom(e)

      case BagAdd(bag, elem) =>
        val BagType(base) = bag.getType
        Add(transform(base))(transform(bag), transform(elem)).copiedFrom(e)

      case MultiplicityInBag(elem, bag) =>
        val BagType(base) = bag.getType
        Get(transform(base))(transform(bag), transform(elem)).copiedFrom(e)

      case BagIntersection(b1, b2) =>
        val BagType(base) = b1.getType
        Intersect(transform(base))(transform(b1), transform(b2)).copiedFrom(e)

      case BagUnion(b1, b2) =>
        val BagType(base) = b1.getType
        Union(transform(base))(transform(b1), transform(b2)).copiedFrom(e)

      case BagDifference(b1, b2) =>
        val BagType(base) = b1.getType
        Difference(transform(base))(transform(b1), transform(b2))

      case Equals(b1, b2) if b1.getType.isInstanceOf[BagType] =>
        val BagType(base) = b1.getType
        BagEquals(transform(base))(transform(b1), transform(b2)).copiedFrom(e)

      case _ => super.transform(e)
    }

    override def transform(tpe: Type): Type = tpe match {
      case BagType(base) => Bag(transform(base)).copiedFrom(tpe)
      case _ => super.transform(tpe)
    }
  }

  protected object decoder extends SelfTreeTransformer {
    import targetProgram._

    override def transform(e: Expr): Expr = e match {
      case cc @ ADT(ADTType(BagID, Seq(tpe)), Seq(FiniteSet(elems, _), l @ Lambda(Seq(_), _))) =>
        val tl = transform(l)
        FiniteBag(elems.map { e =>
          val te = transform(e)
          te -> evaluator.eval(Application(tl, Seq(te))).result.getOrElse {
            throw new Unsupported(e, "Unexpectedly failed to evaluate bag lambda")
          }.copiedFrom(e)
        }, transform(tpe)).copiedFrom(e)

      case cc @ ADT(ADTType(BagID, Seq(tpe)), args) =>
        throw new Unsupported(e, "Unexpected argument to bag constructor")

      case FunctionInvocation(AddID, Seq(_), Seq(bag, elem)) =>
        BagAdd(transform(bag), transform(elem)).copiedFrom(e)

      case FunctionInvocation(GetID, Seq(_), Seq(bag, elem)) =>
        MultiplicityInBag(transform(elem), transform(bag)).copiedFrom(e)

      case FunctionInvocation(IntersectID, Seq(_), Seq(b1, b2)) =>
        BagIntersection(transform(b1), transform(b2)).copiedFrom(e)

      case FunctionInvocation(UnionID, Seq(_), Seq(b1, b2)) =>
        BagUnion(transform(b1), transform(b2)).copiedFrom(e)

      case FunctionInvocation(DifferenceID, Seq(_), Seq(b1, b2)) =>
        BagDifference(transform(b1), transform(b2)).copiedFrom(e)

      case FunctionInvocation(EqualsID, Seq(_), Seq(b1, b2)) =>
        Equals(transform(b1), transform(b2)).copiedFrom(e)

      case _ => super.transform(e)
    }

    override def transform(tpe: Type): Type = tpe match {
      case ADTType(BagID, Seq(base)) => BagType(transform(base)).copiedFrom(tpe)
      case _ => super.transform(tpe)
    }
  }
}
