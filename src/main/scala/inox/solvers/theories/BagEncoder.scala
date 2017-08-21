/* Copyright 2009-2015 EPFL, Lausanne */

package inox
package solvers
package theories

import evaluators._

trait BagEncoder extends SimpleEncoder {
  import trees.{forall => _, _}
  import trees.dsl._

  val evaluator: DeterministicEvaluator {
    val program: sourceProgram.type
  }

  val BagID = FreshIdentifier("Bag")
  val SumID = FreshIdentifier("Sum")
  val ElemID = FreshIdentifier("Elem")
  val LeafID = FreshIdentifier("Leaf")

  val left = FreshIdentifier("left")
  val right = FreshIdentifier("right")
  val key = FreshIdentifier("key")
  val value = FreshIdentifier("value")

  val Bag = T(BagID)
  val Sum = T(SumID)
  val Elem = T(ElemID)
  val Leaf = T(LeafID)

  val GetID = FreshIdentifier("get")
  val Get = mkFunDef(GetID)("T") { case Seq(aT) => (
    Seq("bag" :: Bag(aT), "x" :: aT), IntegerType, {
      case Seq(bag, x) => if_ (bag.isInstOf(Sum(aT))) {
        E(GetID)(aT)(bag.asInstOf(Sum(aT)).getField(left), x) +
          E(GetID)(aT)(bag.asInstOf(Sum(aT)).getField(right), x)
      } else_ {
        if_ (bag.isInstOf(Elem(aT)) && bag.asInstOf(Elem(aT)).getField(key) === x) {
          bag.asInstOf(Elem(aT)).getField(value)
        } else_ {
          E(BigInt(0))
        }
      }
    })
  }

  val AddID = FreshIdentifier("add")
  val Add = mkFunDef(AddID)("T") { case Seq(aT) => (
    Seq("bag" :: Bag(aT), "x" :: aT), Bag(aT), { case Seq(bag, x) => Sum(aT)(bag, Elem(aT)(x, E(BigInt(1)))) })
  }

  val UnionID = FreshIdentifier("union")
  val Union = mkFunDef(UnionID)("T") { case Seq(aT) => (
    Seq("b1" :: Bag(aT), "b2" :: Bag(aT)), Bag(aT), { case Seq(b1, b2) => Sum(aT)(b1, b2) })
  }

  val diff = FreshIdentifier("diffImpl")
  val DifferenceImpl = mkFunDef(diff)("T") { case Seq(aT) => (
    Seq("keys" :: Bag(aT), "b1" :: Bag(aT), "b2" :: Bag(aT)), Bag(aT), {
      case Seq(keys, b1, b2) => if_ (keys.isInstOf(Sum(aT))) {
        Sum(aT)(E(diff)(aT)(keys.asInstOf(Sum(aT)).getField(left), b1, b2),
          E(diff)(aT)(keys.asInstOf(Sum(aT)).getField(right), b1, b2))
      } else_ {
        if_ (keys.isInstOf(Elem(aT))) {
          let("f" :: aT, keys.asInstOf(Elem(aT)).getField(key)) { f =>
            let("d" :: IntegerType, Get(aT)(b1, f) - Get(aT)(b2, f)) { d =>
              if_ (d < E(BigInt(0))) { Leaf(aT)() } else_ { Elem(aT)(f, d) }
            }
          }
        } else_ {
          Leaf(aT)()
        }
      }
    })
  }

  val DifferenceID = FreshIdentifier("difference")
  val Difference = mkFunDef(DifferenceID)("T") { case Seq(aT) => (
    Seq("b1" :: Bag(aT), "b2" :: Bag(aT)), Bag(aT), { case Seq(b1, b2) => E(diff)(aT)(b1, b1, b2) })
  }

  val inter = FreshIdentifier("interImpl")
  val IntersectImpl = mkFunDef(inter)("T") { case Seq(aT) => (
    Seq("keys" :: Bag(aT), "b1" :: Bag(aT), "b2" :: Bag(aT)), Bag(aT), {
      case Seq(keys, b1, b2) => if_ (keys.isInstOf(Sum(aT))) {
        Sum(aT)(E(inter)(aT)(keys.asInstOf(Sum(aT)).getField(left), b1, b2),
          E(inter)(aT)(keys.asInstOf(Sum(aT)).getField(right), b1, b2))
      } else_ {
        if_ (keys.isInstOf(Elem(aT))) {
          let("f" :: aT, keys.asInstOf(Elem(aT)).getField(key)) { f =>
            let("v1" :: IntegerType, Get(aT)(b1, f)) { v1 =>
              let("v2" :: IntegerType, Get(aT)(b2, f)) { v2 =>
                Elem(aT)(f, if_ (v1 <= v2) { v1 } else_ { v2 })
              }
            }
          }
        } else_ {
          Leaf(aT)()
        }
      }
    })
  }

  val IntersectID = FreshIdentifier("intersect")
  val Intersect = mkFunDef(IntersectID)("T") { case Seq(aT) => (
    Seq("b1" :: Bag(aT), "b2" :: Bag(aT)), Bag(aT), { case Seq(b1, b2) => E(inter)(aT)(b1, b1, b2) })
  }

  val EqualsID = FreshIdentifier("equals")
  val BagEquals = mkFunDef(EqualsID)("T") { case Seq(aT) => (
    Seq("b1" :: Bag(aT), "b2" :: Bag(aT)), BooleanType, {
      case Seq(b1, b2) => forall("x" :: aT)(x => Get(aT)(b1, x) === Get(aT)(b2, x))
    })
  }

  val InvID = FreshIdentifier("inv")
  val BagInvariant = mkFunDef(InvID)("T") { case Seq(aT) => (
    Seq("bag" :: Bag(aT)), BooleanType, {
      case Seq(bag) => if_ (bag.isInstOf(Elem(aT))) {
        bag.asInstOf(Elem(aT)).getField(value) >= E(BigInt(0))
      } else_ {
        E(true)
      }
    })
  }

  val bagADT = mkSort(BagID, HasADTEquality(EqualsID), HasADTInvariant(InvID))("T")(Seq(SumID, ElemID, LeafID))

  val sumADT = mkConstructor(SumID)("T")(Some(BagID)) {
    case Seq(aT) => Seq(ValDef(left, Bag(aT)), ValDef(right, Bag(aT)))
  }

  val elemADT = mkConstructor(ElemID)("T")(Some(BagID)) {
    case Seq(aT) => Seq(ValDef(key, aT), ValDef(value, IntegerType))
  }

  val leafADT = mkConstructor(LeafID)("T")(Some(BagID))(_ => Seq.empty)


  override val extraFunctions =
    Seq(Get, Add, Union, DifferenceImpl, Difference, IntersectImpl, Intersect, BagEquals, BagInvariant)

  override val extraADTs =
    Seq(bagADT, sumADT, elemADT, leafADT)


  protected object encoder extends SelfTreeTransformer {
    import sourceProgram._
    import evaluator.context._

    override def transform(e: Expr): Expr = e match {
      case FiniteBag(elems, tpe) =>
        val newTpe = transform(tpe)
        val newElems = elems.map(p => transform(p._1) -> transform(p._2))
        newElems.foldRight((Leaf(newTpe)(): Expr, Seq[Expr]())) {
          case ((key, value), (acc, elems)) => (IfExpr(
            orJoin(elems.map(e => Equals(e, key))),
            acc,
            Sum(newTpe)(acc, Elem(newTpe)(key, value))
          ), key +: elems)
        }._1

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
        Difference(transform(base))(transform(b1), transform(b2)).copiedFrom(e)

      case _ => super.transform(e)
    }

    override def transform(tpe: Type): Type = tpe match {
      case BagType(base) => Bag(transform(base)).copiedFrom(tpe)
      case _ => super.transform(tpe)
    }
  }

  protected object decoder extends SelfTreeTransformer {
    import targetProgram._
    import evaluator.context._

    override def transform(e: Expr): Expr = e match {
      case ADT(ADTType(SumID, Seq(tpe)), Seq(e1, e2)) =>
        val fb1 @ FiniteBag(els1, _) = transform(e1)
        val fb2 @ FiniteBag(els2, _) = transform(e2)

        if (exprOps.variablesOf(fb1).isEmpty && exprOps.variablesOf(fb2).isEmpty) {
          def groundMap(els: Seq[(Expr, Expr)]): Map[Expr, Expr] = els.map { case (key, value) => (
            evaluator.eval(key).result.getOrElse(throw new Unsupported(e, "Failed to evaluate bag contents")),
            evaluator.eval(value).result.getOrElse(throw new Unsupported(e, "Failed to evaluate bag contents"))
          )}.toMap

          val map1 = groundMap(els1)
          val map2 = groundMap(els2)

          FiniteBag((map1.keySet ++ map2.keySet).map { key =>
            val IntegerLiteral(i1) = map1.getOrElse(key, IntegerLiteral(0))
            val IntegerLiteral(i2) = map2.getOrElse(key, IntegerLiteral(0))
            key -> IntegerLiteral(i1 + i2)
          }.toSeq, transform(tpe)).copiedFrom(e)
        } else {
          FiniteBag(els1 ++ els2, transform(tpe)).copiedFrom(e)
        }

      case ADT(ADTType(ElemID, Seq(tpe)), Seq(key, value)) =>
        FiniteBag(Seq(transform(key) -> transform(value)), transform(tpe)).copiedFrom(e)

      case ADT(ADTType(LeafID, Seq(tpe)), Seq()) =>
        FiniteBag(Seq.empty, transform(tpe)).copiedFrom(e)

      case FunctionInvocation(AddID, _, Seq(bag, elem)) =>
        BagAdd(transform(bag), transform(elem)).copiedFrom(e)

      case FunctionInvocation(GetID, _, Seq(bag, elem)) =>
        MultiplicityInBag(transform(elem), transform(bag)).copiedFrom(e)

      case FunctionInvocation(IntersectID, _, Seq(b1, b2)) =>
        BagIntersection(transform(b1), transform(b2)).copiedFrom(e)

      case FunctionInvocation(UnionID, _, Seq(b1, b2)) =>
        BagUnion(transform(b1), transform(b2)).copiedFrom(e)

      case FunctionInvocation(DifferenceID, _, Seq(b1, b2)) =>
        BagDifference(transform(b1), transform(b2)).copiedFrom(e)

      case _ => super.transform(e)
    }

    override def transform(tpe: Type): Type = tpe match {
      case ADTType(BagID | SumID | ElemID | LeafID, Seq(base)) => BagType(transform(base)).copiedFrom(tpe)
      case _ => super.transform(tpe)
    }
  }
}

object BagEncoder {
  def apply(enc: ast.ProgramTransformer)
           (ev: DeterministicEvaluator { val program: enc.sourceProgram.type }):
           BagEncoder { val sourceProgram: enc.targetProgram.type } = new {
    val sourceProgram: enc.targetProgram.type = enc.targetProgram
    val evaluator = ReverseEvaluator(enc)(ev)
  } with BagEncoder
}
