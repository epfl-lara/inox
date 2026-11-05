/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package theories

import evaluators._

class BagEncoder private
  (val enc: transformers.ProgramTransformer)
  (override val sourceProgram: enc.targetProgram.type)
  (evaluator: DeterministicEvaluator {
    val program: sourceProgram.type
  })
  (theory: BagTheory[sourceProgram.trees.type])
  extends SimpleEncoder(
    sourceProgram,
    bagEnc(sourceProgram)(theory)(evaluator).asInstanceOf,
    bagDec(sourceProgram)(theory)(evaluator).asInstanceOf,
    theory.extraFunctions,
    theory.extraSorts)

private class BagTheory[Trees <: ast.Trees](val trees: Trees) {
  import trees._
  import trees.dsl._

  val BagID  = FreshIdentifier("Bag")
  val SumID  = FreshIdentifier("Sum")
  val ElemID = FreshIdentifier("Elem")
  val LeafID = FreshIdentifier("Leaf")

  val left  = FreshIdentifier("left")
  val right = FreshIdentifier("right")
  val key   = FreshIdentifier("key")
  val value = FreshIdentifier("value")

  val Bag  = T(BagID)
  val Sum  = C(SumID)
  val Elem = C(ElemID)
  val Leaf = C(LeafID)

  val GetID = FreshIdentifier("get")
  val Get = mkFunDef(GetID)("T") { case Seq(aT) => (
    Seq("bag" :: Bag(aT), "x" :: aT), IntegerType(), {
    case Seq(bag, x) => if_ (bag `is` SumID) {
      E(GetID)(aT)(bag.getField(left), x) +
        E(GetID)(aT)(bag.getField(right), x)
    } else_ {
      if_ (bag.is(ElemID) && bag.getField(key) === x) {
        bag.getField(value)
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

  // Note that a key can occur in several `Elem` nodes of the same bag (e.g. after
  // repeated `BagAdd`s), so difference and intersection cannot simply compute the
  // resulting multiplicity once per `Elem` node. Instead, we traverse the first bag
  // while accumulating the part `seen` of it that precedes the current node. An
  // `Elem(x, v)` node with `p = get(seen, x)` and `m = get(b2, x)` contributes
  //   max(0, p + v - m) - max(0, p - m)  to the difference, and
  //   min(p + v, m) - min(p, m)          to the intersection,
  // which add up over all nodes of key `x` to `max(0, get(b1, x) - m)` and
  // `min(get(b1, x), m)` respectively. Unlike computing differences of the second
  // bag along the way, this only ever calls `get` on subterms of `b1` and `b2`,
  // which keeps the number of function unfoldings quadratic instead of exponential.
  private def mkSetOperation(id: Identifier, auxId: Identifier)
                            (contribution: (Expr, Expr, Expr) => Expr): (FunDef, FunDef) = {
    val aux = mkFunDef(auxId)("T") { case Seq(aT) => (
      Seq("b1" :: Bag(aT), "b2" :: Bag(aT), "seen" :: Bag(aT)), Bag(aT), {
      case Seq(b1, b2, seen) => if_ (b1 `is` SumID) {
        Sum(aT)(E(auxId)(aT)(b1.getField(left), b2, seen),
          E(auxId)(aT)(b1.getField(right), b2, Sum(aT)(seen, b1.getField(left))))
      } else_ {
        if_ (b1 `is` ElemID) {
          let("f" :: aT, b1.getField(key)) { f =>
            let("p" :: IntegerType(), E(GetID)(aT)(seen, f)) { p =>
              let("m" :: IntegerType(), E(GetID)(aT)(b2, f)) { m =>
                let("c" :: IntegerType(), contribution(p, b1.getField(value), m)) { c =>
                  if_ (c <= E(BigInt(0))) { Leaf(aT)() } else_ { Elem(aT)(f, c) }
                }
              }
            }
          }
        } else_ {
          Leaf(aT)()
        }
      }
    })
    }

    val fd = mkFunDef(id)("T") { case Seq(aT) => (
      Seq("b1" :: Bag(aT), "b2" :: Bag(aT)), Bag(aT), {
      case Seq(b1, b2) => E(auxId)(aT)(b1, b2, Leaf(aT)())
    })
    }

    (fd, aux)
  }

  private def max0(e: Expr): Expr = if_ (e <= E(BigInt(0))) { E(BigInt(0)) } else_ { e }
  private def min(e1: Expr, e2: Expr): Expr = if_ (e1 <= e2) { e1 } else_ { e2 }

  val DifferenceID = FreshIdentifier("difference")
  val DifferenceAuxID = FreshIdentifier("differenceAux")
  private val difference = mkSetOperation(DifferenceID, DifferenceAuxID) {
    (p, v, m) => max0(p + v - m) - max0(p - m)
  }
  val Difference = difference._1
  val DifferenceAux = difference._2

  val IntersectID = FreshIdentifier("intersect")
  val IntersectAuxID = FreshIdentifier("intersectAux")
  private val intersect = mkSetOperation(IntersectID, IntersectAuxID) {
    (p, v, m) => min(p + v, m) - min(p, m)
  }
  val Intersect = intersect._1
  val IntersectAux = intersect._2

  val EqualsID = FreshIdentifier("equals")
  val BagEquals = mkFunDef(EqualsID)("T") { case Seq(aT) => (
    Seq("b1" :: Bag(aT), "b2" :: Bag(aT)), BooleanType(), {
    case Seq(b1, b2) => forall("x" :: aT)(x => Get(aT)(b1, x) === Get(aT)(b2, x))
  })
  }

  val InvID = FreshIdentifier("inv")
  val BagInvariant = mkFunDef(InvID)("T") { case Seq(aT) => (
    Seq("bag" :: Bag(aT)), BooleanType(), {
    case Seq(bag) => if_ (bag `is` ElemID) {
      bag.getField(value) >= E(BigInt(0))
    } else_ {
      E(true)
    }
  })
  }

  val bagSort = mkSort(BagID, HasADTEquality(EqualsID), HasADTInvariant(InvID))("T") {
    case Seq(aT) => Seq(
      (SumID, Seq(ValDef(left, Bag(aT)), ValDef(right, Bag(aT)))),
      (ElemID, Seq(ValDef(key, aT), ValDef(value, IntegerType()))),
      (LeafID, Seq())
    )
  }

  val extraFunctions =
    Seq(Get, Add, Union, Difference, DifferenceAux, Intersect, IntersectAux, BagEquals, BagInvariant)

  val extraSorts = Seq(bagSort)
}

def bagEnc(sourceProgram: Program)
          (theory: BagTheory[sourceProgram.trees.type])
          (evaluator: DeterministicEvaluator { val program: sourceProgram.type }): transformers.TreeTransformer { val s: sourceProgram.trees.type; val t: sourceProgram.trees.type } = {
  class BagEnc extends sourceProgram.trees.ConcreteSelfTreeTransformer {
    import theory._
    import theory.trees._
    import theory.trees.dsl._
    import sourceProgram._
    import sourceProgram.symbols.{given, _}
    import evaluator.context._

    override def transform(e: Expr): Expr = e match {
      case FiniteBag(elems, tpe) =>
        val newTpe = transform(tpe)
        val newElems = elems.map(p => transform(p._1) -> transform(p._2))
        // Later occurrences of a key override earlier ones and entries with
        // non-positive multiplicities do not belong to the bag (as in the evaluator).
        def elem(key: Expr, value: Expr): Expr = value match {
          case IntegerLiteral(i) if i > 0 => Elem(newTpe)(key, value)
          case IntegerLiteral(_) => Leaf(newTpe)()
          case _ => IfExpr(GreaterThan(value, IntegerLiteral(0)), Elem(newTpe)(key, value), Leaf(newTpe)())
        }

        newElems.foldRight((Leaf(newTpe)(): Expr, Seq[Expr]())) {
          case ((key, value), (acc, elems)) => (IfExpr(
            orJoin(elems.map(e => Equals(e, key))),
            acc,
            Sum(newTpe)(acc, elem(key, value))
          ), key +: elems)
        }._1

      case BagAdd(bag, elem) =>
        val BagType(base) = bag.getType: @unchecked
        Add(transform(base))(transform(bag), transform(elem)).copiedFrom(e)

      case MultiplicityInBag(elem, bag) =>
        val BagType(base) = bag.getType: @unchecked
        Get(transform(base))(transform(bag), transform(elem)).copiedFrom(e)

      case BagIntersection(b1, b2) =>
        val BagType(base) = b1.getType: @unchecked
        Intersect(transform(base))(transform(b1), transform(b2)).copiedFrom(e)

      case BagUnion(b1, b2) =>
        val BagType(base) = b1.getType: @unchecked
        Union(transform(base))(transform(b1), transform(b2)).copiedFrom(e)

      case BagDifference(b1, b2) =>
        val BagType(base) = b1.getType: @unchecked
        Difference(transform(base))(transform(b1), transform(b2)).copiedFrom(e)

      case _ => super.transform(e)
    }

    override def transform(tpe: Type): Type = tpe match {
      case BagType(base) => Bag(transform(base)).copiedFrom(tpe)
      case _ => super.transform(tpe)
    }
  }
  new BagEnc
}

def bagDec(sourceProgram: Program)
          (theory: BagTheory[sourceProgram.trees.type])
          (evaluator: DeterministicEvaluator { val program: sourceProgram.type }): transformers.TreeTransformer { val s: sourceProgram.trees.type; val t: sourceProgram.trees.type } = {
  class BagDec extends sourceProgram.trees.ConcreteSelfTreeTransformer {
    import theory._
    import theory.trees._
    import theory.trees.dsl._
    import evaluator.context.{given, _}

    override def transform(e: Expr): Expr = e match {
      case ADT(SumID, Seq(tpe), Seq(e1, e2)) => (transform(e1), transform(e2)) match {
        case (fb1 @ FiniteBag(els1, _), fb2 @ FiniteBag(els2, _))
          if exprOps.variablesOf(fb1).isEmpty && exprOps.variablesOf(fb2).isEmpty =>
          def groundMap(els: Seq[(Expr, Expr)]): Map[Expr, Expr] = els.map { case (key, value) => (
            evaluator.eval(key).result.getOrElse(throw new UnsupportedTree(e, "Failed to evaluate bag contents")),
            evaluator.eval(value).result.getOrElse(throw new UnsupportedTree(e, "Failed to evaluate bag contents"))
          )}.toMap

          val map1 = groundMap(els1)
          val map2 = groundMap(els2)

          FiniteBag((map1.keySet ++ map2.keySet).map { key =>
            val IntegerLiteral(i1) = map1.getOrElse(key, IntegerLiteral(0)): @unchecked
            val IntegerLiteral(i2) = map2.getOrElse(key, IntegerLiteral(0)): @unchecked
            key -> IntegerLiteral(i1 + i2)
          }.toSeq, transform(tpe)).copiedFrom(e)

        // Symbolic keys of the two bags may be equal, in which case their multiplicities
        // must be added up. A `FiniteBag` would let the right entry override the left one.
        case (FiniteBag(Seq(), _), b2) => b2
        case (b1, FiniteBag(Seq(), _)) => b1
        case (b1, b2) => BagUnion(b1, b2).copiedFrom(e)
      }

      case ADT(ElemID, Seq(tpe), Seq(key, value)) =>
        FiniteBag(Seq(transform(key) -> transform(value)), transform(tpe)).copiedFrom(e)

      case ADT(LeafID, Seq(tpe), Seq()) =>
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
  new BagDec
}

object BagEncoder {
  def apply(encc: transformers.ProgramTransformer)
           (ev: DeterministicEvaluator { val program: encc.sourceProgram.type }):
           BagEncoder { val sourceProgram: encc.targetProgram.type } =
    new BagEncoder(encc)(encc.targetProgram)(ReverseEvaluator(encc)(ev))(new BagTheory[encc.targetProgram.trees.type](encc.targetProgram.trees))
      .asInstanceOf
}
