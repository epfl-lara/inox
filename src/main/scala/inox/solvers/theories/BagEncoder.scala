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
  val NodeID = FreshIdentifier("Node")
  val ElemID = FreshIdentifier("Elem")
  val LeafID = FreshIdentifier("Leaf")

  val op    = FreshIdentifier("op")
  val left  = FreshIdentifier("left")
  val right = FreshIdentifier("right")
  val key   = FreshIdentifier("key")
  val value = FreshIdentifier("value")

  val Bag  = T(BagID)
  val Node = C(NodeID)
  val Elem = C(ElemID)
  val Leaf = C(LeafID)

  // Union, difference and intersection are all represented by `Node`s, and `get`
  // computes their multiplicities from those of their operands. Using a single
  // constructor keeps `get` down to two recursive calls on the selectors of its
  // argument. Computing differences and intersections by traversing their operands
  // instead takes many recursive calls, each of which adds congruence clauses for the
  // custom bag equality, which Princess can't cope with.
  val UnionOp = BigInt(0)
  val DifferenceOp = BigInt(1)
  val IntersectionOp = BigInt(2) // any other value is also treated as an intersection

  val GetID = FreshIdentifier("get")
  val Get = mkFunDef(GetID)("T") { case Seq(aT) => (
    Seq("bag" :: Bag(aT), "x" :: aT), IntegerType(), {
    case Seq(bag, x) => if_ (bag `is` NodeID) {
      let("v1" :: IntegerType(), E(GetID)(aT)(bag.getField(left), x)) { v1 =>
        let("v2" :: IntegerType(), E(GetID)(aT)(bag.getField(right), x)) { v2 =>
          if_ (bag.getField(op) === E(UnionOp)) {
            v1 + v2
          } else_ {
            if_ (bag.getField(op) === E(DifferenceOp)) {
              if_ (v1 <= v2) { E(BigInt(0)) } else_ { v1 - v2 }
            } else_ {
              if_ (v1 <= v2) { v1 } else_ { v2 }
            }
          }
        }
      }
    } else_ {
      if_ (bag.is(ElemID) && bag.getField(key) === x) {
        bag.getField(value)
      } else_ {
        E(BigInt(0))
      }
    }
  })
  }

  // The bag operations are encoded as `Node`s directly (rather than through function
  // calls), so that bags built from them are plain constructor terms.
  def Sum(aT: Type)(b1: Expr, b2: Expr): Expr = Node(aT)(E(UnionOp), b1, b2)
  def Difference(aT: Type)(b1: Expr, b2: Expr): Expr = Node(aT)(E(DifferenceOp), b1, b2)
  def Intersect(aT: Type)(b1: Expr, b2: Expr): Expr = Node(aT)(E(IntersectionOp), b1, b2)

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
      (NodeID, Seq(ValDef(op, IntegerType()), ValDef(left, Bag(aT)), ValDef(right, Bag(aT)))),
      (ElemID, Seq(ValDef(key, aT), ValDef(value, IntegerType()))),
      (LeafID, Seq())
    )
  }

  val extraFunctions =
    Seq(Get, BagEquals, BagInvariant)

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
        Sum(transform(base))(transform(bag), Elem(transform(base))(transform(elem), E(BigInt(1)))).copiedFrom(e)

      case MultiplicityInBag(elem, bag) =>
        val BagType(base) = bag.getType: @unchecked
        Get(transform(base))(transform(bag), transform(elem)).copiedFrom(e)

      case BagIntersection(b1, b2) =>
        val BagType(base) = b1.getType: @unchecked
        Intersect(transform(base))(transform(b1), transform(b2)).copiedFrom(e)

      case BagUnion(b1, b2) =>
        val BagType(base) = b1.getType: @unchecked
        Sum(transform(base))(transform(b1), transform(b2)).copiedFrom(e)

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

    private def groundMap(e: Expr, els: Seq[(Expr, Expr)]): Map[Expr, BigInt] = els.map { case (key, value) =>
      def eval(e2: Expr): Expr = evaluator.eval(e2).result.getOrElse(throw new UnsupportedTree(e, "Failed to evaluate bag contents"))
      val IntegerLiteral(i) = eval(value): @unchecked
      eval(key) -> i
    }.toMap

    // Combines the multiplicities of two decoded bags, or falls back to the
    // corresponding bag operation if they aren't ground.
    private def combine(e: Expr, b1: Expr, b2: Expr, tpe: Type)
                       (op: (BigInt, BigInt) => BigInt)
                       (mk: (Expr, Expr) => Expr): Expr = (b1, b2) match {
      case (FiniteBag(els1, _), FiniteBag(els2, _)) if exprOps.variablesOf(b1).isEmpty && exprOps.variablesOf(b2).isEmpty =>
        val map1 = groundMap(e, els1)
        val map2 = groundMap(e, els2)

        FiniteBag((map1.keySet ++ map2.keySet).toSeq.flatMap { key =>
          val i = op(map1.getOrElse(key, BigInt(0)), map2.getOrElse(key, BigInt(0)))
          if (i > 0) Some(key -> IntegerLiteral(i)) else None
        }, tpe).copiedFrom(e)

      case _ =>
        mk(b1, b2).copiedFrom(e)
    }

    override def transform(e: Expr): Expr = e match {
      case ADT(NodeID, Seq(tpe), Seq(IntegerLiteral(op), e1, e2)) =>
        val (b1, b2) = (transform(e1), transform(e2))
        if (op == UnionOp) combine(e, b1, b2, transform(tpe))(_ + _)(BagUnion(_, _))
        else if (op == DifferenceOp) combine(e, b1, b2, transform(tpe))(_ - _)(BagDifference(_, _))
        else combine(e, b1, b2, transform(tpe))(_ min _)(BagIntersection(_, _))

      case ADT(ElemID, Seq(tpe), Seq(key, value)) =>
        FiniteBag(Seq(transform(key) -> transform(value)), transform(tpe)).copiedFrom(e)

      case ADT(LeafID, Seq(tpe), Seq()) =>
        FiniteBag(Seq.empty, transform(tpe)).copiedFrom(e)

      case FunctionInvocation(GetID, _, Seq(bag, elem)) =>
        MultiplicityInBag(transform(elem), transform(bag)).copiedFrom(e)

      case _ => super.transform(e)
    }

    override def transform(tpe: Type): Type = tpe match {
      case ADTType(BagID | NodeID | ElemID | LeafID, Seq(base)) => BagType(transform(base)).copiedFrom(tpe)
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
