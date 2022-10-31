/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package theories

import scala.collection.immutable.{Set => ScalaSet}

class SetEncoder private(override val sourceProgram: Program)
                        (theory: SetTheory[sourceProgram.trees.type]) extends
  SimpleEncoder(
    sourceProgram,
    new SetEnc[sourceProgram.type](sourceProgram)(theory).asInstanceOf,
    new SetDec[sourceProgram.type](sourceProgram)(theory).asInstanceOf,
    theory.extraFunctions,
    theory.extraSorts
  )

private class SetTheory[Trees <: ast.Trees](val trees: Trees) {
  import trees._
  import trees.dsl._

  val SetID = FreshIdentifier("Set")
  val SumID = FreshIdentifier("Sum")
  val ElemID = FreshIdentifier("Elem")
  val LeafID = FreshIdentifier("Leaf")

  val left = FreshIdentifier("left")
  val right = FreshIdentifier("right")
  val value = FreshIdentifier("value")

  val Set = T(SetID)
  val Sum  = C(SumID)
  val Elem = C(ElemID)
  val Leaf = C(LeafID)

  val ContainsID = FreshIdentifier("contains")
  val Contains = mkFunDef(ContainsID)("T") { case Seq(aT) => (
    Seq("set" :: Set(aT), "x" :: aT), BooleanType(), {
    case Seq(set, x) => !set.is(LeafID) && (if_ (set.is(SumID)) {
      E(ContainsID)(aT)(set.getField(left), x) ||
        E(ContainsID)(aT)(set.getField(right), x)
    } else_ {
      set.getField(value) === x
    })
  })
  }

  val RemoveID = FreshIdentifier("remove")
  val Remove = mkFunDef(RemoveID)("T") { case Seq(aT) => (
    Seq("set" :: Set(aT), "x" :: aT), Set(aT), {
    case Seq(set, x) => if_ (set.is(SumID)) {
      Sum(aT)(E(RemoveID)(aT)(set.getField(left), x),
        E(RemoveID)(aT)(set.getField(right), x))
    } else_ {
      if_ (set.is(ElemID) && set.getField(value) === x) {
        Leaf(aT)()
      } else_ {
        set
      }
    }
  })
  }

  val AddID = FreshIdentifier("add")
  val Add = mkFunDef(AddID)("T") { case Seq(aT) => (
    Seq("set" :: Set(aT), "x" :: aT), Set(aT), {
    case Seq(set, x) => Sum(aT)(set, Elem(aT)(x))
  })
  }

  val UnionID = FreshIdentifier("union")
  val Union = mkFunDef(UnionID)("T") { case Seq(aT) => (
    Seq("s1" :: Set(aT), "s2" :: Set(aT)), Set(aT), {
    case Seq(s1, s2) => Sum(aT)(s1, s2)
  })
  }

  val DifferenceID = FreshIdentifier("difference")
  val Difference = mkFunDef(DifferenceID)("T") { case Seq(aT) => (
    Seq("s1" :: Set(aT), "s2" :: Set(aT)), Set(aT), {
    case Seq(s1, s2) => if_ (s2.is(SumID)) {
      E(DifferenceID)(aT)(
        E(DifferenceID)(aT)(s1, s2.getField(left)),
        s2.getField(right)
      )
    } else_ {
      if_ (s2.is(ElemID)) {
        E(RemoveID)(aT)(s1, s2.getField(value))
      } else_ {
        s1
      }
    }
  })
  }

  val IntersectID = FreshIdentifier("intersect")
  val Intersect = mkFunDef(IntersectID)("T") { case Seq(aT) => (
    Seq("s1" :: Set(aT), "s2" :: Set(aT)), Set(aT), {
    case Seq(s1, s2) => if_ (s1.is(SumID)) {
      Sum(aT)(E(IntersectID)(aT)(s1.getField(left), s2),
        E(IntersectID)(aT)(s1.getField(right), s2))
    } else_ {
      if_ (s1.is(ElemID) && !E(ContainsID)(aT)(s2, s1.getField(value))) {
        Leaf(aT)()
      } else_ {
        s1
      }
    }
  })
  }

  val EqualsID = FreshIdentifier("equals")
  val SetEquals = mkFunDef(EqualsID)("T") { case Seq(aT) => (
    Seq("s1" :: Set(aT), "s2" :: Set(aT)), BooleanType(), {
    case Seq(s1, s2) => forall("y" :: aT) { y =>
      E(ContainsID)(aT)(s1, y) === E(ContainsID)(aT)(s2, y)
    }
  })
  }

  val setSort = mkSort(SetID, HasADTEquality(EqualsID))("T") {
    case Seq(aT) => Seq(
      (SumID, Seq(ValDef(left, Set(aT)), ValDef(right, Set(aT)))),
      (ElemID, Seq(ValDef(value, aT))),
      (LeafID, Seq.empty)
    )
  }

  val extraFunctions = Seq(Contains, Remove, Add, Union, Difference, Intersect, SetEquals)
  val extraSorts = Seq(setSort)
}

private class SetEnc[Prog <: Program]
  (val sourceProgram: Prog)
  (val theory: SetTheory[sourceProgram.trees.type])
  extends theory.trees.ConcreteSelfTreeTransformer {

  import theory._
  import theory.trees._
  import theory.trees.dsl._
  import sourceProgram.symbols.{given, _}

  override def transform(e: Expr): Expr = e match {
    case FiniteSet(elems, tpe) =>
      val newTpe = transform(tpe)
      val newElems = elems.map(transform)
      newElems.foldLeft(Leaf(newTpe).copiedFrom(e)().copiedFrom(e)) {
        (acc, x) => Sum(newTpe).copiedFrom(e)(acc, Elem(newTpe).copiedFrom(e)(x).copiedFrom(e)).copiedFrom(e)
      }

    case SetAdd(set, elem) =>
      val SetType(base) = set.getType: @unchecked
      Add(transform(base))(transform(set), transform(elem)).copiedFrom(e)

    case ElementOfSet(elem, set) =>
      val SetType(base) = set.getType: @unchecked
      Contains(transform(base))(transform(set), transform(elem)).copiedFrom(e)

    case SetIntersection(s1, s2) =>
      val SetType(base) = s1.getType: @unchecked
      Intersect(transform(base))(transform(s1), transform(s2)).copiedFrom(e)

    case SetUnion(s1, s2) =>
      val SetType(base) = s1.getType: @unchecked
      Union(transform(base))(transform(s1), transform(s2)).copiedFrom(e)

    case SetDifference(s1, s2) =>
      val SetType(base) = s1.getType: @unchecked
      Difference(transform(base))(transform(s1), transform(s2)).copiedFrom(e)

    case _ => super.transform(e)
  }

  override def transform(tpe: Type): Type = tpe match {
    case SetType(base) => Set(transform(base)).copiedFrom(tpe)
    case _ => super.transform(tpe)
  }
}

private class SetDec[Prog <: Program]
  (val sourceProgram: Prog)
  (val theory: SetTheory[sourceProgram.trees.type])
  extends theory.trees.ConcreteSelfTreeTransformer {

  import theory._
  import theory.trees._
  import theory.trees.dsl._

  override def transform(e: Expr): Expr = e match {
    case ADT(SumID, Seq(tpe), Seq(e1, e2)) =>
      val FiniteSet(els1, _) = transform(e1): @unchecked
      val FiniteSet(els2, _) = transform(e2): @unchecked
      FiniteSet(els1 ++ els2, transform(tpe)).copiedFrom(e)

    case ADT(ElemID, Seq(tpe), Seq(e)) =>
      FiniteSet(Seq(transform(e)), transform(tpe)).copiedFrom(e)

    case ADT(LeafID, Seq(tpe), Seq()) =>
      FiniteSet(Seq.empty, transform(tpe)).copiedFrom(e)

    case FunctionInvocation(AddID, _, Seq(set, elem)) =>
      SetAdd(transform(set), transform(elem)).copiedFrom(e)

    case FunctionInvocation(ContainsID, _, Seq(set, elem)) =>
      ElementOfSet(transform(elem), transform(set)).copiedFrom(e)

    case FunctionInvocation(IntersectID, _, Seq(s1, s2)) =>
      SetIntersection(transform(s1), transform(s2)).copiedFrom(e)

    case FunctionInvocation(UnionID, _, Seq(s1, s2)) =>
      SetUnion(transform(s1), transform(s2)).copiedFrom(e)

    case FunctionInvocation(DifferenceID, _, Seq(s1, s2)) =>
      SetDifference(transform(s1), transform(s2)).copiedFrom(e)

    case _ => super.transform(e)
  }

  override def transform(tpe: Type): Type = tpe match {
    case ADTType(SetID, Seq(base)) => SetType(transform(base)).copiedFrom(tpe)
    case _ => super.transform(tpe)
  }
}

object SetEncoder {
  def apply(p: Program): SetEncoder { val sourceProgram: p.type } =
    new SetEncoder(p)(new SetTheory[p.trees.type](p.trees)).asInstanceOf
}
