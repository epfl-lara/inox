/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package theories

import scala.collection.immutable.{Set => ScalaSet}

trait SetEncoder extends SimpleEncoder {
  import trees.{forall => _, _}
  import trees.dsl._

  val SetID = FreshIdentifier("Set")
  val SumID = FreshIdentifier("Sum")
  val ElemID = FreshIdentifier("Elem")
  val LeafID = FreshIdentifier("Leaf")

  val left = FreshIdentifier("left")
  val right = FreshIdentifier("right")
  val value = FreshIdentifier("value")

  val Set = T(SetID)
  val Sum  = T(SumID)
  val Elem = T(ElemID)
  val Leaf = T(LeafID)

  val ContainsID = FreshIdentifier("contains")
  val Contains = mkFunDef(ContainsID)("T") { case Seq(aT) => (
    Seq("set" :: Set(aT), "x" :: aT), BooleanType, {
      case Seq(set, x) => !set.isInstOf(Leaf(aT)) && (if_ (set.isInstOf(Sum(aT))) {
        E(ContainsID)(aT)(set.asInstOf(Sum(aT)).getField(left), x) ||
        E(ContainsID)(aT)(set.asInstOf(Sum(aT)).getField(right), x)
      } else_ {
        set.asInstOf(Elem(aT)).getField(value) === x
      })
    })
  }

  val RemoveID = FreshIdentifier("remove")
  val Remove = mkFunDef(RemoveID)("T") { case Seq(aT) => (
    Seq("set" :: Set(aT), "x" :: aT), Set(aT), {
      case Seq(set, x) => if_ (set.isInstOf(Sum(aT))) {
        Sum(aT)(E(RemoveID)(aT)(set.asInstOf(Sum(aT)).getField(left), x),
          E(RemoveID)(aT)(set.asInstOf(Sum(aT)).getField(right), x))
      } else_ {
        if_ (set.isInstOf(Elem(aT)) && set.asInstOf(Elem(aT)).getField(value) === x) {
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
      case Seq(s1, s2) => if_ (s2.isInstOf(Sum(aT))) {
        E(DifferenceID)(aT)(
          E(DifferenceID)(aT)(s1, s2.asInstOf(Sum(aT)).getField(left)),
          s2.asInstOf(Sum(aT)).getField(right)
        )
      } else_ {
        if_ (s2.isInstOf(Elem(aT))) {
          E(RemoveID)(aT)(s1, s2.asInstOf(Elem(aT)).getField(value))
        } else_ {
          s1
        }
      }
    })
  }

  val IntersectID = FreshIdentifier("intersect")
  val Intersect = mkFunDef(IntersectID)("T") { case Seq(aT) => (
    Seq("s1" :: Set(aT), "s2" :: Set(aT)), Set(aT), {
      case Seq(s1, s2) => if_ (s1.isInstOf(Sum(aT))) {
        Sum(aT)(E(IntersectID)(aT)(s1.asInstOf(Sum(aT)).getField(left), s2),
          E(IntersectID)(aT)(s1.asInstOf(Sum(aT)).getField(right), s2))
      } else_ {
        if_ (s1.isInstOf(Elem(aT)) && !E(ContainsID)(aT)(s2, s1.asInstOf(Elem(aT)).getField(value))) {
          Leaf(aT)()
        } else_ {
          s1
        }
      }
    })
  }

  val EqualsID = FreshIdentifier("equals")
  val SetEquals = mkFunDef(EqualsID)("T") { case Seq(aT) => (
    Seq("s1" :: Set(aT), "s2" :: Set(aT)), BooleanType, {
      case Seq(s1, s2) => forall("y" :: aT) { y =>
        E(ContainsID)(aT)(s1, y) === E(ContainsID)(aT)(s2, y)
      }
    })
  }

  val setADT: ADTDefinition = {
    val tparams = Seq(TypeParameterDef(TypeParameter.fresh("T")))
    val tp = tparams.head.tp
    new ADTSort(SetID, tparams, Seq(SumID, ElemID, LeafID),
      ScalaSet(HasADTEquality(EqualsID))
    )
  }

  val sumADT = mkConstructor(SumID)("T")(Some(SetID)) {
    case Seq(aT) => Seq(ValDef(left, Set(aT)), ValDef(right, Set(aT)))
  }

  val elemADT = mkConstructor(ElemID)("T")(Some(SetID)) {
    case Seq(aT) => Seq(ValDef(value, aT))
  }

  val leafADT = mkConstructor(LeafID)("T")(Some(SetID))(_ => Seq.empty)

  override val extraFunctions = Seq(Contains, Remove, Add, Union, Difference, Intersect, SetEquals)
  override val extraADTs = Seq(setADT, sumADT, elemADT, leafADT)

  protected object encoder extends SelfTreeTransformer {
    import sourceProgram._

    override def transform(e: Expr): Expr = e match {
      case FiniteSet(elems, tpe) =>
        val newTpe = transform(tpe)
        val newElems = elems.map(transform)
        newElems.foldLeft(Leaf(newTpe).copiedFrom(e)().copiedFrom(e)) {
          (acc, x) => Sum(newTpe).copiedFrom(e)(acc, Elem(newTpe).copiedFrom(e)(x).copiedFrom(e)).copiedFrom(e)
        }

      case SetAdd(set, elem) =>
        val SetType(base) = set.getType
        Add(transform(base))(transform(set), transform(elem)).copiedFrom(e)

      case ElementOfSet(elem, set) =>
        val SetType(base) = set.getType
        Contains(transform(base))(transform(set), transform(elem)).copiedFrom(e)

      case SetIntersection(s1, s2) =>
        val SetType(base) = s1.getType
        Intersect(transform(base))(transform(s1), transform(s2)).copiedFrom(e)

      case SetUnion(s1, s2) =>
        val SetType(base) = s1.getType
        Union(transform(base))(transform(s1), transform(s2)).copiedFrom(e)

      case SetDifference(s1, s2) =>
        val SetType(base) = s1.getType
        Difference(transform(base))(transform(s1), transform(s2)).copiedFrom(e)

      case _ => super.transform(e)
    }

    override def transform(tpe: Type): Type = tpe match {
      case SetType(base) => Set(transform(base)).copiedFrom(tpe)
      case _ => super.transform(tpe)
    }
  }

  protected object decoder extends SelfTreeTransformer {
    import targetProgram._

    override def transform(e: Expr): Expr = e match {
      case cc @ ADT(ADTType(SetID, Seq(tpe)), Seq(elems, l @ Lambda(Seq(_), _))) =>
        val tl = transform(l)
        def rec(e: Expr): ScalaSet[Expr] = e match {
          case ADT(ADTType(SumID, Seq(_)), Seq(e1, e2)) => rec(e1) ++ rec(e2)
          case ADT(ADTType(ElemID, Seq(_)), Seq(e)) => ScalaSet(e)
          case ADT(ADTType(LeafID, Seq(_)), Seq()) => ScalaSet.empty
          case _ => throw new Unsupported(e, "Unexpected element in set contents")
        }

        FiniteSet(rec(elems).toSeq.map(transform), transform(tpe)).copiedFrom(e)

      case FunctionInvocation(AddID, Seq(_), Seq(set, elem)) =>
        SetAdd(transform(set), transform(elem)).copiedFrom(e)

      case FunctionInvocation(ContainsID, Seq(_), Seq(set, elem)) =>
        ElementOfSet(transform(elem), transform(set)).copiedFrom(e)

      case FunctionInvocation(IntersectID, Seq(_), Seq(s1, s2)) =>
        SetIntersection(transform(s1), transform(s2)).copiedFrom(e)

      case FunctionInvocation(UnionID, Seq(_), Seq(s1, s2)) =>
        SetUnion(transform(s1), transform(s2)).copiedFrom(e)

      case FunctionInvocation(DifferenceID, Seq(_), Seq(s1, s2)) =>
        SetDifference(transform(s1), transform(s2)).copiedFrom(e)

      case _ => super.transform(e)
    }

    override def transform(tpe: Type): Type = tpe match {
      case ADTType(SetID, Seq(base)) => SetType(transform(base)).copiedFrom(tpe)
      case _ => super.transform(tpe)
    }
  }
}

object SetEncoder {
  def apply(p: Program): SetEncoder { val sourceProgram: p.type } = new {
    val sourceProgram: p.type = p
  } with SetEncoder
}
