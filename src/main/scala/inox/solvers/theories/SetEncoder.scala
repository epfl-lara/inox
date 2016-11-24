/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package theories

import evaluators._
import scala.collection.immutable.{Set => ScalaSet}

trait SetEncoder extends SimpleEncoder {
  import trees._
  import trees.dsl._

  val evaluator: DeterministicEvaluator {
    val program: sourceProgram.type
  }

  val ReprID = FreshIdentifier("Repr")
  val SumID = FreshIdentifier("Sum")
  val ElemID = FreshIdentifier("Elem")
  val LeafID = FreshIdentifier("Leaf")

  val left = FreshIdentifier("left")
  val right = FreshIdentifier("right")
  val value = FreshIdentifier("value")

  val Repr = T(ReprID)
  val Sum  = T(SumID)
  val Elem = T(ElemID)
  val Leaf = T(LeafID)

  val reprADT = mkSort(ReprID)("T")(Seq(SumID, ElemID, LeafID))
  val sumADT = mkConstructor(SumID)("T")(Some(ReprID)) {
    case Seq(aT) => Seq(ValDef(left, Repr(aT)), ValDef(right, Repr(aT)))
  }

  val elemADT = mkConstructor(ElemID)("T")(Some(ReprID)) {
    case Seq(aT) => Seq(ValDef(value, aT))
  }

  val leafADT = mkConstructor(LeafID)("T")(Some(ReprID))(_ => Seq.empty)

  val ReprContainsID = FreshIdentifier("reprContains")
  val ReprContains = mkFunDef(ReprContainsID)("T") { case Seq(aT) => (
    Seq("repr" :: Repr(aT), "x" :: aT), BooleanType, {
      case Seq(repr, x) => !repr.isInstOf(Leaf(aT)) && (if_ (repr.isInstOf(Sum(aT))) {
        E(ReprContainsID)(aT)(repr.asInstOf(Sum(aT)).getField(left), x) ||
        E(ReprContainsID)(aT)(repr.asInstOf(Sum(aT)).getField(right), x)
      } else_ {
        repr.asInstOf(Elem(aT)).getField(value) === x
      })
    })
  }

  val SetID = FreshIdentifier("Set")
  val repr = FreshIdentifier("repr")
  val f = FreshIdentifier("f")

  val Set = T(SetID)

  val ContainsID = FreshIdentifier("contains")
  val Contains = mkFunDef(ContainsID)("T") { case Seq(aT) => (
    Seq("set" :: Set(aT), "x" :: aT), BooleanType, {
      case Seq(set, x) => E(ReprContainsID)(aT)(set.getField(repr), x) && set.getField(f)(x)
    })
  }

  val AddID = FreshIdentifier("add")
  val Add = mkFunDef(AddID)("T") { case Seq(aT) => (
    Seq("set" :: Set(aT), "x" :: aT), Set(aT), {
      case Seq(set, x) => Set(aT)(
        Sum(aT)(set.getField(repr), Elem(aT)(x)),
        \("y" :: aT)(y => set.getField(f)(y) || y === x)
      )
    })
  }

  val UnionID = FreshIdentifier("union")
  val Union = mkFunDef(UnionID)("T") { case Seq(aT) => (
    Seq("s1" :: Set(aT), "s2" :: Set(aT)), Set(aT), {
      case Seq(s1, s2) => Set(aT)(
        Sum(aT)(s1.getField(repr), s2.getField(repr)),
        \("y" :: aT)(y => s1.getField(f)(y) || s2.getField(f)(y))
      )
    })
  }

  val DifferenceID = FreshIdentifier("difference")
  val Difference = mkFunDef(DifferenceID)("T") { case Seq(aT) => (
    Seq("s1" :: Set(aT), "s2" :: Set(aT)), Set(aT), {
      case Seq(s1, s2) => Set(aT)(
        s1.getField(repr),
        \("y" :: aT)(y => s1.getField(f)(y) && !s2.getField(f)(y))
      )
    })
  }

  val IntersectID = FreshIdentifier("intersect")
  val Intersect = mkFunDef(IntersectID)("T") { case Seq(aT) => (
    Seq("s1" :: Set(aT), "s2" :: Set(aT)), Set(aT), {
      case Seq(s1, s2) => Set(aT)(
        s1.getField(repr),
        \("y" :: aT)(y => s1.getField(f)(y) && s2.getField(f)(y))
      )
    })
  }

  val EqualsID = FreshIdentifier("equals")
  val SetEquals = mkFunDef(EqualsID)("T") { case Seq(aT) => (
    Seq("s1" :: Set(aT), "s2" :: Set(aT)), BooleanType, {
      case Seq(s1, s2) => forall("y" :: aT) { y =>
        (E(ReprContainsID)(aT)(y) && s1.getField(f)(y)) ===
          (E(ReprContainsID)(aT)(y) && s2.getField(f)(y))
      }
    })
  }

  val setADT: ADTConstructor = {
    val tparams @ Seq(TypeParameterDef(tp)) = Seq(TypeParameterDef(TypeParameter.fresh("T")))
    new ADTConstructor(SetID, tparams, None,
      Seq(ValDef(repr, Repr(tp)), ValDef(f, tp =>: BooleanType)),
      ScalaSet(HasADTEquality(EqualsID))
    )
  }

  override val extraFunctions = Seq(ReprContains, Contains, Add, Union, Difference, Intersect, SetEquals)
  override val extraADTs = Seq(reprADT, sumADT, elemADT, leafADT, setADT)

  protected object encoder extends SelfTreeTransformer {
    import sourceProgram._

    override def transform(e: Expr): Expr = e match {
      case FiniteSet(elems, tpe) =>
        val newTpe = transform(tpe)
        val newElems = elems.map(transform)
        Set(newTpe)(
          newElems.foldLeft(Leaf(newTpe)())((acc, x) => Sum(newTpe)(acc, Elem(newTpe)(x))),
          \("x" :: newTpe)(x => newElems.foldLeft(E(false).copiedFrom(e)) {
            (res,elem) => (res || (x === elem).copiedFrom(e)).copiedFrom(e)
          })
        ).copiedFrom(e)

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

        FiniteSet(rec(elems).toSeq.flatMap { e =>
          val te = transform(e)
          val res = evaluator.eval(Application(tl, Seq(te))).result.getOrElse {
            throw new Unsupported(e, "Unexpectedly failed to evaluate set lambda")
          }

          if (res == BooleanLiteral(true)) Some(e) else None
        }, transform(tpe)).copiedFrom(e)

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
  def apply(enc: ast.ProgramTransformer, opts: Options)
           (ev: DeterministicEvaluator { val program: enc.sourceProgram.type }):
           SetEncoder { val sourceProgram: enc.targetProgram.type } = new {
    val sourceProgram: enc.targetProgram.type = enc.targetProgram
    val evaluator = ReverseEvaluator(enc, opts)(ev)
  } with SetEncoder
}
