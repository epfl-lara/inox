/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package ast

import org.scalatest.funsuite.AnyFunSuite

/** The generic operations on types look into the types of the variables that pi, sigma and
  * refinement types bind. */
class BinderTypeSuite extends AnyFunSuite {
  import inox.trees._
  import inox.trees.dsl._

  val sel = FreshIdentifier("x")
  val tID = FreshIdentifier("T")

  // case class T(x: BigInt, y: field)
  def withField(field: Type): ADTSort =
    mkSort(tID)() { _ => Seq((FreshIdentifier("T"), Seq(ValDef(sel, IntegerType()), ValDef(FreshIdentifier("y"), field)))) }

  def wellFormed(sorts: Seq[ADTSort], functions: Seq[FunDef] = Seq()): Boolean =
    scala.util.Try(NoSymbols.withSorts(sorts).withFunctions(functions).ensureWellFormed).isSuccess

  // { v: BigInt | forall((t: T) => t.x != v) }
  def paradox: Type = {
    val v = Variable.fresh("v", IntegerType())
    RefinementType(v.toVal, forall("t" :: T(tID)())(t => Not(Equals(t.getField(sel), v))))
  }

  test("control: a field refinement that quantifies over its sort is rejected") {
    assert(!wellFormed(Seq(withField(paradox))))
  }

  test("stratification: a refinement under a refinement") {
    val w = Variable.fresh("w", paradox)
    assert(!wellFormed(Seq(withField(RefinementType(w.toVal, E(true))))))
  }

  test("stratification: a refinement in a sigma parameter") {
    assert(!wellFormed(Seq(withField(SigmaType(Seq(ValDef.fresh("a", paradox)), IntegerType())))))
  }

  test("stratification: a refinement in a pi parameter") {
    assert(!wellFormed(Seq(withField(PiType(Seq(ValDef.fresh("a", paradox)), IntegerType())))))
  }

  test("stratification: a refinement in the result of a sigma under a refinement") {
    val s = Variable.fresh("s", SigmaType(Seq(ValDef.fresh("a", IntegerType())), paradox))
    assert(!wellFormed(Seq(withField(RefinementType(s.toVal, E(true))))))
  }

  test("stratification: an uninterpreted call of a refined sort type") {
    // case class T(x: BigInt) { require(choose((t: { t: T | true }) => true) != this) }
    val r = Variable.fresh("r", T(tID)())
    val choose = UninterpretedCall(FreshIdentifier("choose"), Seq(), Seq(),
      FunctionType(Seq(), RefinementType(r.toVal, E(true))))
    val inv = mkFunDef(FreshIdentifier("TInv"))() { _ =>
      (Seq("t" :: T(tID)()), BooleanType(), { case Seq(t) => Not(Equals(choose, t)) })
    }
    val sort = mkSort(tID, HasADTInvariant(inv.id))() { _ =>
      Seq((FreshIdentifier("T"), Seq(ValDef(sel, IntegerType()))))
    }
    assert(!wellFormed(Seq(sort), Seq(inv)))
  }

  test("control: an uninterpreted call of the plain sort type is rejected") {
    val choose = UninterpretedCall(FreshIdentifier("choose"), Seq(), Seq(), FunctionType(Seq(), T(tID)()))
    val inv = mkFunDef(FreshIdentifier("TInv"))() { _ =>
      (Seq("t" :: T(tID)()), BooleanType(), { case Seq(t) => Not(Equals(choose, t)) })
    }
    val sort = mkSort(tID, HasADTInvariant(inv.id))() { _ =>
      Seq((FreshIdentifier("T"), Seq(ValDef(sel, IntegerType()))))
    }
    assert(!wellFormed(Seq(sort), Seq(inv)))
  }

  test("isParametricType: type parameters under binders") {
    val a = TypeParameter.fresh("A")
    assert(typeOps.isParametricType(RefinementType(ValDef.fresh("v", a), E(true))))
    assert(typeOps.isParametricType(SigmaType(Seq(ValDef.fresh("v", a)), IntegerType())))
    assert(typeOps.isParametricType(PiType(Seq(ValDef.fresh("v", a)), IntegerType())))
  }

  test("typeOps reaches the types of bound variables") {
    val a = TypeParameter.fresh("A")
    def has(tpe: Type): Boolean = typeOps.exists(_ == a)(tpe)
    assert(has(RefinementType(ValDef.fresh("v", a), E(true))))
    assert(has(SigmaType(Seq(ValDef.fresh("v", a)), IntegerType())))
    assert(has(PiType(Seq(ValDef.fresh("v", a)), IntegerType())))
    val inner = RefinementType(ValDef.fresh("w", a), E(true))
    assert(typeOps.collect[Type] { case r: RefinementType => Set(r) case _ => Set() }(
      RefinementType(ValDef.fresh("v", inner), E(true))).contains(inner))
  }

  test("typeOps substitutes the bound variables whose type it changes") {
    val a = TypeParameter.fresh("A")
    val toInt: Type => Option[Type] = { case `a` => Some(IntegerType()) case _ => None }

    // { v: A | v == v }
    val v = Variable.fresh("v", a)
    val RefinementType(nv, pred) = typeOps.preMap(toInt)(RefinementType(v.toVal, Equals(v, v))): @unchecked
    assert(nv.tpe == IntegerType() && pred == Equals(nv.toVariable, nv.toVariable))

    // (x: A, y: { y: A | y == x }, { z: A | z == y })
    val x = Variable.fresh("x", a)
    val y = Variable.fresh("y", RefinementType(ValDef.fresh("y", a), E(true)))
    val yv = Variable.fresh("y", a)
    val z = Variable.fresh("z", a)
    val sigma = SigmaType(Seq(x.toVal, ValDef(y.id, RefinementType(yv.toVal, Equals(yv, x)))),
      RefinementType(z.toVal, Equals(z, Variable(y.id, RefinementType(yv.toVal, Equals(yv, x)), Seq()))))
    val res = typeOps.preMap(toInt)(sigma)
    assert(!typeOps.isParametricType(res))
    assert(typeOps.variablesOf(res).isEmpty)
  }
}
