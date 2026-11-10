/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package ast

import org.scalatest.funsuite.AnyFunSuite

/** Symbol tables, definitions and their typed instances, and the generic tree operations. */
class DefinitionsSuite extends AnyFunSuite {
  import inox.trees._
  import inox.trees.dsl._

  val tp = TypeParameter.fresh("A")
  val boxId = FreshIdentifier("Box")
  val consId = FreshIdentifier("MkBox")
  val fieldId = FreshIdentifier("content")
  val annotated = ValDef(fieldId, tp, Seq(Annotation("field", Seq(tp, IntegerLiteral(1)))))
  val box = new ADTSort(boxId, Seq(TypeParameterDef(tp)), Seq(new ADTConstructor(consId, boxId, Seq(annotated))),
    Seq(Annotation("sort", Seq(tp))))

  val idFd = {
    val ftp = TypeParameter.fresh("T")
    val x = ValDef(FreshIdentifier("x"), ftp, Seq(Annotation("param", Seq(ftp))))
    new FunDef(FreshIdentifier("id"), Seq(TypeParameterDef(ftp)), Seq(x), ftp, x.toVariable, Seq(Annotation("fun", Seq(ftp))))
  }

  given symbols: Symbols = NoSymbols.withSorts(Seq(box)).withFunctions(Seq(idFd))

  test("Lookups") {
    val unknown = FreshIdentifier("unknown")
    assert(intercept[ADTLookupException](symbols.getSort(unknown)).getMessage.contains("Lookup failed for adt"))
    intercept[ADTLookupException](symbols.getSort(unknown, Seq()))
    intercept[ADTLookupException](symbols.getConstructor(unknown))
    intercept[ADTLookupException](symbols.getConstructor(unknown, Seq()))
    assert(intercept[FunctionLookupException](symbols.getFunction(unknown)).getMessage.contains("function"))
    intercept[FunctionLookupException](symbols.getFunction(unknown, Seq()))
    assert(symbols.getSort(boxId) == box)
    assert(symbols.getConstructor(consId).getSort == box)
    assert(symbols.toString.contains("Box") && symbols.toString.contains("id"))
  }

  test("Symbol equality") {
    assert(symbols == NoSymbols.withFunctions(Seq(idFd)).withSorts(Seq(box)))
    assert(symbols.hashCode == NoSymbols.withFunctions(Seq(idFd)).withSorts(Seq(box)).hashCode)
    assert(symbols != NoSymbols)
    assert(symbols != box)
  }

  test("Well-formedness") {
    val x = Variable.fresh("x", IntegerType())
    val bad = new FunDef(FreshIdentifier("bad"), Seq(), Seq(), IntegerType(), x, Seq())
    val ex = intercept[NotWellFormedException](NoSymbols.withFunctions(Seq(bad)).ensureWellFormed)
    assert(ex.getMessage.contains("Unknown variables"))
    symbols.ensureWellFormed
  }

  test("Type parameter definitions") {
    val tpd = TypeParameterDef.fresh("B", Seq(Annotation("tp", Seq())))
    assert(tpd.flags == Seq(Annotation("tp", Seq())))
    assert(tpd.freshen != tpd && tpd.freshen.id.name == "B")
    assert(tpd == TypeParameterDef(tpd.tp))
    assert(tpd != tp)
    assert(tpd.hashCode == tpd.tp.hashCode)
    assert(tpd.toString == s"TypeParameterDef(${tpd.tp})")
    val TypeParameterDef(id, flags) = tpd: @unchecked
    assert(id == tpd.id && flags == tpd.flags)
    assert(TypeParameterDef(id).flags.isEmpty)
  }

  test("Variable symbols") {
    val vd = ValDef.fresh("v", IntegerType())
    val v = vd.toVariable
    assert(v.to[ValDef] == vd && (vd.to[ValDef] eq vd))
    assert(vd.to[Variable] == v && (v.to[Variable] eq v))
    val vds = Seq(ValDef.fresh("b", IntegerType()), ValDef.fresh("a", IntegerType()))
    assert(vds.sorted == vds.sortBy(_.id))
  }

  test("Sorts, constructors and their typed instances") {
    val cons = box.constructors.head
    assert(!box.hasEquality && !box.hasInvariant)
    assert(box.isWellFormed)
    assert(cons.typed.fields.head.tpe == tp)
    assert(cons.copy(fields = Seq()).fields.isEmpty)
    assert(intercept[RuntimeException](cons.selectorID2Index(FreshIdentifier("nope"))).getMessage.contains("Could not find"))

    val typed = box.typed(Seq(IntegerType()))
    assert(typed.flags == Seq(Annotation("sort", Seq(IntegerType()))))
    val v = Variable.fresh("v", tp)
    assert(typed.instantiate(v).getType == IntegerType())
    val tcons = typed.constructors.head
    assert(tcons.fields.head.flags == Seq(Annotation("field", Seq(IntegerType(), IntegerLiteral(1)))))
    assert(tcons.fields.head.tpe == IntegerType())

    val tupleSort = mkSort(FreshIdentifier("Pairs"))() { _ =>
      Seq((FreshIdentifier("P"), Seq(ValDef.fresh("p", TupleType(Seq(IntegerType(), BooleanType()))))))
    }
    assert(tupleSort.isWellFormed(using NoSymbols.withSorts(Seq(tupleSort))))
  }

  test("Functions and their typed instances") {
    assert(idFd.applied == FunctionInvocation(idFd.id, idFd.typeArgs, Seq(idFd.params.head.toVariable)))
    assert(idFd.getTpe(stripRefinements = true) == idFd.returnType)
    assert(idFd.getTpe(stripRefinements = false) == idFd.returnType)
    assert(idFd.copy(fullBody = idFd.fullBody).fullBody == idFd.fullBody)
    val typed = idFd.typed(Seq(IntegerType()))
    assert(typed.flags == Seq(Annotation("fun", Seq(IntegerType()))))
    assert(typed.params.head.flags == Seq(Annotation("param", Seq(IntegerType()))))
    assert(typed.getTpe(stripRefinements = false) == IntegerType())
    assert(typed.instantiate(Annotation("f", Seq(idFd.tparams.head.tp))) == Annotation("f", Seq(IntegerType())))
    assert(box.typed(Seq(BooleanType())).instantiate(Annotation("s", Seq(tp))) == Annotation("s", Seq(BooleanType())))
  }

  test("Types") {
    val boxType = ADTType(boxId, Seq(IntegerType()))
    assert(boxType.getField(fieldId).map(_.id) == Some(fieldId))
    assert(boxType.getField(FreshIdentifier("nope")).isEmpty)
    assert(ADTType(FreshIdentifier("nope"), Seq()).getField(fieldId).isEmpty)
    assert(IntegerType().stripToplevelRefinement == IntegerType())
    val ref = RefinementType(ValDef.fresh("r", IntegerType()), BooleanLiteral(true))
    assert(ref.stripToplevelRefinement == IntegerType())
    assert(typeOps.isParametricType(SetType(tp)))
    assert(!typeOps.isParametricType(SetType(IntegerType())))
    assert(typeOps.isParametricType(tp))
  }

  test("Identifier aliasing") {
    val a1 = FreshIdentifier("a")
    val a2 = FreshIdentifier("a")
    assert(aliased(a1, a2))
    assert(!aliased(a1, FreshIdentifier("b")))
    assert(aliased(Set(a1), Set(a2, FreshIdentifier("c"))))
    assert(aliasedSymbols(Set(ValDef(a1, IntegerType())), Set(Variable(a2, IntegerType(), Seq()))))
    assert(!a1.equals(null) && !a1.equals("a"))
    val forced = FreshIdentifier.forceId("forced", 42)
    assert(forced.id == 42 && forced.name == "forced")
  }

  test("Generic tree operations") {
    import exprOps._
    val x = Variable.fresh("x", IntegerType())
    val e = Plus(Times(x, IntegerLiteral(2)), IntegerLiteral(1))

    assert(simpleTransform(
      { case IntegerLiteral(i) => IntegerLiteral(i + 1) case e => e },
      { case Plus(a, b) => Minus(a, b) case e => e })(e) ==
      Minus(Times(x, IntegerLiteral(3)), IntegerLiteral(2)))
    assert(simplePreTransform({ case Times(a, _) => a case e => e })(e) == Plus(x, IntegerLiteral(1)))

    val depths = preFoldWithContext[Int]((e, d) => d + 1, (e, d, subs) => (d +: subs).max)(e, 0)
    assert(depths == 3)
    assert(collectPreorder[Expr] { case l: IntegerLiteral => Seq(l) case _ => Seq() }(e) ==
      Seq(IntegerLiteral(2), IntegerLiteral(1)))
    assert(filter(_.isInstanceOf[IntegerLiteral])(e) == Set(IntegerLiteral(2), IntegerLiteral(1)))
    assert(depth(e) == 3)

    val renamed = Plus(Times(IntegerLiteral(5), IntegerLiteral(2)), IntegerLiteral(1))
    assert(lookup[Expr](_ == x, identity)(e, renamed) == Some(IntegerLiteral(5)))
    assert(lookup[Expr](_ == x, identity)(e, IntegerLiteral(0)).isEmpty)
    assert(lookup[Expr](_ == Variable.fresh("y", IntegerType()), identity)(e, renamed).isEmpty)
  }
}
