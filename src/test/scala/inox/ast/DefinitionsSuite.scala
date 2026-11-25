/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package ast

import org.scalatest.funsuite.AnyFunSuite

/** Symbol tables, definitions and their typed instances, and the generic tree operations. */
class DefinitionsSuite extends AnyFunSuite {
  import inox.trees._
  import inox.trees.dsl._

  val tp = TypeParameter.fresh("A")
  // Annotation arguments are expressions, so an empty set carries the types that instantiation changes
  def at(tpe: Type): Expr = FiniteSet(Seq(), tpe)
  val boxId = FreshIdentifier("Box")
  val consId = FreshIdentifier("MkBox")
  val fieldId = FreshIdentifier("content")
  val annotated = ValDef(fieldId, tp, Seq(Annotation("field", Seq(at(tp), IntegerLiteral(1)))))
  val box = new ADTSort(boxId, Seq(TypeParameterDef(tp)), Seq(new ADTConstructor(consId, boxId, Seq(annotated))),
    Seq(Annotation("sort", Seq(at(tp)))))

  val idFd = {
    val ftp = TypeParameter.fresh("T")
    val x = ValDef(FreshIdentifier("x"), ftp, Seq(Annotation("param", Seq(at(ftp)))))
    new FunDef(FreshIdentifier("id"), Seq(TypeParameterDef(ftp)), Seq(x), ftp, x.toVariable, Seq(Annotation("fun", Seq(at(ftp)))))
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

  test("Sort invariants can't quantify over values that depend on their own") {
    // a sort `id` with a field `x: BigInt` and a field of type `field`, if any, refined by `inv`
    def refined(id: Identifier, inv: FunDef, field: Option[Type] = None): ADTSort =
      mkSort(id, HasADTInvariant(inv.id))() { _ =>
        Seq((FreshIdentifier(id.name), Seq(ValDef(FreshIdentifier("x"), IntegerType())) ++
          field.map(ValDef(FreshIdentifier("f"), _))))
      }
    def invariant(id: Identifier)(body: Expr => Expr): FunDef =
      mkFunDef(FreshIdentifier(id.name + "Inv"))() { _ =>
        (Seq("t" :: T(id)()), BooleanType(), { case Seq(t) => body(t) })
      }
    def wellFormed(sorts: Seq[ADTSort], functions: Seq[FunDef]): Boolean =
      scala.util.Try(NoSymbols.withSorts(sorts).withFunctions(functions).ensureWellFormed).isSuccess

    // case class T(x: BigInt) { require(forall((t: T) => false)) }: T has values iff it has none
    val tID = FreshIdentifier("T")
    val tInv = invariant(tID)(_ => forall("u" :: T(tID)())(_ => E(false)))
    val ex = intercept[NotWellFormedException](
      NoSymbols.withSorts(Seq(refined(tID, tInv))).withFunctions(Seq(tInv)).ensureWellFormed)
    assert(ex.getMessage.contains("quantifies over the values of"))

    // the same, through a function that the invariant calls
    val none = mkFunDef(FreshIdentifier("none"))() { _ =>
      (Seq(), BooleanType(), { case Seq() => forall("u" :: T(tID)())(_ => E(false)) })
    }
    val tCalls = invariant(tID)(_ => FunctionInvocation(none.id, Seq(), Seq()))
    assert(!wellFormed(Seq(refined(tID, tCalls)), Seq(tCalls, none)))

    // through a generic function that quantifies over its type parameter
    val noneOf = mkFunDef(FreshIdentifier("noneOf"))("A") { case Seq(a) =>
      (Seq(), BooleanType(), { case Seq() => forall("u" :: a)(_ => E(false)) })
    }
    val tGeneric = invariant(tID)(_ => FunctionInvocation(noneOf.id, Seq(T(tID)()), Seq()))
    assert(!wellFormed(Seq(refined(tID, tGeneric)), Seq(tGeneric, noneOf)))

    // through functions of the sort, and through another sort that holds it
    val tFun = invariant(tID)(_ => forall("f" :: (IntegerType() =>: T(tID)()))(_ => E(false)))
    assert(!wellFormed(Seq(refined(tID, tFun)), Seq(tFun)))
    val aID = FreshIdentifier("A")
    val bID = FreshIdentifier("B")
    val aInv = invariant(aID)(_ => forall("b" :: T(bID)())(_ => E(false)))
    val b = mkSort(bID)() { _ => Seq((FreshIdentifier("B"), Seq(ValDef(FreshIdentifier("a"), T(aID)())))) }
    assert(!wellFormed(Seq(refined(aID, aInv), b), Seq(aInv)))

    // through another sort that only quantifies over it: an A exists iff no B exists, and a B
    // exists iff some A exists, without either sort holding the other
    val aOnly = invariant(aID)(_ => forall("b" :: T(bID)())(_ => E(false)))
    val bOnly = invariant(bID)(_ => Not(forall("a" :: T(aID)())(_ => E(false))))
    assert(!wellFormed(Seq(refined(aID, aOnly), refined(bID, bOnly)), Seq(aOnly, bOnly)))

    // quantifiers over other values are fine
    val cID = FreshIdentifier("C")
    val tOthers = invariant(tID)(_ => forall("c" :: T(cID)())(_ => forall("y" :: IntegerType())(_ => E(true))))
    val c = mkSort(cID)() { _ => Seq((FreshIdentifier("C"), Seq(ValDef(FreshIdentifier("n"), IntegerType())))) }
    assert(wellFormed(Seq(refined(tID, tOthers), c), Seq(tOthers)))
    // as are the uses of the sort's values that don't quantify over them
    val tIdentity = invariant(tID)(t => Equals(t, t))
    assert(wellFormed(Seq(refined(tID, tIdentity)), Seq(tIdentity)))
    // a sort that holds T can quantify over T, which doesn't depend on it
    val dID = FreshIdentifier("D")
    val dInv = invariant(dID)(_ => forall("t" :: T(tID)())(_ => E(true)))
    val tPlain = mkSort(tID)() { _ => Seq((FreshIdentifier("T"), Seq(ValDef(FreshIdentifier("x"), IntegerType())))) }
    assert(wellFormed(Seq(refined(dID, dInv, Some(T(tID)())), tPlain), Seq(dInv)))

    // an uninterpreted call stands for some value of its type, as Stainless's `choose` does:
    // case class T(x: BigInt) { require(choose((t: T) => true) != this) }
    val tChoose = invariant(tID)(t => Not(Equals(UninterpretedCall(FreshIdentifier("choose"), Seq(), Seq(), FunctionType(Seq(), T(tID)())), t)))
    assert(!wellFormed(Seq(refined(tID, tChoose)), Seq(tChoose)))
    // also in a function that the invariant calls, as for the body of an abstract function
    val some = mkFunDef(FreshIdentifier("some"))() { _ =>
      (Seq(), T(tID)(), { case Seq() => UninterpretedCall(FreshIdentifier("some"), Seq(), Seq(), FunctionType(Seq(), T(tID)())) })
    }
    val tSome = invariant(tID)(t => Not(Equals(FunctionInvocation(some.id, Seq(), Seq()), t)))
    assert(!wellFormed(Seq(refined(tID, tSome)), Seq(tSome, some)))
    // and over other values, it is fine
    val tInt = invariant(tID)(t => Equals(UninterpretedCall(FreshIdentifier("n"), Seq(), Seq(), FunctionType(Seq(), IntegerType())), E(BigInt(0))))
    assert(wellFormed(Seq(refined(tID, tInt)), Seq(tInt)))
  }

  test("Field refinements can't quantify over values that depend on their sort") {
    // a sort `id` with a field `x: BigInt` and a field `y: { v: BigInt | pred(v) }`
    val sel = FreshIdentifier("x")
    def withField(id: Identifier, consId: Identifier, pred: Variable => Expr): ADTSort = {
      val v = Variable.fresh("v", IntegerType())
      mkSort(id)() { _ =>
        Seq((consId, Seq(ValDef(sel, IntegerType()),
          ValDef(FreshIdentifier("y"), RefinementType(v.toVal, pred(v))))))
      }
    }
    def wellFormed(sorts: Seq[ADTSort], functions: Seq[FunDef]): Boolean =
      scala.util.Try(NoSymbols.withSorts(sorts).withFunctions(functions).ensureWellFormed).isSuccess

    // case class T(x: BigInt, y: { v: BigInt | forall((t: T) => t.x != v) })
    val tID = FreshIdentifier("T")
    val tCons = FreshIdentifier("T")
    val paradox = withField(tID, tCons, v => forall("t" :: T(tID)())(t => Not(Equals(t.getField(sel), v))))
    val ex = intercept[NotWellFormedException](NoSymbols.withSorts(Seq(paradox)).ensureWellFormed)
    assert(ex.getMessage.contains("the refinement of one of its field types quantifies over the values of"))

    // the same, through a function that the refinement calls
    val none = mkFunDef(FreshIdentifier("none"))() { _ =>
      (Seq("n" :: IntegerType()), BooleanType(), { case Seq(n) => forall("t" :: T(tID)())(_ => E(false)) })
    }
    assert(!wellFormed(Seq(withField(tID, tCons, v => FunctionInvocation(none.id, Seq(), Seq(v)))), Seq(none)))
    // through a choice
    def some(name: String) = UninterpretedCall(FreshIdentifier(name), Seq(), Seq(), FunctionType(Seq(), T(tID)()))
    assert(!wellFormed(Seq(withField(tID, tCons, _ => Equals(some("choose"), some("other")))), Seq()))
    // and through another sort whose field refinement quantifies over it
    val aID = FreshIdentifier("A")
    val bID = FreshIdentifier("B")
    val a = withField(aID, FreshIdentifier("A"), _ => forall("b" :: T(bID)())(_ => E(false)))
    val b = withField(bID, FreshIdentifier("B"), _ => Not(forall("a" :: T(aID)())(_ => E(false))))
    assert(!wellFormed(Seq(a, b), Seq()))

    // refinements that only inspect the field are fine
    assert(wellFormed(Seq(withField(tID, tCons, v => GreaterEquals(v, E(BigInt(0))))), Seq()))
    // as are quantifiers over other values
    assert(wellFormed(Seq(withField(tID, tCons, v => forall("n" :: IntegerType())(n => Equals(n, n)))), Seq()))
  }

  test("Sorts can't recurse through larger instances of themselves") {
    def wellFormed(sorts: ADTSort*): Boolean = scala.util.Try(NoSymbols.withSorts(sorts).ensureWellFormed).isSuccess

    val listID = FreshIdentifier("List")
    val list = mkSort(listID)("X") { case Seq(x) => Seq(
      (FreshIdentifier("Nil"), Seq()),
      (FreshIdentifier("Cons"), Seq(ValDef(FreshIdentifier("h"), x), ValDef(FreshIdentifier("t"), T(listID)(x)))))
    }
    def nested(id: Identifier)(field: TypeParameter => Type): ADTSort = mkSort(id)("A") { case Seq(a) => Seq(
      (FreshIdentifier("Leaf"), Seq(ValDef(FreshIdentifier("a"), a))),
      (FreshIdentifier("Node"), Seq(ValDef(FreshIdentifier("n"), field(a)))))
    }

    // Nest[A] = Leaf(a: A) | Node(n: Nest[List[A]])
    val nestID = FreshIdentifier("Nest")
    val ex = intercept[NotWellFormedException](
      NoSymbols.withSorts(Seq(list, nested(nestID)(a => T(nestID)(T(listID)(a))))).ensureWellFormed)
    assert(ex.getMessage.contains("it recurses through larger instances of itself"))
    // the same, under a function, a tuple and another sort
    assert(!wellFormed(list, nested(nestID)(a => FunctionType(Seq(IntegerType()), T(nestID)(TupleType(Seq(a, a)))))))
    assert(!wellFormed(list, nested(nestID)(a => T(listID)(T(nestID)(T(listID)(a))))))
    // and in the bound variables of dependent types
    def bound(tpe: Type) = ValDef.fresh("x", tpe)
    def nestOfList(a: TypeParameter) = T(nestID)(T(listID)(a))
    assert(!wellFormed(list, nested(nestID)(a => RefinementType(bound(nestOfList(a)), BooleanLiteral(true)))))
    assert(!wellFormed(list, nested(nestID)(a => SigmaType(Seq(bound(nestOfList(a))), IntegerType()))))
    assert(!wellFormed(list, nested(nestID)(a => PiType(Seq(bound(IntegerType())), nestOfList(a)))))
    assert(!wellFormed(list, nested(nestID)(a => T(listID)(RefinementType(bound(nestOfList(a)), BooleanLiteral(true))))))
    // and through another sort that recurses with it
    val otherID = FreshIdentifier("Other")
    val other = mkSort(otherID)("B") { case Seq(b) => Seq((FreshIdentifier("Other"), Seq(ValDef(FreshIdentifier("o"), T(nestID)(T(listID)(b)))))) }
    assert(!wellFormed(list, other, nested(nestID)(a => T(otherID)(a))))

    // uniform recursion, also through other sorts, is fine
    assert(wellFormed(list, nested(nestID)(a => T(listID)(T(nestID)(a)))))
    assert(wellFormed(list, nested(nestID)(a => T(nestID)(a))))
    assert(wellFormed(list, nested(nestID)(a => RefinementType(bound(T(nestID)(a)), BooleanLiteral(true)))))
    // as are larger instances of other sorts, and other instances that don't grow
    assert(wellFormed(list, nested(nestID)(a => T(listID)(T(listID)(a)))))
    assert(wellFormed(list, nested(nestID)(_ => T(nestID)(IntegerType()))))
    // and swapped type parameters
    val pairID = FreshIdentifier("Pair")
    val pair = mkSort(pairID)("A", "B") { case Seq(a, b) => Seq(
      (FreshIdentifier("End"), Seq()),
      (FreshIdentifier("Swap"), Seq(ValDef(FreshIdentifier("a"), a), ValDef(FreshIdentifier("p"), T(pairID)(b, a)))))
    }
    assert(wellFormed(pair))
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
    assert(typed.flags == Seq(Annotation("sort", Seq(at(IntegerType())))))
    val v = Variable.fresh("v", tp)
    assert(typed.instantiate(v).getType == IntegerType())
    val tcons = typed.constructors.head
    assert(tcons.fields.head.flags == Seq(Annotation("field", Seq(at(IntegerType()), IntegerLiteral(1)))))
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
    assert(typed.flags == Seq(Annotation("fun", Seq(at(IntegerType())))))
    assert(typed.params.head.flags == Seq(Annotation("param", Seq(at(IntegerType())))))
    assert(typed.getTpe(stripRefinements = false) == IntegerType())
    assert(typed.instantiate(Annotation("f", Seq(at(idFd.tparams.head.tp)))) == Annotation("f", Seq(at(IntegerType()))))
    assert(box.typed(Seq(BooleanType())).instantiate(Annotation("s", Seq(at(tp)))) == Annotation("s", Seq(at(BooleanType()))))
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
