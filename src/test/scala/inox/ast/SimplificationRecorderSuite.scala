/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package ast

import org.scalatest.funsuite.AnyFunSuite

/** The steps that the simplifiers record of what they do (see [[SymbolOps.SimplificationRecorder]]),
  * which certificates give for their checker to check. */
class SimplificationRecorderSuite extends AnyFunSuite with DatastructureUtils {
  import inox.trees._
  import inox.trees.dsl._

  val incID = FreshIdentifier("inc")
  val n = ValDef.fresh("n", IntegerType())
  val inc = new FunDef(incID, Seq(), Seq(n), IntegerType(), Plus(n.toVariable, IntegerLiteral(1)), Seq())
  // a constant of the program
  val onesID = FreshIdentifier("ones")
  val intList = T(listID)(IntegerType())
  val ones = new FunDef(onesID, Seq(), Seq(), intList,
    ADT(consID, Seq(IntegerType()), Seq(IntegerLiteral(1), ADT(nilID, Seq(IntegerType()), Seq()))), Seq())
  // a function with a quantifier, which is inlined
  val increasesID = FreshIdentifier("increases")
  val (m, k) = (ValDef.fresh("m", IntegerType()), ValDef.fresh("k", IntegerType()))
  val increases = new FunDef(increasesID, Seq(), Seq(m), BooleanType(),
    Forall(Seq(k), GreaterThan(Plus(k.toVariable, IntegerLiteral(1)), m.toVariable)), Seq())

  // a function with a postcondition
  val postID = FreshIdentifier("post")
  val (pa, pr) = (ValDef.fresh("a", IntegerType()), ValDef.fresh("res", IntegerType()))
  val post = new FunDef(postID, Seq(), Seq(pa), IntegerType(),
    Let(pr, FunctionInvocation(incID, Seq(), Seq(pa.toVariable)), Assume(GreaterThan(FunctionInvocation(incID, Seq(), Seq(pa.toVariable)), pr.toVariable), pr.toVariable)), Seq())
  // a constant that is a function
  val idfID = FreshIdentifier("idf")
  val idf = new FunDef(idfID, Seq(), Seq(), FunctionType(Seq(IntegerType()), IntegerType()), Lambda(Seq(n), n.toVariable), Seq())
  // a sort with an equality, which quantifies
  val (wrapID, wrapConsID, wrapEqID, unwrap) = (FreshIdentifier("Wrap"), FreshIdentifier("Wrap"), FreshIdentifier("wrapEq"), FreshIdentifier("unwrap"))
  val wrap = new ADTSort(wrapID, Seq(), Seq(new ADTConstructor(wrapConsID, wrapID, Seq(ValDef(unwrap, IntegerType())))), Seq(HasADTEquality(wrapEqID)))
  val (wa, wb, wk) = (ValDef.fresh("a", ADTType(wrapID, Seq())), ValDef.fresh("b", ADTType(wrapID, Seq())), ValDef.fresh("k", IntegerType()))
  val wrapEq = new FunDef(wrapEqID, Seq(), Seq(wa, wb), BooleanType(),
    Forall(Seq(wk), Equals(GreaterThan(ADTSelector(wa.toVariable, unwrap), wk.toVariable), GreaterThan(ADTSelector(wb.toVariable, unwrap), wk.toVariable))), Seq())

  given symbols: Symbols = baseSymbols.withSorts(Seq(wrap)).withFunctions(Seq(inc, ones, increases, post, idf, wrapEq))
  import symbols._

  given ctx: Context = TestContext.empty
  given sem: symbols.Semantics = InoxProgram(symbols).getSemantics.asInstanceOf[symbols.Semantics]
  given PrinterOptions = PrinterOptions(symbols = Some(symbols))

  val x = Variable.fresh("x", IntegerType())
  val y = Variable.fresh("y", IntegerType())
  // the variables that the tests quantify over
  val i = Variable.fresh("i", IntegerType())
  val j = Variable.fresh("j", IntegerType())
  val p = Variable.fresh("p", BooleanType())
  val q = Variable.fresh("q", BooleanType())
  val r = Variable.fresh("r", BooleanType())
  val l = Variable.fresh("l", intList)
  val w = Variable.fresh("w", Int32Type())

  def cons(h: Expr, t: Expr): Expr = ADT(consID, Seq(IntegerType()), Seq(h, t))
  val nil: Expr = ADT(nilID, Seq(IntegerType()), Seq())

  // values of the variables, under which the terms of the steps are evaluated
  val models: Seq[Map[ValDef, Expr]] = for (bp <- Seq(true, false); bq <- Seq(true, false); i <- Seq(-1, 0, 2)) yield Map[ValDef, Expr](
    x.toVal -> IntegerLiteral(i), y.toVal -> IntegerLiteral(1 - i), p.toVal -> BooleanLiteral(bp), q.toVal -> BooleanLiteral(bq),
    r.toVal -> BooleanLiteral(bp != bq), l.toVal -> (if (bq) cons(IntegerLiteral(i), nil) else nil), w.toVal -> Int32Literal(i))

  /** The rules of the steps of the simplification of `e`, which lead to what `e` simplifies
    * into without them, and whose terms have the value of `e` wherever it has one. */
  def rules(e: Expr): Seq[String] = {
    val (res, steps) = simplifyFormulaRecorded(e)
    assert(steps.isEmpty == (res == e), s"the steps of $e to $res are ${steps.mkString(", ")}")
    assert(steps.lastOption.forall(_._2 == res), s"the steps of $e don't end at $res")
    assert(sameUpToLocals(res, simplifyFormula(e)), s"$e simplifies into something else when its steps are recorded")
    for ((rule, term) <- steps) assert(term.getType == e.getType, s"the step $rule of $e gives $term, of another type")

    val evaluator = sem.getEvaluator
    for (model <- models) {
      def value(term: Expr) = evaluator.eval(exprOps.replaceFromSymbols(model, term)).result
      // an assumption that is lifted out of a quantifier also fails where nothing is quantified over
      val lifted = steps.indexWhere(_._1 == "lift-assumptions")
      for (expected <- value(e); ((rule, term), index) <- steps.zipWithIndex; actual = value(term) if actual.isDefined || lifted < 0 || index < lifted)
        assert(actual == Some(expected), s"the step $rule of $e gives $term, of another value under $model")
    }
    steps.map(_._1)
  }

  def inc(e: Expr): Expr = FunctionInvocation(incID, Seq(), Seq(e))
  def int(i: Int): Expr = IntegerLiteral(i)

  test("No steps are recorded for a term that is not simplified") {
    assert(rules(And(p, q)) == Seq())
    assert(rules(GreaterThan(inc(x), y)) == Seq())
    assert(rules(Forall(Seq(i.toVal), GreaterThan(inc(i), i))) == Seq())
  }

  test("Simplifications of connectives and conditionals are steps of logic") {
    assert(rules(Not(Not(p))) == Seq("logic"))
    assert(rules(IfExpr(p, x, x)) == Seq("logic"))
    assert(rules(And(p, Or(p, q))) == Seq("logic", "logic", "logic"))
    // the condition holds in the first branch
    assert(rules(IfExpr(p, And(p, q), r)) == Seq("logic", "logic"))
    assert(rules(Implies(Equals(x, inc(y)), GreaterThan(x, y))) == Seq("logic"))
  }

  test("Simplifications of integer arithmetic are steps of arith, and the others of fold") {
    assert(rules(GreaterThan(Plus(x, int(0)), y)) == Seq("arith"))
    assert(rules(Equals(Plus(w, Int32Literal(0)), w)) == Seq("fold", "arith"))
    assert(rules(And(p, Equals(StringLiteral("a"), StringLiteral("b")))) == Seq("fold", "logic"))
  }

  test("Selections of fields and of elements are steps of select") {
    assert(rules(ADTSelector(cons(x, nil), head)) == Seq("select"))
    assert(rules(GreaterThan(TupleSelect(Tuple(Seq(x, p)), 1), y)) == Seq("select"))
  }

  test("The other elements of a selection are bound when they have effects") {
    assert(rules(GreaterThan(TupleSelect(Tuple(Seq(x, Division(x, y))), 1), y)) == Seq("bind", "select"))
  }

  test("Bound variables are expanded where their value is selected from") {
    assert(rules(Let(l.toVal, cons(x, nil), GreaterThan(ADTSelector(l, head), int(0)))) == Seq("expand", "select", "logic"))
  }

  test("Reconstructions of a value from its fields or elements are steps of eta and of tuple") {
    assert(rules(Assume(IsConstructor(l, consID), Equals(cons(ADTSelector(l, head), ADTSelector(l, tail)), l))) == Seq("eta", "arith"))
    val t = Variable.fresh("t", TupleType(Seq(IntegerType(), BooleanType())))
    assert(rules(Equals(Tuple(Seq(TupleSelect(t, 1), TupleSelect(t, 2))), t)) == Seq("tuple", "arith"))
  }

  test("Applications of lambdas are steps of beta") {
    assert(rules(GreaterThan(Application(Lambda(Seq(n), Plus(n.toVariable, x)), Seq(y)), x)) == Seq("beta", "logic"))
  }

  test("An assumption on the caller of an application is lifted") {
    val f = Variable.fresh("f", FunctionType(Seq(IntegerType()), IntegerType()))
    assert(rules(GreaterThan(Application(Assume(p, f), Seq(x)), y)) == Seq("lift"))
  }

  test("Constants of the program are unfolded, and ground calls are evaluated") {
    assert(rules(GreaterThan(ADTSelector(FunctionInvocation(onesID, Seq(), Seq()), head), x)) == Seq("unfold"))
    assert(rules(GreaterThan(inc(int(1)), x)) == Seq("evaluate"))
    assert(rules(GreaterThan(Plus(int(1), int(2)), x)) == Seq("evaluate"))
  }

  test("Functions with quantifiers are unfolded where they are called") {
    assert(rules(And(p, FunctionInvocation(increasesID, Seq(), Seq(y)))) == Seq("unfold", "logic", "logic"))
  }

  test("Quantifiers are merged, and their unused variables dropped") {
    assert(rules(Forall(Seq(i.toVal), Forall(Seq(j.toVal), LessThan(i, j)))) == Seq("merge"))
    assert(rules(Forall(Seq(i.toVal, j.toVal), GreaterThan(i, int(0)))) == Seq("unused"))
  }

  test("Variables of types that may be empty are not dropped") {
    val a = Variable.fresh("a", TypeParameter.fresh("T"))
    assert(rules(Forall(Seq(i.toVal, a.toVal), GreaterThan(i, int(0)))) == Seq())
  }

  test("Quantifiers are lifted by steps of prenex, where the checker knows the types to have values") {
    assert(rules(Forall(Seq(i.toVal), And(Forall(Seq(j.toVal), LessThan(i, j)), p))) == Seq("prenex"))
    assert(rules(Forall(Seq(i.toVal), Implies(p, Forall(Seq(j.toVal), LessThan(i, j))))) == Seq("prenex", "logic"))
    // not from the premise of an implication
    assert(rules(Forall(Seq(i.toVal), Implies(Forall(Seq(j.toVal), LessThan(i, j)), p))) == Seq("logic"))

    val tp = TypeParameter.fresh("T")
    val (a, b) = (Variable.fresh("a", tp), Variable.fresh("b", tp))
    val distinct = Forall(Seq(a.toVal), Not(Equals(a, b)))
    // a disjunction holds for all values of a type that has none
    assert(rules(Forall(Seq(i.toVal), Or(distinct, GreaterThan(i, y)))) == Seq("lift-quantifiers"))
    assert(rules(Forall(Seq(i.toVal), And(distinct, GreaterThan(i, y)))) == Seq())
  }

  test("Assumptions are lifted by steps of logic, except out of quantifiers") {
    assert(rules(Assume(p, IfExpr(q, Assume(r, x), y))) == Seq("logic", "logic"))
    assert(rules(Assume(p, Forall(Seq(i.toVal), Assume(q, GreaterThan(i, int(0)))))) == Seq("lift-assumptions"))
  }

  test("A constant that evaluates to itself up to its bound variables is renamed") {
    val f = Variable.fresh("f", FunctionType(Seq(IntegerType()), IntegerType()))
    assert(rules(Equals(FunctionInvocation(idfID, Seq(), Seq()), f)) == Seq("unfold", "rename"))
  }

  test("Unused variables of types that the checker doesn't know to have values are dropped by another rule") {
    val fl = Variable.fresh("fl", Float32Type())
    assert(rules(Forall(Seq(i.toVal, fl.toVal), GreaterThan(i, int(0)))) == Seq("drop-variables"))
  }

  test("Finite sets and maps are built by a step of matchers") {
    assert(rules(ElementOfSet(x, FiniteSet(Seq(x, y), IntegerType()))) == Seq("matchers"))
    assert(rules(Equals(MapApply(FiniteMap(Seq(x -> y), int(0), IntegerType(), IntegerType()), x), y)) == Seq("matchers"))
  }

  test("The postcondition of a call on quantified variables is assumed by a step of inline-postconditions") {
    assert(rules(Forall(Seq(i.toVal), GreaterThan(FunctionInvocation(postID, Seq(), Seq(i)), i))) == Seq("inline-postconditions"))
  }

  test("The equality function of a sort is inlined by a step of inline-equality") {
    val (a, b) = (Variable.fresh("a", T(wrapID)()), Variable.fresh("b", T(wrapID)()))
    // the call is unfolded by steps that the checker knows
    assert(rules(And(p, FunctionInvocation(wrapEqID, Seq(), Seq(a, b)))) == Seq("unfold", "logic", "logic", "logic"))
    // an equality is only inlined where the function is called too
    assert(rules(And(p, Equals(a, b))) == Seq())
    assert(rules(Or(FunctionInvocation(wrapEqID, Seq(), Seq(b, a)), Not(Equals(a, b)))).contains("inline-equality"))
  }
}
