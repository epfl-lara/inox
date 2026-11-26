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
  // a recursive function with a quantifier, which is not inlined
  val everID = FreshIdentifier("ever")
  val (em, ek) = (ValDef.fresh("m", IntegerType()), ValDef.fresh("k", IntegerType()))
  val ever = new FunDef(everID, Seq(), Seq(em), BooleanType(),
    And(Forall(Seq(ek), GreaterThan(Plus(ek.toVariable, IntegerLiteral(1)), em.toVariable)),
      FunctionInvocation(everID, Seq(), Seq(Plus(em.toVariable, IntegerLiteral(1))))), Seq())
  // a function that calls one with a quantifier, and has none itself
  val callsID = FreshIdentifier("calls")
  val cm = ValDef.fresh("m", IntegerType())
  val calls = new FunDef(callsID, Seq(), Seq(cm), BooleanType(),
    FunctionInvocation(increasesID, Seq(), Seq(Plus(cm.toVariable, IntegerLiteral(1)))), Seq())
  // a function with a quantifier under an assumption, which is inlined
  val boundedID = FreshIdentifier("bounded")
  val (bm, bk) = (ValDef.fresh("m", IntegerType()), ValDef.fresh("k", IntegerType()))
  val bounded = new FunDef(boundedID, Seq(), Seq(bm), BooleanType(),
    Assume(GreaterThan(bm.toVariable, IntegerLiteral(0)), Forall(Seq(bk), GreaterThan(Plus(bk.toVariable, bm.toVariable), bk.toVariable))), Seq())

  // a recursive function, which terminates
  val downID = FreshIdentifier("down")
  val dm = ValDef.fresh("m", IntegerType())
  val downDef = new FunDef(downID, Seq(), Seq(dm), IntegerType(),
    IfExpr(LessEquals(dm.toVariable, IntegerLiteral(0)), IntegerLiteral(0),
      FunctionInvocation(downID, Seq(), Seq(Minus(dm.toVariable, IntegerLiteral(1))))), Seq())
  // a constant that is a function, which calls it again
  val againID = FreshIdentifier("again")
  val am = ValDef.fresh("m", IntegerType())
  val againDef = new FunDef(againID, Seq(), Seq(), FunctionType(Seq(IntegerType()), IntegerType()),
    Lambda(Seq(am), Application(FunctionInvocation(againID, Seq(), Seq()), Seq(am.toVariable))), Seq())
  // a constant that is a function
  val idfID = FreshIdentifier("idf")
  val idf = new FunDef(idfID, Seq(), Seq(), FunctionType(Seq(IntegerType()), IntegerType()), Lambda(Seq(n), n.toVariable), Seq())
  // a sort with an equality, which quantifies
  val (wrapID, wrapConsID, wrapEqID, unwrap) = (FreshIdentifier("Wrap"), FreshIdentifier("Wrap"), FreshIdentifier("wrapEq"), FreshIdentifier("unwrap"))
  val wrap = new ADTSort(wrapID, Seq(), Seq(new ADTConstructor(wrapConsID, wrapID, Seq(ValDef(unwrap, IntegerType())))), Seq(HasADTEquality(wrapEqID)))
  val (wa, wb, wk) = (ValDef.fresh("a", ADTType(wrapID, Seq())), ValDef.fresh("b", ADTType(wrapID, Seq())), ValDef.fresh("k", IntegerType()))
  val wrapEq = new FunDef(wrapEqID, Seq(), Seq(wa, wb), BooleanType(),
    Forall(Seq(wk), Equals(GreaterThan(ADTSelector(wa.toVariable, unwrap), wk.toVariable), GreaterThan(ADTSelector(wb.toVariable, unwrap), wk.toVariable))), Seq())

  given symbols: Symbols = baseSymbols.withSorts(Seq(wrap)).withFunctions(Seq(inc, ones, increases, ever, calls, bounded, idf, wrapEq, downDef, againDef))
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
  def down(e: Expr): Expr = FunctionInvocation(downID, Seq(), Seq(e))
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
    assert(rules(GreaterThan(ADTSelector(FunctionInvocation(onesID, Seq(), Seq()), head), x)) == Seq("unfold", "select"))
    assert(rules(GreaterThan(inc(int(1)), x)) == Seq("evaluate"))
    assert(rules(GreaterThan(Plus(int(1), int(2)), x)) == Seq("evaluate"))
  }

  test("The values of ground terms are simplified with, in the same traversal") {
    // the condition is evaluated, and its conditional is then one of its branches
    assert(simplifyFormula(IfExpr(GreaterThan(inc(int(1)), int(1)), p, q)) == p)
    assert(rules(IfExpr(GreaterThan(inc(int(1)), int(1)), p, q)) == Seq("evaluate", "evaluate", "logic"))
    assert(simplifyFormula(And(Equals(x, int(3)), LessThan(inc(int(1)), int(1)))) == BooleanLiteral(false))
    assert(simplifyFormula(Or(Equals(x, int(3)), LessThan(inc(int(1)), int(1)))) == Equals(x, int(3)))
  }

  test("The ground terms that an inlined binding leaves are evaluated") {
    assert(simplifyFormula(Let(n, int(42), GreaterThan(Times(n.toVariable, n.toVariable), x))) == GreaterThan(int(1764), x))
    assert(rules(Let(n, int(42), GreaterThan(Times(n.toVariable, n.toVariable), x))) == Seq("logic", "evaluate"))
  }

  test("The value of the term of a binding is simplified with in its body") {
    val bound = Let(n, inc(int(1)), GreaterThan(Times(n.toVariable, n.toVariable), x))
    assert(simplifyFormula(bound) == GreaterThan(int(4), x))
    rules(bound)
  }

  test("In a lambda, a ground term is evaluated if its operations are pure whatever their operands") {
    val f = Variable.fresh("f", FunctionType(Seq(IntegerType()), IntegerType()))
    def fun(e: Expr): Expr = Lambda(Seq(n), Plus(n.toVariable, e))
    // whether or not the lambda is ground
    assert(simplifyFormula(Equals(f, fun(inc(int(1))))) == Equals(f, fun(int(2))))
    assert(simplifyFormula(Equals(f, fun(Plus(x, inc(int(1)))))) == Equals(f, fun(Plus(x, int(2)))))
    // a division is not pure for any divisor, and stays as it is written
    assert(simplifyFormula(Equals(f, fun(Division(int(10), int(2))))) == Equals(f, fun(Division(int(10), int(2)))))
    assert(simplifyFormula(GreaterThan(Division(int(10), int(2)), x)) == GreaterThan(int(5), x))
    // a recursive function is not pure unless it is checked to terminate
    assert(simplifyFormula(Equals(f, fun(down(int(3))))) == Equals(f, fun(down(int(3)))))
    // the value of a function whose recursion is in a lambda calls it again
    val again = Lambda(Seq(n), Application(FunctionInvocation(againID, Seq(), Seq()), Seq(n.toVariable)))
    assert(simplifyFormula(Equals(f, again)) == Equals(f, again))
  }

  test("Functions with quantifiers are unfolded where they are called") {
    def increases(e: Expr): Expr = FunctionInvocation(increasesID, Seq(), Seq(e))
    def called(e: Expr): Boolean = exprOps.exists { case _: FunctionInvocation => true case _ => false } (simplifyFormula(e))
    assert(rules(And(p, increases(y))) == Seq("unfold", "logic", "logic"))
    // wherever the call is: under a negation, in a branch, a quantifier, a lambda that is applied
    assert(!called(Not(increases(y))))
    assert(!called(IfExpr(p, increases(x), increases(y))))
    assert(!called(Forall(Seq(i.toVal), Or(GreaterThan(i, y), increases(i)))))
    assert(!called(Application(Lambda(Seq(i.toVal), increases(i)), Seq(y))))
    assert(rules(Forall(Seq(i.toVal), Or(GreaterThan(i, y), increases(i)))).contains("unfold"))
    // the call of an inlined function may bring another one
    assert(!called(And(p, increases(Plus(x, y)))) && !called(Or(increases(x), increases(y))))
  }

  test("Only the functions with quantifiers that are not recursive are unfolded") {
    val recursive = And(p, FunctionInvocation(everID, Seq(), Seq(y)))
    assert(rules(recursive) == Seq() && simplifyFormula(recursive) == recursive)
    // a function without a quantifier is not, even if it calls one that has one
    val indirect = And(p, FunctionInvocation(callsID, Seq(), Seq(y)))
    assert(rules(indirect) == Seq() && simplifyFormula(indirect) == indirect)
    val none = And(p, GreaterThan(inc(x), y))
    assert(rules(none) == Seq() && simplifyFormula(none) == none)
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
    assert(rules(Forall(Seq(i.toVal), Implies(p, Forall(Seq(j.toVal), LessThan(i, j))))) == Seq("logic", "prenex"))
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

  test("Assumptions under assumptions are merged, in their predicates and in their bodies") {
    assert(simplifyFormula(Assume(p, Assume(q, x))) == Assume(And(p, q), x))
    assert(simplifyFormula(Assume(Assume(p, q), x)) == Assume(And(p, q), x))
    assert(simplifyFormula(Assume(p, Plus(Assume(q, x), Assume(r, y)))) == Assume(And(Seq(p, q, r)), Plus(x, y)))
    assert(rules(Assume(p, Assume(q, x))) == Seq("logic"))
    // an assumption that the lifted ones make true is dropped
    assert(simplifyFormula(Assume(p, Plus(Assume(p, x), y))) == Assume(p, Plus(x, y)))
  }

  test("The assumptions of an inlined function are lifted into the assumption around its call") {
    val e = Assume(p, FunctionInvocation(boundedID, Seq(), Seq(x)))
    assert(rules(e) == Seq("unfold", "logic", "logic", "logic"))
    simplifyFormula(e) match {
      case Assume(And(Seq(`p`, GreaterThan(`x`, IntegerLiteral(zero)))), _: Forall) => assert(zero == 0)
      case res => fail(s"$e simplifies into $res")
    }
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

  test("The equality function of a sort is inlined where it is called, and its equalities are kept") {
    val (a, b) = (Variable.fresh("a", T(wrapID)()), Variable.fresh("b", T(wrapID)()))
    // the call is unfolded by steps that the checker knows
    assert(rules(And(p, FunctionInvocation(wrapEqID, Seq(), Seq(a, b)))) == Seq("unfold", "logic", "logic", "logic"))
    // an equality stays one, also where the function is called
    assert(rules(And(p, Equals(a, b))) == Seq())
    val both = Or(FunctionInvocation(wrapEqID, Seq(), Seq(b, a)), Not(Equals(a, b)))
    assert(exprOps.exists { case Equals(`a`, `b`) => true case _ => false } (simplifyFormula(both)))
    assert(!exprOps.exists { case fi: FunctionInvocation => true case _ => false } (simplifyFormula(both)))
  }

  test("The elements of tuples are simplified, and their sets built by a step of matchers") {
    val t = Variable.fresh("t", TupleType(Seq(SetType(IntegerType()), BooleanType())))
    val e = Equals(Tuple(Seq(FiniteSet(Seq(x, y), IntegerType()), Implies(p, q))), t)
    assert(rules(e) == Seq("matchers", "logic"))
    assert(simplifyFormula(e) == Equals(Tuple(Seq(SetAdd(SetAdd(FiniteSet(Seq(), IntegerType()), x), y), Or(Not(p), q))), t))
  }

  test("Lambdas that are bound around quantifiers are applied by steps of beta") {
    val f = ValDef.fresh("f", FunctionType(Seq(IntegerType()), IntegerType()))
    val e = Let(f, Lambda(Seq(n), Plus(n.toVariable, x)), And(Forall(Seq(i.toVal), GreaterThan(Application(f.toVariable, Seq(i)), y)), GreaterThan(Application(f.toVariable, Seq(y)), x)))
    assert(rules(e) == Seq("expand", "beta", "logic", "expand", "beta", "logic", "logic"))
    assert(simplifyFormula(e) == And(Forall(Seq(i.toVal), GreaterThan(Plus(i, x), y)), GreaterThan(Plus(y, x), x)))
  }
}
