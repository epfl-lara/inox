/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import Feature._

/** Checks the solver-specific parts of the unrolling encoding on every solver.
  *
  * Function calls, lambdas, chooses and quantifiers are encoded by templates, and the template
  * encoding (inox trees or, for `nativez3`, Z3 terms) and the extraction of their values from
  * models depend on the solver. The problems below only need a few unfoldings, so failures point
  * at the solver rather than at the unrolling engine, which `src/it` tests on a single solver.
  */
class TemplateEncodingSuite extends SolverTestSuite with DatastructureUtils {
  override protected def options = Seq(optCheckModels(true))

  import inox.trees.{given, _}
  import inox.trees.dsl.{given, _}
  import SolverResponses.{given, _}

  def int(i: Int): Expr = IntegerLiteral(i)

  val incID = FreshIdentifier("inc")
  val inc = mkFunDef(incID)() { _ => (
    Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) => x + int(1) })
  }

  val incBVID = FreshIdentifier("incBV")
  val incBV = mkFunDef(incBVID)() { _ => (
    Seq("x" :: Int32Type()), Int32Type(), { case Seq(x) => x + E(1) })
  }

  val lengthID = FreshIdentifier("length")
  val length = mkFunDef(lengthID)("A") { case Seq(aT) => (
    Seq("l" :: T(listID)(aT)), IntegerType(), { case Seq(l) =>
      if_ (l `is` consID) {
        int(1) + E(lengthID)(aT)(l.getField(tail))
      } else_ {
        int(0)
      }
    })
  }

  val greaterID = FreshIdentifier("greater")
  val greater = mkFunDef(greaterID)() { _ => (
    Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) =>
      choose("v" :: IntegerType())(v => v > x)
    })
  }

  override protected def symbols: Symbols = baseSymbols.withFunctions(Seq(inc, incBV, length, greater))
  given Symbols = symbols

  // Countermodels of quantified formulas can't be checked by evaluation
  def withoutModelChecks(ctx: Context): Context = ctx.withOpts(optCheckModels(false))

  def model(s: SimpleSolverAPI { val program: InoxProgram }, clause: Expr) =
    s.solveSAT(clause) match {
      case SatWithModel(model) => model
      case res => fail(s"Expected a model for ${clause.asString} but got $res")
    }

  test("Non-recursive function call", Integers) { ctx =>
    val s = solver(ctx)
    val x = Variable.fresh("x", IntegerType())
    assert(model(s, Equals(inc(x), int(5))).vars.get(x.toVal) == Some(int(4)))
    assert(s.solveVALID(Equals(inc(inc(x)), x + int(2))) contains true)
  }

  test("Function call over bit-vectors") { ctx =>
    val s = solver(ctx)
    val x = Variable.fresh("x", Int32Type())
    assert(model(s, Equals(incBV(x), E(5))).vars.get(x.toVal) == Some(Int32Literal(4)))
    assert(s.solveVALID(Equals(incBV(incBV(x)), x + E(2))) contains true)
  }

  test("Recursive function over ADTs", Integers, ADTs) { ctx =>
    val s = solver(ctx)
    val l = Variable.fresh("l", T(listID)(IntegerType()))
    val value = model(s, Equals(length(IntegerType())(l), int(2))).vars(l.toVal)
    assert(value match {
      case ADT(`consID`, _, Seq(_, ADT(`consID`, _, Seq(_, ADT(`nilID`, _, _))))) => true
      case _ => false
    }, s"Expected a list of length 2 but got ${value.asString}")
  }

  test("Lambdas in models", Integers, Functions) { ctx =>
    val s = solver(ctx)
    val f = Variable.fresh("f", FunctionType(Seq(IntegerType()), IntegerType()))
    val m = model(s, Equals(f(int(1)), int(2)) && Equals(f(int(2)), int(3)))
    val value = m.vars(f.toVal)
    assert(value.isInstanceOf[Lambda], s"Expected a lambda but got ${value.asString}")
    val ev = program.getEvaluator(ctx)
    for ((arg, res) <- Seq(1 -> 2, 2 -> 3)) {
      assert(ev.eval(Application(value, Seq(int(arg)))).result == Some(int(res)))
    }
  }

  test("Function equality", Integers, Functions) { ctx =>
    val s = solver(ctx)
    val f = Variable.fresh("f", FunctionType(Seq(IntegerType()), IntegerType()))
    val succ = \("x" :: IntegerType())(x => x + int(1))
    assert(s.solveVALID(Equals(f, succ) ==> Equals(f(int(1)), int(2))) contains true)
    assert(s.solveVALID(Equals(f, succ) ==> Equals(f(int(1)), int(1))) contains false)
  }

  test("Choose in function", Integers) { ctx =>
    val s = solver(ctx)
    val x = Variable.fresh("x", IntegerType())
    assert(s.solveVALID(greater(x) > x) contains true)
    model(s, Equals(greater(int(10)), int(42)))
  }

  test("Quantified assumption", Integers, Functions, Quantifiers) { ctx =>
    val s = solver(withoutModelChecks(ctx))
    val f = Variable.fresh("f", FunctionType(Seq(IntegerType()), IntegerType()))
    val x = Variable.fresh("x", IntegerType())
    val pos = Forall(Seq(x.toVal), f(x) > int(0))
    assert(s.solveVALID(pos ==> (f(int(3)) > int(0))) contains true)
    // countermodels of universally quantified formulas are out of reach, so this is unknown
    assert(!(s.solveVALID(pos ==> (f(int(3)) > int(1))) contains true))
  }

  test("Refinement types in quantifiers", Integers, Functions, Quantifiers) { ctx =>
    val s = solver(withoutModelChecks(ctx))

    val f = Variable.fresh("f", FunctionType(Seq(IntegerType()), IntegerType()))
    val y = Variable.fresh("y", IntegerType())
    val nonZero = RefinementType(y.toVal, Not(Equals(y, IntegerLiteral(0))))
    val z = Variable.fresh("z", nonZero)

    // the refinement restricts the quantification domain
    assert(s.solveVALID(Forall(Seq(z.toVal), Not(Equals(z, IntegerLiteral(0))))) contains true)
    assert(s.solveVALID(Implies(
      Forall(Seq(z.toVal), Equals(Application(f, Seq(z)), IntegerLiteral(1))),
      Equals(Application(f, Seq(IntegerLiteral(1))), IntegerLiteral(1))
    )) contains true)
    assert(s.solveVALID(Implies(
      Forall(Seq(z.toVal), Equals(Application(f, Seq(z)), IntegerLiteral(1))),
      Equals(Application(f, Seq(IntegerLiteral(0))), IntegerLiteral(1))
    )) contains false)

    // A refinement predicate that only holds (here, that only makes its assumptions)
    // within its base type must not be asserted for values outside of the base type:
    // instantiating the quantifier with 0 must simply make the type check false.
    val x = Variable.fresh("x", nonZero)
    val guarded = RefinementType(x.toVal, Assume(Not(Equals(x, IntegerLiteral(0))), BooleanLiteral(true)))
    val w = Variable.fresh("w", guarded)
    assert(s.solveVALID(Implies(
      Forall(Seq(w.toVal), Equals(Application(f, Seq(w)), IntegerLiteral(1))),
      Equals(Application(f, Seq(IntegerLiteral(0))), IntegerLiteral(1))
    )) contains false)
    assert(s.solveVALID(Implies(
      Forall(Seq(w.toVal), Equals(Application(f, Seq(w)), IntegerLiteral(1))),
      Equals(Application(f, Seq(IntegerLiteral(2))), IntegerLiteral(1))
    )) contains true)
  }

  test("Refinement predicate calling a function with an assumption", Integers, Functions, Quantifiers) { ctx =>
    // As above, but the assumption comes from a function called in the predicate,
    // similarly to a Stainless `require`. Unrolling `pre(0)` must only falsify the
    // type check of the instantiation, not the whole instantiation.
    val a = ValDef.fresh("a", IntegerType())
    val pre = new FunDef(FreshIdentifier("pre"), Seq(), Seq(a), BooleanType(),
      Assume(Not(Equals(a.toVariable, IntegerLiteral(0))), BooleanLiteral(true)), Seq())

    val p = InoxProgram(NoSymbols.withFunctions(Seq(pre)))
    import p.trees._
    val s = SimpleSolverAPI(p.getSolver(withoutModelChecks(ctx)))

    val f = Variable.fresh("f", FunctionType(Seq(IntegerType()), IntegerType()))
    val y = Variable.fresh("y", IntegerType())
    val nonZero = RefinementType(y.toVal, Not(Equals(y, IntegerLiteral(0))))
    val x = Variable.fresh("x", nonZero)
    val guarded = RefinementType(x.toVal, FunctionInvocation(pre.id, Seq(), Seq(x)))
    val w = Variable.fresh("w", guarded)

    assert(s.solveVALID(Implies(
      Forall(Seq(w.toVal), Equals(Application(f, Seq(w)), IntegerLiteral(1))),
      Equals(Application(f, Seq(IntegerLiteral(0))), IntegerLiteral(1))
    )) contains false)
    assert(s.solveVALID(Implies(
      Forall(Seq(w.toVal), Equals(Application(f, Seq(w)), IntegerLiteral(1))),
      Equals(Application(f, Seq(IntegerLiteral(2))), IntegerLiteral(1))
    )) contains true)
  }

  test("Choose inside quantifier", Integers, Quantifiers) { ctx =>
    // The `choose` must be in a function body to be handled by the ChooseEncoder.
    val x = Variable.fresh("x", IntegerType())
    val y = ValDef.fresh("y", IntegerType())
    val succ = Plus(x, IntegerLiteral(1))
    val fd = new FunDef(FreshIdentifier("chooseInForall"), Seq(), Seq(), BooleanType(),
      Forall(Seq(x.toVal), Equals(Choose(y, Equals(y.toVariable, succ)), succ)), Seq())

    val p = InoxProgram(NoSymbols.withFunctions(Seq(fd)))
    val s = SimpleSolverAPI(p.getSolver(withoutModelChecks(ctx)))
    assert(s.solveVALID(p.trees.FunctionInvocation(fd.id, Seq(), Seq())) contains true)
  }
}
