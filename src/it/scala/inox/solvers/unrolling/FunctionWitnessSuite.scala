/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import SolverResponses._
import evaluators.EvaluationResults

/** Checks that distinct first-class functions in models have a distinguishing input.
  *
  * @see [[LambdaTemplates.witnessAssumptions]]
  */
class FunctionWitnessSuite extends UnrollingTestSuite {
  import inox.trees._
  import dsl._

  override protected def optionMatrix = UnrollingTestSuite.combinations(
    // most tests compare functions, which the default semantics rejects
    Seq(optFunctionEquality(FunctionEquality.Intensional)),
    Seq(optCheckModels(true)),
    Seq(optModelFinding(0), optModelFinding(1))
  )

  override def optionsString(options: Options): String =
    "solvr=" + options.findOptionOrDefault(optSelectedSolvers).head + " " +
    "model=" + options.findOptionOrDefault(optModelFinding)

  val listID = FreshIdentifier("List")
  val consID = FreshIdentifier("Cons")
  val nilID  = FreshIdentifier("Nil")
  val head = FreshIdentifier("head")
  val tail = FreshIdentifier("tail")

  val List = mkSort(listID)("A") {
    case Seq(aT) => Seq(
      (nilID, Seq()),
      (consID, Seq(ValDef(head, aT), ValDef(tail, T(listID)(aT))))
    )
  }

  val sizeID = FreshIdentifier("size")
  val sizeFd = mkFunDef(sizeID)("A") { case Seq(aT) => (
    Seq("l" :: T(listID)(aT)), IntegerType(), { case Seq(l) =>
      if_ (l `is` consID) {
        E(BigInt(1)) + E(sizeID)(aT)(l.getField(tail))
      } else_ {
        E(BigInt(0))
      }
    })
  }

  val boxID = FreshIdentifier("Box")
  val boxConsID = FreshIdentifier("MkBox")
  val fn = FreshIdentifier("fn")

  val Box = mkSort(boxID)() {
    case Seq() => Seq((boxConsID, Seq(ValDef(fn, IntegerType() =>: IntegerType()))))
  }

  // a recursive type with function fields, like Stainless's encoding of `Object`
  val objID = FreshIdentifier("Obj")
  val funID = FreshIdentifier("Fun")
  val numID = FreshIdentifier("Num")
  val objFn = FreshIdentifier("objFn")
  val objNum = FreshIdentifier("objNum")

  val Obj = mkSort(objID)() {
    case Seq() => Seq(
      (funID, Seq(ValDef(objFn, T(objID)() =>: T(objID)()))),
      (numID, Seq(ValDef(objNum, IntegerType())))
    )
  }

  val program = InoxProgram(new Symbols(Map(sizeID -> sizeFd), Map(listID -> List, boxID -> Box, objID -> Obj)))

  val intList = T(listID)(IntegerType())

  private def solve(clause: Expr)(using Context): Map[ValDef, Expr] = {
    SimpleSolverAPI(program.getSolver).solveSAT(clause) match {
      case SatWithModel(model) => model.vars
      case res => fail(s"Expected a model, got $res")
    }
  }

  private def result(clause: Expr)(using Context) = SimpleSolverAPI(program.getSolver).solveSAT(clause)

  /** Closed sub-expressions of the extracted models that have type `tpe`. */
  private def candidates(tpe: Type, es: Iterable[Expr]): Set[Expr] = es.toSet.flatMap { (e: Expr) =>
    exprOps.collect[Expr] {
      case e if e.getType(using program.symbols) == tpe && exprOps.variablesOf(e).isEmpty => Set(e)
      case _ => Set.empty
    } (e)
  }

  /** Whether `f1` and `f2` give different results on some inputs taken from `pool` (by default,
    * the two functions themselves). Results of function type are compared the same way, so curried
    * functions are distinguished by a sequence of inputs. */
  private def distinguishable(f1: Expr, f2: Expr, pool: Expr*)(using ctx: Context): Boolean = {
    val FunctionType(from, _) = f1.getType(using program.symbols): @unchecked
    val exprs = pool ++ Seq(f1, f2)
    val evaluator = program.getEvaluator
    val argss = from.foldRight(Seq(Seq.empty[Expr])) { (tpe, rest) =>
      for (arg <- candidates(tpe, exprs).toSeq; args <- rest) yield arg +: args
    }
    argss.exists { args =>
      val r1 = evaluator.eval(Application(f1, args))
      val r2 = evaluator.eval(Application(f2, args))
      (r1, r2) match {
        case (EvaluationResults.Successful(v1), EvaluationResults.Successful(v2)) =>
          v1.getType(using program.symbols) match {
            case _: FunctionType => distinguishable(v1, v2, (exprs :+ v1 :+ v2)*)
            case _ => v1 != v2
          }
        case _ => false
      }
    }
  }

  /** Whether `e` compares functions, which a language without function equality can't evaluate. */
  private def comparesFunctions(e: Expr): Boolean = exprOps.exists {
    case Equals(l, _) => typeOps.exists(_.isInstanceOf[FunctionType])(l.getType(using program.symbols))
    case _ => false
  } (e)

  /** cvc5 models for functions applied to functions can't be extracted yet. */
  private def hasHigherOrderModels(ctx: Context): FilterStatus =
    if (ctx.options.findOptionOrDefault(optSelectedSolvers).contains("smt-cvc5")) Skip else Test

  test("functions applied to distinct functions", hasHigherOrderModels) {
    // `f` must map `g` and `h` to different results, and its extraction tells them apart by
    // applying its argument to their distinguishing input instead of comparing it with them
    val f = ("f" :: ((IntegerType() =>: IntegerType()) =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val h = ("h" :: (IntegerType() =>: IntegerType())).toVariable
    val model = solve(f(g) !== f(h))
    assert(!model.values.exists(comparesFunctions))
  }

  test("functions applied to a function and a lambda", hasHigherOrderModels) {
    val f = ("f" :: ((IntegerType() =>: IntegerType()) =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val succ = \("x" :: IntegerType())(x => x + E(BigInt(1)))
    val model = solve(f(g) !== f(succ))
    assert(!model.values.exists(comparesFunctions))
  }

  test("structurally distinct lambdas remain distinct") {
    val succ = \("x" :: IntegerType())(x => x + E(BigInt(1)))
    val pred = \("x" :: IntegerType())(x => x - E(BigInt(1)))
    assert(result(succ === pred).isUNSAT)
    assert(result(succ !== pred).isSAT)
  }

  // unrollz3 evaluates `f` to the same result on `g` and `h`, so its models are rejected
  test("functions applied to distinct curried functions", ctx =>
    if (ctx.options.findOptionOrDefault(optSelectedSolvers).contains("unrollz3")) Skip
    else hasHigherOrderModels(ctx)) {
    val tpe = IntegerType() =>: (IntegerType() =>: IntegerType())
    val f = ("f" :: (tpe =>: IntegerType())).toVariable
    val g = ("g" :: tpe).toVariable
    val h = ("h" :: tpe).toVariable
    val model = solve(f(g) !== f(h))
    assert(!model.values.exists(comparesFunctions))
  }

  test("distinct first-order functions") {
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val model = solve(f !== g)
    assert(distinguishable(model(f.toVal), model(g.toVal)))
  }

  test("distinct function and lambda") {
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val clause = f !== \("x" :: IntegerType())(x => x + E(BigInt(1)))
    val model = solve(clause)
    assert(distinguishable(model(f.toVal), \("x" :: IntegerType())(x => x + E(BigInt(1)))))
  }

  test("distinct higher-order functions") { ctx ?=>
    val tpe = (IntegerType() =>: IntegerType()) =>: IntegerType()
    val f = ("f" :: tpe).toVariable
    val g = ("g" :: tpe).toVariable
    val model = solve(f !== g)
    // cvc5 models for function-typed witnesses can't be extracted yet, so the solver
    // falls back to a model without distinguishing inputs
    // falls back to a model without distinguishing inputs. With a single application each,
    // the extracted functions are constant, so any input tells them apart.
    if (!ctx.options.findOptionOrDefault(optSelectedSolvers).contains("smt-cvc5")) {
      val id = \("x" :: IntegerType())(x => x)
      assert(distinguishable(model(f.toVal), model(g.toVal), id))
      assert(!model.values.exists(comparesFunctions))
    }
  }

  test("distinct functions agreeing on an input") {
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val clause = (f !== g) && f(E(BigInt(0))) === g(E(BigInt(0)))
    val model = solve(clause)
    assert(distinguishable(model(f.toVal), model(g.toVal)))
  }

  test("many pairwise distinct functions") {
    // More pairs than any fixed budget of distinguishing inputs would cover. All functions agree
    // on `true`, so the solver has to pick a different result on `false` for each of them.
    val fs = (1 to 16).map(i => (s"f$i" :: (BooleanType() =>: IntegerType())).toVariable)
    val pairs = for (f1 <- fs; f2 <- fs if f1.id.globalId < f2.id.globalId) yield (f1, f2)
    val clause = andJoin(fs.map(f => f(E(true)) === E(BigInt(0))) ++ pairs.map((f1, f2) => f1 !== f2))
    val model = solve(clause)
    val evaluator = program.getEvaluator
    def resultOnFalse(f: Variable): Option[Expr] = evaluator.eval(Application(model(f.toVal), Seq(E(false)))) match {
      case EvaluationResults.Successful(v) => Some(v)
      case _ => None
    }
    val results = fs.map(f => f -> resultOnFalse(f)).toMap
    for ((f1, f2) <- pairs) {
      assert(results(f1).isDefined && results(f1) != results(f2), s"$f1 and $f2 aren't distinguished")
    }
  }

  test("distinct nullary functions") {
    // the distinguishing input of nullary functions is the empty argument list
    val f = ("f" :: FunctionType(Seq(), IntegerType())).toVariable
    val g = ("g" :: FunctionType(Seq(), IntegerType())).toVariable
    val model = solve(f !== g)
    assert(distinguishable(model(f.toVal), model(g.toVal)))
  }

  test("distinct nullary function and lambda") {
    val f = ("f" :: FunctionType(Seq(), IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val lambda = Lambda(Seq(), g(E(BigInt(5))))
    val model = solve(f !== lambda)
    assert(distinguishable(model(f.toVal), exprOps.replaceFromSymbols(Map(g -> model(g.toVal)), lambda)))
  }

  test("nullary functions with equal results") {
    // `f() == g()` implies `f == g` under the witness clauses, so only an intensional
    // counterexample remains, which the solver finds once it drops the witnesses
    val f = ("f" :: FunctionType(Seq(), IntegerType())).toVariable
    val g = ("g" :: FunctionType(Seq(), IntegerType())).toVariable
    assert(!result((f !== g) && (Application(f, Seq()) === Application(g, Seq()))).isUNSAT)
  }

  test("eta-expanded closure remains distinct") {
    // Function equality is intensional and `f` closes over `g`, so `f != g` even though
    // no distinguishing input can exist: the solver must drop the witness assumptions.
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val clause = f === \("x" :: IntegerType())(x => g(x))
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  // Models: distinct functions are told apart by an input

  test("distinct functions of several arguments") {
    val tpe = (IntegerType(), IntegerType()) =>: IntegerType()
    val f = ("f" :: tpe).toVariable
    val g = ("g" :: tpe).toVariable
    val zero = E(BigInt(0))
    val model = solve((f !== g) && f(zero, zero) === g(zero, zero))
    assert(distinguishable(model(f.toVal), model(g.toVal)))
  }

  test("distinct curried functions") {
    val tpe = IntegerType() =>: (IntegerType() =>: IntegerType())
    val f = ("f" :: tpe).toVariable
    val g = ("g" :: tpe).toVariable
    val model = solve(f !== g)
    assert(distinguishable(model(f.toVal), model(g.toVal)))
  }

  test("distinct function and closure") {
    // the lambda captures `y`, so it is only known up to the value of `y`
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val y = ("y" :: IntegerType()).toVariable
    val lambda = \("x" :: IntegerType())(x => x + y)
    val model = solve((f !== lambda) && f(E(BigInt(0))) === y)
    val closed = \("x" :: IntegerType())(x => x + model(y.toVal))
    assert(distinguishable(model(f.toVal), closed))
  }

  test("distinct functions in datatypes") {
    val b1 = ("b1" :: T(boxID)()).toVariable
    val b2 = ("b2" :: T(boxID)()).toVariable
    val zero = E(BigInt(0))
    val model = solve((b1 !== b2) && b1.getField(fn)(zero) === b2.getField(fn)(zero))
    (model(b1.toVal), model(b2.toVal)) match {
      case (ADT(_, _, Seq(f1)), ADT(_, _, Seq(f2))) => assert(distinguishable(f1, f2))
      case res => fail(s"Unexpected model: $res")
    }
  }

  test("distinct functions on a type parameter") {
    val tp = TypeParameter.fresh("A")
    val f = ("f" :: (tp =>: tp)).toVariable
    val g = ("g" :: (tp =>: tp)).toVariable
    val model = solve(f !== g)
    assert(distinguishable(model(f.toVal), model(g.toVal)))
  }

  test("all Boolean functions") {
    // There are exactly four functions from Boolean to Boolean, so the model must contain each
    // of them, with a distinguishing input for every pair.
    val fs = (1 to 4).map(i => (s"f$i" :: (BooleanType() =>: BooleanType())).toVariable)
    val pairs = for (f1 <- fs; f2 <- fs if f1.id.globalId < f2.id.globalId) yield (f1, f2)
    val model = solve(andJoin(pairs.map((f1, f2) => f1 !== f2)))
    for ((f1, f2) <- pairs) {
      assert(distinguishable(model(f1.toVal), model(f2.toVal), E(true), E(false)), s"$f1 and $f2 aren't distinguished")
    }
  }

  test("distinguishing input that needs unfolding") {
    // `f` and `g` agree on every list of size 0 or 1, so the distinguishing input must be
    // a longer list, which requires unfolding `size` on the witness
    val tpe = intList =>: IntegerType()
    val f = ("f" :: tpe).toVariable
    val g = ("g" :: tpe).toVariable
    val clause = (f !== g) &&
      forall("l" :: intList)(l => (sizeFd(IntegerType())(l) <= E(BigInt(1))) ==> (f(l) === g(l)))
    val model = solve(clause)
    assert(distinguishable(model(f.toVal), model(g.toVal)))
  }

  test("distinct functions next to a recursive function") {
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val l = ("l" :: intList).toVariable
    val model = solve((f !== g) && f(sizeFd(IntegerType())(l)) === g(E(BigInt(2))) && sizeFd(IntegerType())(l) > E(BigInt(2)))
    assert(distinguishable(model(f.toVal), model(g.toVal)))
  }

  // Intensional equality: the extensionality assumption must never make a satisfiable query UNSAT

  test("structurally distinct, extensionally equal lambdas") {
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val id = \("x" :: IntegerType())(x => x)
    val alsoId = \("x" :: IntegerType())(x => if_ (x === E(BigInt(0))) { E(BigInt(0)) } else_ { x })
    assert(result((f !== id) && (f === alsoId)).isSAT)
  }

  test("distinct functions equal on every input") {
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val clause = (f !== g) && forall("x" :: IntegerType())(x => f(x) === g(x))
    // Satisfiable by two closures with the same results. Model extraction can't build such
    // closures for free functions, so the answer may be unknown, but it must not be UNSAT.
    assert(!result(clause).isUNSAT)
  }

  test("more distinct Boolean functions than extensional ones") {
    val fs = (1 to 5).map(i => (s"f$i" :: (BooleanType() =>: BooleanType())).toVariable)
    val pairs = for (f1 <- fs; f2 <- fs if f1.id.globalId < f2.id.globalId) yield (f1, f2)
    assert(!result(andJoin(pairs.map((f1, f2) => f1 !== f2))).isUNSAT)
  }

  test("intensional counterexample that needs unfolding") {
    // `f` closes over `g`, so they are distinct without a distinguishing input, and the list
    // constraint keeps the solver unrolling after the witnesses turn out to be infeasible
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val l = ("l" :: intList).toVariable
    val clause = (f === \("x" :: IntegerType())(x => g(x))) && sizeFd(IntegerType())(l) > E(BigInt(3))
    assert(result(clause).isSAT)
  }

  test("intensional counterexample over a recursive type with function fields") {
    // Witnesses of type `Obj` contain fresh functions, which need witnesses of their own, so
    // there are always more of them to instantiate: the solver must still drop them and stop.
    // Model extraction can't build a valid model for this query even without witnesses, so the
    // answer may be unknown.
    val tpe = T(objID)() =>: T(objID)()
    val f = ("f" :: tpe).toVariable
    val g = ("g" :: tpe).toVariable
    assert(!result(f === \("x" :: T(objID)())(x => g(x))).isUNSAT)
  }

  test("distinct functions over a recursive type with function fields") {
    val tpe = T(objID)() =>: T(objID)()
    val f = ("f" :: tpe).toVariable
    val g = ("g" :: tpe).toVariable
    val model = solve(f !== g)
    assert(distinguishable(model(f.toVal), model(g.toVal)))
  }

  // Proofs are unaffected

  test("equal functions agree") {
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val x = ("x" :: IntegerType()).toVariable
    assert(result((f === g) && (f(x) !== g(x))).isUNSAT)
  }

  test("unsatisfiable query with distinct functions") {
    // the witnesses must not keep the solver from refuting the query by unfolding `size`
    val tpe = intList =>: IntegerType()
    val f = ("f" :: tpe).toVariable
    val g = ("g" :: tpe).toVariable
    val l = ("l" :: intList).toVariable
    val one = C(consID)(IntegerType())(E(BigInt(1)), C(nilID)(IntegerType())())
    val clause = (f !== g) && (f(l) === g(l)) && (l === one) && (sizeFd(IntegerType())(l) !== E(BigInt(1)))
    assert(result(clause).isUNSAT)
  }

  test("unsatisfiable query about distinguishing inputs") {
    // Two distinct functions on Unit must differ on (), yet both map it to 0. This is UNSAT
    // only extensionally, so the solver must not report UNSAT because of the witnesses alone:
    // dropping them leaves a satisfiable query.
    val f = ("f" :: (UnitType() =>: IntegerType())).toVariable
    val g = ("g" :: (UnitType() =>: IntegerType())).toVariable
    val clause = (f !== g) && f(UnitLiteral()) === E(BigInt(0)) && g(UnitLiteral()) === E(BigInt(0))
    assert(!result(clause).isUNSAT)
  }

  // Solver state and options

  test("incremental solving") { ctx ?=>
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val solver = program.getSolver.getNewSolver()
    try {
      solver.assertCnstr(f !== g)
      solver.push()
      solver.assertCnstr(f === g)
      assert(solver.check(Simple).isUNSAT)
      solver.pop()
      solver.check(Model) match {
        case SatWithModel(model) => assert(distinguishable(model.vars(f.toVal), model.vars(g.toVal)))
        case res => fail(s"Expected a model, got $res")
      }
      solver.push()
      solver.assertCnstr(f(E(BigInt(1))) === g(E(BigInt(1))))
      solver.check(Model) match {
        case SatWithModel(model) => assert(distinguishable(model.vars(f.toVal), model.vars(g.toVal)))
        case res => fail(s"Expected a model, got $res")
      }
      solver.pop()
    } finally {
      solver.free()
    }
  }

  private def withEquality(semantics: FunctionEquality)(using ctx: Context): Context =
    ctx.withOpts(optFunctionEquality(semantics))

  private def resultWith(semantics: FunctionEquality)(clause: Expr)(using Context) =
    SimpleSolverAPI(program.getSolver(withEquality(semantics))).solveSAT(clause)

  test("function comparisons are rejected without function equality") { ctx ?=>
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val box = ("b" :: T(boxID)()).toVariable
    for (clause <- Seq(f !== g, box === box)) {
      val e = intercept[Exception](resultWith(FunctionEquality.None)(clause))
      assert(e.getMessage.contains("can't be compared"))
    }
  }

  test("comparisons with constructors without functions are accepted") { ctx ?=>
    // `Num(n)` holds no function, so comparing an `Obj` with it is a constructor test
    val o = ("o" :: T(objID)()).toVariable
    val n = ("n" :: IntegerType()).toVariable
    assert(resultWith(FunctionEquality.None)(o === C(numID)(n)).isSAT)
    assert(resultWith(FunctionEquality.None)((o === C(numID)(n)) && (o !== C(numID)(n))).isUNSAT)
  }

  test("functions applied to functions without function equality", hasHigherOrderModels) { ctx ?=>
    val f = ("f" :: ((IntegerType() =>: IntegerType()) =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val succ = \("x" :: IntegerType())(x => x + E(BigInt(1)))
    val pred = \("x" :: IntegerType())(x => x - E(BigInt(1)))
    val a = ("a" :: IntegerType()).toVariable
    val b = ("b" :: IntegerType()).toVariable
    val addA = \("x" :: IntegerType())(x => x + a)
    val addB = \("x" :: IntegerType())(x => x + b)
    // lambdas get a distinguishing input instead of being distinct by structure or closures
    for (clause <- Seq(f(g) !== f(succ), f(succ) !== f(pred), f(addA) !== f(addB))) {
      resultWith(FunctionEquality.None)(clause) match {
        case SatWithModel(model) => assert(!model.vars.values.exists(comparesFunctions))
        case res => fail(s"Expected a model, got $res")
      }
    }
  }

  test("intensional counterexamples don't exist without function equality") { ctx ?=>
    // the query can't tell `f` and `h` apart, so it is satisfiable with `f == h`
    val f = ("f" :: FunctionType(Seq(), IntegerType())).toVariable
    val h = ("h" :: FunctionType(Seq(), IntegerType())).toVariable
    assert(resultWith(FunctionEquality.None)(Application(f, Seq()) === Application(h, Seq())).isSAT)

    // a function applied to functions can't tell apart functions that agree on every input
    val k = ("k" :: ((IntegerType() =>: IntegerType()) =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    assert(resultWith(FunctionEquality.None)(k(g) !== k(\("x" :: IntegerType())(x => g(x)))).isUNSAT)
  }

  test("extensionally equal functions are equal") { ctx ?=>
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val etaG = \("x" :: IntegerType())(x => g(x))
    val id = \("x" :: IntegerType())(x => x)
    val alsoId = \("x" :: IntegerType())(x => if_ (x === E(BigInt(0))) { E(BigInt(0)) } else_ { x })
    val agree = forall("x" :: IntegerType())(x => f(x) === g(x))
    for (clause <- Seq((f !== g) && agree, g !== etaG, id !== alsoId)) {
      val res = resultWith(FunctionEquality.Extensional)(clause)
      assert(res.isUNSAT, s"${clause.asString(using PrinterOptions())}: $res")
      assert(!resultWith(FunctionEquality.Intensional)(clause).isUNSAT)
    }
  }

  test("extensionally distinct lambdas are distinct") { ctx ?=>
    val succ = \("x" :: IntegerType())(x => x + E(BigInt(1)))
    val pred = \("x" :: IntegerType())(x => x - E(BigInt(1)))
    assert(resultWith(FunctionEquality.Extensional)(succ === pred).isUNSAT)
    assert(resultWith(FunctionEquality.Extensional)(succ !== pred).isSAT)
  }

  test("disabled witnesses") { ctx ?=>
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val noWitnesses = ctx.withOpts(optFunctionWitnesses(false), optCheckModels(false))
    assert(SimpleSolverAPI(program.getSolver(noWitnesses)).solveSAT(f !== g).isSAT)
  }
}
