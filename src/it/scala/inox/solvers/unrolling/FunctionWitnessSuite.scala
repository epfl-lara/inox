/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import SolverResponses._
import evaluators.EvaluationResults

/** Checks that distinct first-class functions in models have a distinguishing input.
  *
  * @see [[LambdaTemplates.functionWitnesses]]
  */
class FunctionWitnessSuite extends UnrollingTestSuite {
  import inox.trees._
  import dsl._

  override protected def optionMatrix = UnrollingTestSuite.combinations(
    // Most tests compare functions, which `none` rejects. Distinct functions always
    // have a distinguishing input under extensional equality, but not under intensional equality.
    Seq(optFunctionEquality(FunctionEquality.Extensional)),
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

  // compares values of a type parameter, which may be instantiated with a function type
  val sameID = FreshIdentifier("same")
  val sameFd = mkFunDef(sameID)("A") { case Seq(aT) => (
    Seq("x" :: aT, "y" :: aT), BooleanType(), { case Seq(x, y) => x === y })
  }

  // compares values of a type parameter through a callee
  val sameViaID = FreshIdentifier("sameVia")
  val sameViaFd = mkFunDef(sameViaID)("A") { case Seq(aT) => (
    Seq("x" :: aT, "y" :: aT), BooleanType(), { case Seq(x, y) => E(sameID)(aT)(x, y) })
  }

  // polymorphic recursion: `poly[A]` calls `poly[(A, A)]`, so its instances are unbounded
  val polyID = FreshIdentifier("poly")
  val polyFd = mkFunDef(polyID)("A") { case Seq(aT) => (
    Seq("x" :: aT, "n" :: IntegerType()), BooleanType(), { case Seq(x, n) =>
      (x === x) && (if_ (n <= E(BigInt(0))) { E(true) } else_ {
        E(polyID)(TupleType(Seq(aT, aT)))(Tuple(Seq(x, x)), n - E(BigInt(1)))
      })
    })
  }

  val program = InoxProgram(new Symbols(
    Map(sizeID -> sizeFd, sameID -> sameFd, sameViaID -> sameViaFd, polyID -> polyFd),
    Map(listID -> List, boxID -> Box, objID -> Obj)))

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

  test("distinct higher-order functions", hasHigherOrderModels) {
    val tpe = (IntegerType() =>: IntegerType()) =>: IntegerType()
    val f = ("f" :: tpe).toVariable
    val g = ("g" :: tpe).toVariable
    val model = solve(f !== g)
    val id = \("x" :: IntegerType())(x => x)
    assert(distinguishable(model(f.toVal), model(g.toVal), id))
    assert(!model.values.exists(comparesFunctions))
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

  test("nullary functions with equal results") { ctx ?=>
    given Context = ctx.withOpts(optFunctionEquality(FunctionEquality.Intensional))
    // `f() == g()` implies `f == g` extensionally, so only an intensional counterexample remains
    val f = ("f" :: FunctionType(Seq(), IntegerType())).toVariable
    val g = ("g" :: FunctionType(Seq(), IntegerType())).toVariable
    assert(!result((f !== g) && (Application(f, Seq()) === Application(g, Seq()))).isUNSAT)
  }

  test("eta-expanded closure remains distinct") { ctx ?=>
    given Context = ctx.withOpts(optFunctionEquality(FunctionEquality.Intensional))
    // `f` closes over `g`, so `f != g` intensionally, although no distinguishing input can exist
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

  // Intensional equality: distinct functions needn't have a distinguishing input

  test("structurally distinct, extensionally equal lambdas") { ctx ?=>
    given Context = ctx.withOpts(optFunctionEquality(FunctionEquality.Intensional))
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val id = \("x" :: IntegerType())(x => x)
    val alsoId = \("x" :: IntegerType())(x => if_ (x === E(BigInt(0))) { E(BigInt(0)) } else_ { x })
    assert(result((f !== id) && (f === alsoId)).isSAT)
  }

  test("distinct functions equal on every input") { ctx ?=>
    given Context = ctx.withOpts(optFunctionEquality(FunctionEquality.Intensional))
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val clause = (f !== g) && forall("x" :: IntegerType())(x => f(x) === g(x))
    // Satisfiable by two closures with the same results. Model extraction can't build such
    // closures for free functions, so the answer may be unknown, but it must not be UNSAT.
    assert(!result(clause).isUNSAT)
  }

  test("more distinct Boolean functions than extensional ones") { ctx ?=>
    given Context = ctx.withOpts(optFunctionEquality(FunctionEquality.Intensional))
    val fs = (1 to 5).map(i => (s"f$i" :: (BooleanType() =>: BooleanType())).toVariable)
    val pairs = for (f1 <- fs; f2 <- fs if f1.id.globalId < f2.id.globalId) yield (f1, f2)
    assert(!result(andJoin(pairs.map((f1, f2) => f1 !== f2))).isUNSAT)
  }

  test("intensional counterexample that needs unfolding") { ctx ?=>
    given Context = ctx.withOpts(optFunctionEquality(FunctionEquality.Intensional))
    // `f` closes over `g`, so they are distinct without a distinguishing input, and the list
    // constraint keeps the solver unrolling
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val l = ("l" :: intList).toVariable
    val clause = (f === \("x" :: IntegerType())(x => g(x))) && sizeFd(IntegerType())(l) > E(BigInt(3))
    assert(result(clause).isSAT)
  }

  test("intensional counterexample over a recursive type with function fields") { ctx ?=>
    given Context = ctx.withOpts(optFunctionEquality(FunctionEquality.Intensional))
    // Model extraction can't build a valid model for this query, so the answer may be unknown.
    val tpe = T(objID)() =>: T(objID)()
    val f = ("f" :: tpe).toVariable
    val g = ("g" :: tpe).toVariable
    assert(!result(f === \("x" :: T(objID)())(x => g(x))).isUNSAT)
  }

  test("distinct functions over a recursive type with function fields") {
    // The witnesses of type `Obj` contain functions with witnesses of their own, so extracted
    // values can be cyclic and contain `choose`s. Comparing such functions by their results can
    // then fail, and the model is rejected (see the limitations in `function-witnesses.md`).
    val tpe = T(objID)() =>: T(objID)()
    val f = ("f" :: tpe).toVariable
    val g = ("g" :: tpe).toVariable
    result(f !== g) match {
      case SatWithModel(model) => assert(distinguishable(model.vars(f.toVal), model.vars(g.toVal)))
      case res => assert(!res.isUNSAT, s"Expected a model or Unknown, got $res")
    }
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

  test("unsatisfiable query about distinguishing inputs") { ctx ?=>
    // Two distinct functions on Unit must differ on (), yet both map it to 0. This is UNSAT
    // only extensionally.
    val f = ("f" :: (UnitType() =>: IntegerType())).toVariable
    val g = ("g" :: (UnitType() =>: IntegerType())).toVariable
    val clause = (f !== g) && f(UnitLiteral()) === E(BigInt(0)) && g(UnitLiteral()) === E(BigInt(0))
    assert(result(clause).isUNSAT)
    assert(!result(clause)(using ctx.withOpts(optFunctionEquality(FunctionEquality.Intensional))).isUNSAT)
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

  test("function comparisons at type parameters are rejected without function equality") { ctx ?=>
    val fnT = IntegerType() =>: IntegerType()
    val f = ("f" :: fnT).toVariable
    val g = ("g" :: fnT).toVariable
    val e = intercept[Exception](resultWith(FunctionEquality.None)(E(sameID)(fnT)(f, g)))
    assert(e.getMessage.contains("can't be compared"))

    val x = ("x" :: IntegerType()).toVariable
    assert(resultWith(FunctionEquality.None)(E(sameID)(IntegerType())(x, E(BigInt(1)))).isSAT)
  }

  test("function comparisons in callees are found at their type arguments") { ctx ?=>
    val fnT = IntegerType() =>: IntegerType()
    def comparisons(e: Expr) = FunctionEquality.comparisons(program)(e)
    val f = ("f" :: fnT).toVariable
    val x = ("x" :: IntegerType()).toVariable
    val n = ("n" :: IntegerType()).toVariable
    // through an intermediate callee
    assert(comparisons(E(sameViaID)(fnT)(f, f)).nonEmpty)
    assert(comparisons(E(sameViaID)(IntegerType())(x, x)).isEmpty)
    // types without functions, and with function fields
    assert(comparisons(E(sameViaID)(T(listID)(IntegerType()))(C(nilID)(IntegerType())(), C(nilID)(IntegerType())())).isEmpty)
    assert(comparisons(E(sameViaID)(T(boxID)())(C(boxConsID)(f), C(boxConsID)(f))).nonEmpty)
    // polymorphic recursion terminates, and is checked at the instantiated types
    assert(comparisons(E(polyID)(IntegerType())(x, n)).isEmpty)
    assert(comparisons(E(polyID)(fnT)(f, n)).nonEmpty)

    val e = intercept[Exception](resultWith(FunctionEquality.None)(E(sameViaID)(fnT)(f, f)))
    assert(e.getMessage.contains("can't be compared"))
    assert(resultWith(FunctionEquality.None)(E(sameViaID)(IntegerType())(x, E(BigInt(1)))).isSAT)
  }

  test("comparisons with constructors without functions are accepted") { ctx ?=>
    // `Num(n)` holds no function, so comparing an `Obj` with it is a constructor test
    val o = ("o" :: T(objID)()).toVariable
    val n = ("n" :: IntegerType()).toVariable
    assert(resultWith(FunctionEquality.None)(o === C(numID)(n)).isSAT)
    assert(resultWith(FunctionEquality.None)((o === C(numID)(n)) && (o !== C(numID)(n))).isUNSAT)
    assert(resultWith(FunctionEquality.None)(C(numID)(n) === o).isSAT)
  }

  test("function equality option") {
    assert(optFunctionEquality.parser("extensional") == Some(FunctionEquality.Extensional))
    assert(optFunctionEquality.parser("Intensional") == Some(FunctionEquality.Intensional))
    assert(optFunctionEquality.parser("structural").isEmpty)
    assert(optFunctionEquality.default == FunctionEquality.Intensional)
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

  test("free functions passed to a function without function equality", hasHigherOrderModels) { ctx ?=>
    // `f` and `g` are only told apart through `k`, so the model needs their distinguishing input
    // although the query never compares them
    val k = ("k" :: ((IntegerType() =>: IntegerType()) =>: IntegerType())).toVariable
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val h = ("h" :: (IntegerType() =>: IntegerType())).toVariable
    for (clause <- Seq(k(f) !== k(g), (k(f) !== k(g)) && (k(g) !== k(h)) && (k(f) !== k(h)))) {
      resultWith(FunctionEquality.None)(clause) match {
        case SatWithModel(model) =>
          assert(!model.vars.values.exists(comparesFunctions))
          val fns = Seq(f, g, h).filter(v => model.vars.contains(v.toVal)).map(v => model.vars(v.toVal))
          for (case Seq(f1, f2) <- fns.combinations(2)) assert(distinguishable(f1, f2))
        case res => fail(s"Expected a model, got $res")
      }
    }
  }

  test("models with extensional function equality") { ctx ?=>
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val succ = \("x" :: IntegerType())(x => x + E(BigInt(1)))
    val bf = ("bf" :: T(boxID)()).toVariable
    val bg = ("bg" :: T(boxID)()).toVariable
    val clauses = Seq(
      (f !== g) -> Seq(f -> g),
      ((f !== g) && f(E(BigInt(0))) === g(E(BigInt(0)))) -> Seq(f -> g),
      (f !== succ) -> Seq(f -> succ),
      (bf !== bg) -> Seq(bf.getField(fn) -> bg.getField(fn)))
    for ((clause, pairs) <- clauses) {
      resultWith(FunctionEquality.Extensional)(clause) match {
        case SatWithModel(model) =>
          val subst = model.vars.map((vd, v) => vd.toVariable -> v)
          def value(e: Expr): Expr = program.getEvaluator.eval(exprOps.replaceFromSymbols(subst, e)) match {
            case EvaluationResults.Successful(v) => v
            case res => fail(s"Can't evaluate ${e.asString(using PrinterOptions())}: $res")
          }
          for ((e1, e2) <- pairs) assert(distinguishable(value(e1), value(e2)))
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

  test("quantified function comparisons are evaluated extensionally") { ctx ?=>
    val x = ("x" :: IntegerType()).toVariable
    val forall = Forall(Seq(x.toVal),
      \("y" :: IntegerType())(y => y + x) === \("y" :: IntegerType())(y => x + y))
    program.getEvaluator(withEquality(FunctionEquality.Extensional)).eval(forall) match {
      case EvaluationResults.Successful(BooleanLiteral(true)) =>
      case res => fail(s"Expected the quantifier to hold, got $res")
    }
    // without function equality, the quantifier can't be evaluated
    scala.util.Try(program.getEvaluator(withEquality(FunctionEquality.None)).eval(forall)) match {
      case scala.util.Success(EvaluationResults.Successful(v)) => fail(s"Expected an error, got $v")
      case _ =>
    }
  }

  // The models below are checked by the evaluator, which can't compare functions under `none`
  private def solveWithoutEquality(clause: Expr)(using Context): Map[ValDef, Expr] =
    resultWith(FunctionEquality.None)(clause) match {
      case SatWithModel(model) =>
        assert(!model.vars.values.exists(comparesFunctions))
        model.vars
      case res => fail(s"Expected a model, got $res")
    }

  test("functions applied to datatypes with functions without function equality", hasHigherOrderModels) { ctx ?=>
    val fnT = IntegerType() =>: IntegerType()
    val k = ("k" :: (T(boxID)() =>: IntegerType())).toVariable
    val b1 = ("b1" :: T(boxID)()).toVariable
    val b2 = ("b2" :: T(boxID)()).toVariable
    val model = solveWithoutEquality(k(b1) !== k(b2))
    def fnOf(b: Variable) = model(b.toVal) match {
      case ADT(_, _, Seq(f)) => f
      case v => fail(s"Unexpected box $v")
    }
    assert(distinguishable(fnOf(b1), fnOf(b2)))

    // tuples, where the functions must be told apart although the other components are equal
    val t = ("t" :: (TupleType(Seq(fnT, IntegerType())) =>: IntegerType())).toVariable
    val f = ("f" :: fnT).toVariable
    val g = ("g" :: fnT).toVariable
    val zero = E(BigInt(0))
    val model2 = solveWithoutEquality(t(Tuple(Seq(f, zero))) !== t(Tuple(Seq(g, zero))))
    assert(distinguishable(model2(f.toVal), model2(g.toVal)))
  }

  test("functions applied to functions returning datatypes without function equality", hasHigherOrderModels) { ctx ?=>
    // `g` and `h` give different boxes on their distinguishing input. The functions in these boxes
    // aren't necessarily active, so they may have no distinguishing input (see the limitations in
    // `function-witnesses.md`): the solver then can't extract a model without comparing them, and
    // the model is rejected rather than reported.
    val boxFn = IntegerType() =>: T(boxID)()
    val k = ("k" :: (boxFn =>: IntegerType())).toVariable
    val g = ("g" :: boxFn).toVariable
    val h = ("h" :: boxFn).toVariable
    resultWith(FunctionEquality.None)(k(g) !== k(h)) match {
      case SatWithModel(model) => assert(!model.vars.values.exists(comparesFunctions))
      case res => assert(!res.isUNSAT, s"Expected a model or Unknown, got $res")
    }
  }

  test("functions applied to curried lambdas without function equality", hasHigherOrderModels) { ctx ?=>
    // the results of the lambdas on their distinguishing input are lambdas too, and need one of
    // their own, one level deeper
    val tpe = IntegerType() =>: (IntegerType() =>: IntegerType())
    val k = ("k" :: (tpe =>: IntegerType())).toVariable
    val add = \("x" :: IntegerType())(x => \("y" :: IntegerType())(y => x + y))
    val sub = \("x" :: IntegerType())(x => \("y" :: IntegerType())(y => x - y))
    solveWithoutEquality(k(add) !== k(sub))
  }

  test("no distinguishing inputs under intensional equality") { ctx ?=>
    // `f` and `g` agree on `x`, and on any distinguishing input the solver would introduce
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val clause = (f !== g) && forall("x" :: IntegerType())(x => f(x) === g(x))
    assert(resultWith(FunctionEquality.Extensional)(clause).isUNSAT)
    assert(!resultWith(FunctionEquality.Intensional)(clause).isUNSAT)
  }
}
