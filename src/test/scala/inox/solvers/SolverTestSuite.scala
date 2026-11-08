/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import org.scalatest.funsuite.AnyFunSuite

/** Theories and constructs a test can require from a solver.
  *
  * A test declares the features it uses and only runs on the solvers that support all of
  * them (see [[SolverTestSuite.solvers]]).
  */
enum Feature {
  /** Mathematical integers (`BigInt`), including division and modulo. */
  case Integers
  /** Real numbers (fractions). */
  case Reals
  /** Bit-vector casts, bitwise operations, comparisons and division at any width.
    * Bit-vector literals, addition and multiplication are supported everywhere.
    */
  case BitVectors
  /** Conversions between bit-vectors and integers. */
  case BitVectorIntConversions
  /** IEEE floating point numbers. */
  case FloatingPoint
  /** Strings. */
  case Strings
  /** Sets. */
  case Sets
  /** Bags, with multiplicities, additions and equalities. */
  case Bags
  /** Equalities between bag unions, differences and intersections. */
  case BagAlgebra
  /** Maps. */
  case Maps
  /** Sets nested within maps, which Z3 returns as lambdas in models. */
  case NestedArrays
  /** Algebraic datatypes. */
  case ADTs
  /** First-class functions (lambdas and applications). */
  case Functions
  /** Universal quantifiers. */
  case Quantifiers
  /** Type parameters, encoded as uninterpreted sorts. */
  case TypeParameters
}

object SolverTestSuite {
  import Feature._

  /** A solver checked by the solver suites, with the features it doesn't support, the tests it
    * fails because of known bugs (test name -> reason), and the tests whose checks it only passes
    * on ground expressions (see [[SolverTestSuite.check]]), and how many checks it solves in one
    * query.
    */
  case class SolverInfo(
    name: String,
    available: () => Boolean,
    unsupported: Set[Feature],
    knownIssues: Map[String, String] = Map.empty,
    groundOnly: Map[String, String] = Map.empty,
    batchSize: Int = 8
  ) {
    def supports(features: Seq[Feature]): Boolean = features.forall(f => !unsupported(f))
  }

  private val z3BagUnionModels = "Z3 models leave equalities between bag unions unevaluated"
  private val cvcGroundOnly = Map(
    "Bag Operations with repeated keys" -> "returns Unknown for differences of bags with variable elements",
    "Map Operations" -> "returns Unknown for constant maps with a variable default",
  )

  /** Every solver whose encoding and model extraction are tested.
    *
    * The unrolling engine on top of these solvers is shared, so the unrolling suites (in
    * `src/it`) only run against a single solver. These solvers must therefore agree on
    * every feature they support.
    */
  val solvers: Seq[SolverInfo] = Seq(
    SolverInfo("nativez3", () => SolverFactory.hasNativeZ3,
      Set(BitVectorIntConversions, FloatingPoint),
      groundOnly = Map("Bag Operations" -> z3BagUnionModels)),
    SolverInfo("unrollz3", () => SolverFactory.hasNativeZ3,
      Set(BitVectorIntConversions, FloatingPoint),
      groundOnly = Map("Bag Operations" -> z3BagUnionModels)),
    SolverInfo("smt-z3", () => SolverFactory.hasZ3,
      Set(),
      groundOnly = Map("Bag Operations" -> z3BagUnionModels)),
    SolverInfo("smt-cvc4", () => SolverFactory.hasCVC4,
      Set(FloatingPoint, BagAlgebra, NestedArrays),
      groundOnly = cvcGroundOnly),
    SolverInfo("smt-cvc5", () => SolverFactory.hasCVC5,
      Set(BagAlgebra, NestedArrays),
      groundOnly = cvcGroundOnly),
    SolverInfo("smt-bitwuzla", () => SolverFactory.hasBitwuzla,
      Set(Integers, Reals, BitVectorIntConversions, Strings, Sets, Bags, BagAlgebra, Maps, NestedArrays, ADTs,
        Quantifiers, TypeParameters)),
    SolverInfo("princess", () => true,
      Set(BitVectors, FloatingPoint, Sets, BagAlgebra, Maps, NestedArrays),
      // Times out on conjunctions of string checks that it solves quickly one by one
      batchSize = 1,
      groundOnly = Map(
        "BigInt Division and Modulo" -> "throws on division by a variable, which Presburger arithmetic lacks",
      ),
      knownIssues = Map(
        "Simple Bag Operations" -> "struggles with bit-vector keys in bags, as in sets and maps",
        "Bag with several multiplicities" -> "returns Unknown after about two minutes",
        "Function returning bags" -> "crashes (None.get) extracting a function whose results are bags",
        "Function call over bit-vectors" -> "hangs on function calls over bit-vectors",
      )),
  )

  /** Solvers whose absence fails the tests instead of ignoring them, set with
    * `-Dinox.require-solvers=smt-z3,smt-cvc5` (or `all`).
    */
  lazy val requiredSolvers: Set[String] =
    Option(System.getProperty("inox.require-solvers")).toSet
      .flatMap(_.split(",").map(_.trim).filter(_.nonEmpty))
      .flatMap(name => if (name == "all") solvers.map(_.name) else Seq(name))
}

/** Runs each test once per solver of [[SolverTestSuite.solvers]] that supports the features
  * the test requires.
  *
  * Tests that fail on a solver because of a known bug are ignored and list the bug in their name.
  * A solver that isn't installed shows up as ignored tests, unless it is listed in
  * `inox.require-solvers`, in which case its tests fail.
  *
  * The tests of a suite run in parallel (each on its own instance of the suite), since a suite's
  * slowest solvers would otherwise run one after another.
  */
trait SolverTestSuite extends AnyFunSuite with org.scalatest.ParallelTestExecution {
  import SolverTestSuite._
  import inox.trees._
  import SolverResponses._

  /** The symbols of the program the tests are solved in. */
  protected def symbols: Symbols = NoSymbols
  protected final lazy val program: InoxProgram = InoxProgram(symbols)
  protected given PrinterOptions = PrinterOptions(symbols = Some(symbols))

  /** Checks that take longer than this fail with Unknown instead of hanging the suite. */
  protected def checkTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(120, "s")

  protected def solver(ctx: Context): SimpleSolverAPI { val program: InoxProgram } =
    SimpleSolverAPI(program.getSolver(ctx).withTimeout(checkTimeout))

  /** Checks that the value the solver finds for `e` is `expected`.
    *
    * `e` is checked twice: as is, and with each of its literals replaced by a variable equal to
    * it. Ground expressions are mostly evaluated by the simplifier before they reach the solver,
    * so only the second form checks how the solver encodes and evaluates each operation.
    *
    * Both forms are checked when the test ends, together with the test's other checks: one query
    * per [[SolverInfo.batchSize]] checks instead of one per check keeps the suites fast.
    *
    * `e` must also evaluate to `expected` with the recursive evaluator when it has no free
    * variables, so that the evaluator and the solvers agree, and survive a round trip through the
    * serializer.
    */
  protected def check(s: SimpleSolverAPI { val program: InoxProgram }, e: Expr, expected: Expr): Unit = {
    // Expressions with free variables, such as the encoding of FPToBinary, have no value to evaluate to
    if (exprOps.variablesOf(e).isEmpty) {
      evaluator.eval(e) match {
        case evaluators.EvaluationResults.Successful(value) =>
          assert(value == expected, s"for '$e' with the evaluator")
        case got => fail(s"Evaluation of '$e' failed with $got.")
      }
    }

    assert(serializer.deserialize[Expr](serializer.serialize(e)) == e, s"for '$e' after serialization")

    val tpe = e.getType(using symbols)
    solveLater(s, PendingCheck(Variable.fresh("v", tpe), e, Map.empty, expected))

    val (symbolic, literals) = liftLiterals(e)
    if (literals.nonEmpty && !groundOnly.value) {
      solveLater(s, PendingCheck(Variable.fresh("v", tpe), symbolic, literals, expected))
    }
  }

  /** A check that `e`, where each variable of `literals` equals its literal, has the value `expected`. */
  private case class PendingCheck(v: Variable, e: Expr, literals: Map[Expr, Variable], expected: Expr) {
    def constraint: Expr = andJoin(literals.toSeq.map { case (lit, x) => Equals(x, lit) } :+ Equals(v, e))
    def description: String =
      if (literals.isEmpty) s"'$e'"
      else s"'$e' where ${literals.map { case (l, x) => s"$x = $l" }.mkString(", ")}"
  }

  private lazy val evaluator = program.getEvaluator(TestContext.empty)
  private lazy val serializer = utils.Serializer(inox.trees)

  private def solveLater(s: SimpleSolverAPI { val program: InoxProgram }, c: PendingCheck): Unit =
    pendingChecks.value match {
      case Some(pending) => pending += s -> c
      case None => solveChecks(s, Seq(c))
    }

  /** Solves `checks` in one query, and each check on its own when that query fails to pinpoint it. */
  private def solveChecks(s: SimpleSolverAPI { val program: InoxProgram }, checks: Seq[PendingCheck]): Unit = {
    s.solveSAT(andJoin(checks.map(_.constraint))) match {
      case SatWithModel(model) =>
        for (c <- checks) {
          assert(model.vars.get(c.v.toVal) == Some(c.expected), s"for ${c.description}")
        }
      case got if checks.size == 1 =>
        fail(s"Solving of ${checks.head.description} failed with $got.")
      case _ =>
        checks.foreach(c => solveChecks(s, Seq(c)))
    }
  }

  /** The checks of the running test that remain to be solved. */
  private val pendingChecks =
    new scala.util.DynamicVariable[Option[scala.collection.mutable.ArrayBuffer[(SimpleSolverAPI { val program: InoxProgram }, PendingCheck)]]](None)

  /** Runs `body`, then solves the checks it made. */
  private def withBatchedChecks(batchSize: Int)(body: => Unit): Unit = {
    val pending = scala.collection.mutable.ArrayBuffer.empty[(SimpleSolverAPI { val program: InoxProgram }, PendingCheck)]
    pendingChecks.withValue(Some(pending))(body)
    for ((s, checks) <- pending.groupBy(_._1); batch <- checks.map(_._2).grouped(batchSize)) {
      solveChecks(s, batch.toSeq)
    }
  }

  /** Whether the running test only checks ground expressions (see [[SolverInfo.groundOnly]]). */
  private val groundOnly = new scala.util.DynamicVariable(false)

  /** Replaces the literals of `e` with fresh variables, and returns the variable of each literal. */
  protected def liftLiterals(e: Expr): (Expr, Map[Expr, Variable]) = {
    var literals = Map.empty[Expr, Variable]
    val lifted = exprOps.postMap {
      case lit: Literal[?] =>
        Some(literals.getOrElse(lit, {
          val x = Variable.fresh(s"lit${literals.size}", lit.getType(using symbols))
          literals += lit -> x
          x
        }))
      case _ => None
    }(e)
    (lifted, literals)
  }

  /** Options shared by all tests of the suite. */
  protected def options: Seq[OptionValue[?]] = Seq.empty

  protected def solverInfos: Seq[SolverInfo] = solvers

  protected def contextFor(solver: String): Context =
    TestContext(Options(options :+ optSelectedSolvers(Set(solver))))

  /** Registers `body` once per solver that supports all of `requires`. */
  protected def test(name: String, requires: Feature*)(body: Context => Unit): Unit = {
    // Workaround for a compiler crash caused by calling super.test
    def superTest(self: AnyFunSuite, name: String)(body: => Unit): Unit = self.test(name)(body)
    def superIgnore(self: AnyFunSuite, name: String)(body: => Unit): Unit = self.ignore(name)(body)

    for (info <- solverInfos if info.supports(requires)) {
      val testName = s"$name solver=${info.name}"
      if (info.knownIssues.contains(name)) {
        superIgnore(this, s"$testName (known issue: ${info.knownIssues(name)})")(())
      } else if (info.available() && info.groundOnly.contains(name)) {
        superTest(this, s"$testName (ground checks only: ${info.groundOnly(name)})") {
          groundOnly.withValue(true)(withBatchedChecks(info.batchSize)(body(contextFor(info.name))))
        }
      } else if (info.available()) {
        superTest(this, testName)(withBatchedChecks(info.batchSize)(body(contextFor(info.name))))
      } else if (requiredSolvers(info.name)) {
        superTest(this, testName)(fail(s"Solver ${info.name} is required but isn't available"))
      } else {
        superIgnore(this, testName)(())
      }
    }
  }
}
