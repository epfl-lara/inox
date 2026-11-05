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
    * on ground expressions (see [[SolverTestSuite.check]]), and how many variable-form checks it
    * solves in one query.
    */
  case class SolverInfo(
    name: String,
    available: () => Boolean,
    unsupported: Set[Feature],
    knownIssues: Map[String, String] = Map.empty,
    groundOnly: Map[String, String] = Map.empty,
    symbolicBatchSize: Int = 8
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
      knownIssues = Map(
        "Function calls across push and pop" -> "returns Unknown once functions unfolded before a pop are called again",
      ),
      groundOnly = Map("Bag Operations" -> z3BagUnionModels)),
    SolverInfo("unrollz3", () => SolverFactory.hasNativeZ3,
      Set(BitVectorIntConversions, FloatingPoint),
      groundOnly = Map("Bag Operations" -> z3BagUnionModels)),
    SolverInfo("smt-z3", () => SolverFactory.hasZ3,
      Set(),
      knownIssues = Map("Reset" -> "reset() also drops the declarations and options set up when the solver starts"),
      groundOnly = Map("Bag Operations" -> z3BagUnionModels)),
    SolverInfo("smt-cvc4", () => SolverFactory.hasCVC4,
      Set(FloatingPoint, BagAlgebra, NestedArrays),
      knownIssues = Map("Reset" -> "reset() also drops the declarations and options set up when the solver starts"),
      groundOnly = cvcGroundOnly),
    SolverInfo("smt-cvc5", () => SolverFactory.hasCVC5,
      Set(BagAlgebra, NestedArrays),
      knownIssues = Map("Reset" -> "reset() also drops the declarations and options set up when the solver starts"),
      groundOnly = cvcGroundOnly),
    SolverInfo("smt-bitwuzla", () => SolverFactory.hasBitwuzla,
      Set(Integers, Reals, BitVectorIntConversions, Strings, Sets, Bags, BagAlgebra, Maps, NestedArrays, ADTs,
        Quantifiers, TypeParameters),
      knownIssues = Map(
        "Reset" -> "reset() also drops the declarations and options set up when the solver starts",
        "Model extraction of Char" -> "returns Unknown for characters",
      )),
    SolverInfo("princess", () => true,
      Set(BitVectors, FloatingPoint, Sets, Bags, BagAlgebra, Maps, NestedArrays),
      // Times out on conjunctions of string checks that it solves quickly one by one
      symbolicBatchSize = 1,
      groundOnly = Map(
        "BigInt Division, Modulo and Remainder" -> "throws on division by a variable, which Presburger arithmetic lacks",
      ),
      knownIssues = Map(
        "Function call over bit-vectors" -> "hangs on function calls over bit-vectors",
        "Function calls across push and pop" -> "crashes once functions unfolded before a pop are called again",
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
  */
trait SolverTestSuite extends AnyFunSuite {
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
    * The second form is checked when the test ends, together with the test's other checks: one
    * query per [[SolverInfo.symbolicBatchSize]] checks instead of one per check keeps the suites fast.
    */
  protected def check(s: SimpleSolverAPI { val program: InoxProgram }, e: Expr, expected: Expr): Unit = {
    val v = Variable.fresh("v", e.getType(using symbols))
    s.solveSAT(Equals(v, e)) match {
      case SatWithModel(model) =>
        assert(model.vars.get(v.toVal) == Some(expected), s"for '$e'")
      case got => fail(s"Solving of '$e' failed with $got.")
    }

    val (symbolic, literals) = liftLiterals(e)
    if (literals.nonEmpty && !groundOnly.value) {
      val c = SymbolicCheck(v, symbolic, literals, expected)
      pendingChecks.value match {
        case Some(pending) => pending += s -> c
        case None => checkSymbolic(s, Seq(c))
      }
    }
  }

  private case class SymbolicCheck(v: Variable, symbolic: Expr, literals: Map[Expr, Variable], expected: Expr) {
    def constraint: Expr = andJoin(literals.toSeq.map { case (lit, x) => Equals(x, lit) } :+ Equals(v, symbolic))
    def description: String = s"'$symbolic' where ${literals.map { case (l, x) => s"$x = $l" }.mkString(", ")}"
  }

  /** Solves `checks` in one query, and each check on its own when that query fails to pinpoint it. */
  private def checkSymbolic(s: SimpleSolverAPI { val program: InoxProgram }, checks: Seq[SymbolicCheck]): Unit = {
    s.solveSAT(andJoin(checks.map(_.constraint))) match {
      case SatWithModel(model) =>
        for (c <- checks) {
          assert(model.vars.get(c.v.toVal) == Some(c.expected), s"for ${c.description}")
        }
      case got if checks.size == 1 =>
        fail(s"Solving of ${checks.head.description} failed with $got.")
      case _ =>
        checks.foreach(c => checkSymbolic(s, Seq(c)))
    }
  }

  /** The variable-form checks of the running test that remain to be solved. */
  private val pendingChecks =
    new scala.util.DynamicVariable[Option[scala.collection.mutable.ArrayBuffer[(SimpleSolverAPI { val program: InoxProgram }, SymbolicCheck)]]](None)

  /** Runs `body`, then solves the variable-form checks it made. */
  private def withSymbolicChecks(batchSize: Int)(body: => Unit): Unit = {
    val pending = scala.collection.mutable.ArrayBuffer.empty[(SimpleSolverAPI { val program: InoxProgram }, SymbolicCheck)]
    pendingChecks.withValue(Some(pending))(body)
    for ((s, checks) <- pending.groupBy(_._1); batch <- checks.map(_._2).grouped(batchSize)) {
      checkSymbolic(s, batch.toSeq)
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
          groundOnly.withValue(true)(body(contextFor(info.name)))
        }
      } else if (info.available()) {
        superTest(this, testName)(withSymbolicChecks(info.symbolicBatchSize)(body(contextFor(info.name))))
      } else if (requiredSolvers(info.name)) {
        superTest(this, testName)(fail(s"Solver ${info.name} is required but isn't available"))
      } else {
        superIgnore(this, testName)(())
      }
    }
  }
}
