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

  /** A solver checked by the solver suites, with the features it doesn't support and the tests
    * it fails because of known bugs (test name -> reason).
    */
  case class SolverInfo(
    name: String,
    available: () => Boolean,
    unsupported: Set[Feature],
    knownIssues: Map[String, String] = Map.empty
  ) {
    def supports(features: Seq[Feature]): Boolean = features.forall(f => !unsupported(f))
  }

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
      )),
    SolverInfo("unrollz3", () => SolverFactory.hasNativeZ3,
      Set(BitVectorIntConversions, FloatingPoint)),
    SolverInfo("smt-z3", () => SolverFactory.hasZ3,
      Set(),
      knownIssues = Map("Reset" -> "reset() also drops the declarations and options set up when the solver starts")),
    SolverInfo("smt-cvc4", () => SolverFactory.hasCVC4,
      Set(FloatingPoint, BagAlgebra, NestedArrays),
      knownIssues = Map("Reset" -> "reset() also drops the declarations and options set up when the solver starts")),
    SolverInfo("smt-cvc5", () => SolverFactory.hasCVC5,
      Set(BagAlgebra, NestedArrays),
      knownIssues = Map("Reset" -> "reset() also drops the declarations and options set up when the solver starts")),
    SolverInfo("smt-bitwuzla", () => SolverFactory.hasBitwuzla,
      Set(Integers, Reals, BitVectorIntConversions, Strings, Sets, Bags, BagAlgebra, Maps, NestedArrays, ADTs,
        Quantifiers, TypeParameters),
      knownIssues = Map(
        "Reset" -> "reset() also drops the declarations and options set up when the solver starts",
        "Model extraction of Char" -> "returns Unknown for characters",
      )),
    SolverInfo("princess", () => true,
      Set(BitVectors, FloatingPoint, Sets, Bags, BagAlgebra, Maps, NestedArrays),
      knownIssues = Map(
        "Function call over bit-vectors" -> "hangs on function calls over bit-vectors",
        "Function calls across push and pop" -> "crashes once functions unfolded before a pop are called again",
        "Model extraction of (BigInt) => BigInt" -> "returns Unknown when a model contains a function",
        "Lambdas in models" -> "returns Unknown when a model contains a function",
        "higher-order free function applied to free functions" ->
          "evaluates every application of a higher-order free function to the same value",
        "higher-order free function applied to lambdas" ->
          "evaluates every application of a higher-order free function to the same value",
        "higher-order free function applied to constrained functions" ->
          "evaluates every application of a higher-order free function to the same value",
        "higher-order free function with two function parameters" ->
          "evaluates every application of a higher-order free function to the same value",
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

  protected def solver(ctx: Context): SimpleSolverAPI { val program: InoxProgram } =
    SimpleSolverAPI(program.getSolver(ctx))

  /** Checks that the value the solver finds for `e` is `expected`. */
  protected def check(s: SimpleSolverAPI { val program: InoxProgram }, e: Expr, expected: Expr): Unit = {
    val v = Variable.fresh("v", e.getType(using symbols))
    s.solveSAT(Equals(v, e)) match {
      case SatWithModel(model) =>
        assert(model.vars.get(v.toVal) == Some(expected))
      case got => fail(s"Solving of '$e' failed with $got.")
    }
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
      } else if (info.available()) {
        superTest(this, testName)(body(contextFor(info.name)))
      } else if (requiredSolvers(info.name)) {
        superTest(this, testName)(fail(s"Solver ${info.name} is required but isn't available"))
      } else {
        superIgnore(this, testName)(())
      }
    }
  }
}
