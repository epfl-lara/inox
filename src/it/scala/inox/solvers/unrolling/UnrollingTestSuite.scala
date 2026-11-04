/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package unrolling

/** Base trait of the unrolling suites.
  *
  * The unrolling engine (function, lambda, quantifier and type templates, chooses, model
  * finding) is shared by every solver, and the solver suites in `src/test` check that the
  * solvers agree on the encoding and model extraction underneath it. The unrolling suites
  * therefore run against a single solver, `smt-z3` by default (`-Dinox.unrolling.solver=<name>`
  * selects another one), but on every combination of the options that affect unrolling.
  */
trait UnrollingTestSuite extends TestSuite {
  import UnrollingTestSuite._

  /** The combinations of unrolling options each test runs with. */
  protected def optionMatrix: Seq[Seq[OptionValue[?]]] = fullMatrix

  override def configurations = optionMatrix.map { opts =>
    Seq(
      optSelectedSolvers(Set(solverName)),
      optIgnoreModels(false),
      optTimeout(300),
      ast.optPrintUniqueIds(true)
    ) ++ opts
  }

  override protected def optionsString(options: Options): String = {
    super.optionsString(options) +
    " assck=" + options.findOptionOrDefault(optAssumeChecked) +
    " model=" + options.findOptionOrDefault(optModelFinding)
  }
}

object UnrollingTestSuite {
  /** The solver the unrolling suites run against. */
  lazy val solverName: String = Option(System.getProperty("inox.unrolling.solver")).getOrElse("smt-z3")

  /** All combinations of one value from each dimension. */
  def combinations(dimensions: Seq[OptionValue[?]]*): Seq[Seq[OptionValue[?]]] =
    dimensions.foldLeft(Seq(Seq.empty[OptionValue[?]])) { (acc, dimension) =>
      for (opts <- acc; opt <- dimension) yield opts :+ opt
    }

  def both(opt: FlagOptionDef): Seq[OptionValue[?]] = Seq(opt(false), opt(true))

  /** Every combination of the options that affect unrolling. */
  val fullMatrix: Seq[Seq[OptionValue[?]]] = combinations(
    both(optCheckModels),
    both(optFeelingLucky),
    both(optUnrollAssumptions),
    both(optAssumeChecked),
    Seq(optModelFinding(0), optModelFinding(1))
  )
}
