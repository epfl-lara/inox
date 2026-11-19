/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

/** The modes of the unfolding that the options select, derived once (see [[Templates.modes]]). */
class UnfoldingModes(options: Options) {

  /** How the solver compares first-class functions (see [[optFunctionEquality]]). */
  val functionEquality: FunctionEquality = options.findOptionOrDefault(optFunctionEquality)

  /** Whether the front-end has checked that nothing fails (see `optAssumeChecked`). Calls then
    * don't unfold their domains, and measures only need to decrease. */
  val assumeChecked: Boolean = options.findOptionOrDefault(optAssumeChecked)

  /** Unless the front-end has checked them, the partial operations that may fail make their path
    * infeasible when they do, like errors, so that the solver agrees with the evaluator (see
    * [[ast.SymbolOps.definedness]]). */
  val guardPartialOperations: Boolean = !assumeChecked

  /** Whether functions are partial, i.e. whether the solver tells apart functions that fail from
    * functions that don't. Only extensional equality observes where functions fail, and under
    * `optAssumeChecked`, the front-end has checked that nothing fails, so functions are total and
    * failures make their paths infeasible instead. */
  val partialFunctions: Boolean = functionEquality == FunctionEquality.Extensional && !assumeChecked

  /** Whether distinct functions have a distinguishing input, that is whether function equality is
    * extensional or unobservable (see [[optFunctionEquality]]).
    *
    * For a pair of functions `f` and `g`, we then introduce fresh witness arguments `ws` such that
    * `f != g ==> f(ws) != g(ws)`, so that extracted models are meaningfully distinct, and lambdas
    * aren't compared structurally. Witnesses of function type are themselves free functions, so the
    * construction recurses on higher-order argument types (see `function-witnesses.md`). Under
    * intensional equality, distinct functions may agree on every input, and models compare them
    * structurally instead. */
  val functionWitnesses: Boolean = functionEquality != FunctionEquality.Intensional

  /** Without function equality, the equality of two lambdas can't be observed, and their distinguishing
    * input is only needed when model extraction must tell them apart (see
    * [[WitnessTemplates.onDemandWitnesses]]). Under extensional equality, lambdas that differ
    * structurally are only equal when they agree on their distinguishing input, and nothing else can
    * refute their equality. Their distinguishing input is then unfolded like those of free functions
    * (see [[WitnessTemplates.witnessEqualities]]): the lambdas are assumed equal when looking for a
    * model, and the input is instantiated when that equality is part of an unsat core.
    *
    * Instantiating them with each new lambda instead doesn't terminate: distinguishing inputs can
    * create lambdas on the spot (eg. in the typing constraints of applications), and each new lambda
    * is compared to all the previous ones. */
  val onDemandLambdaWitnesses: Boolean = functionEquality == FunctionEquality.None

  /** Unless function equality is extensional, whether two functions are equal never constrains their
    * applications, so their distinguishing input is only needed when a model shows both of them. The
    * pairs that involve a free function are therefore left out of the unfolding until then (see
    * [[WitnessTemplates.promoteWitnesses]]). Unfolding all of them instead can make queries much
    * harder: each function term that the unrolling creates is paired with all the previous ones of
    * its type, and the equalities of these pairs are assumed by every model check. */
  val onDemandFreeWitnesses: Boolean = functionEquality != FunctionEquality.Extensional

  /** The generations by which unfoldings are deferred when model finding is on (see
    * [[optModelFinding]]), so that the solver looks for models between them. */
  val deferFactor: Int = 3 * options.findOptionOrDefault(optModelFinding)
}
