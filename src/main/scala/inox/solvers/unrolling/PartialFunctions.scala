/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

/** Partial functions: a function or a lambda fails on the inputs on which its evaluation fails
  * (an error, an assumption that doesn't hold, or an undefined operation, see
  * [[TemplateGenerator.failureSymbols]]). Each call and each application has a literal for whether
  * it fails, which the instance of the callee's body defines when the call or application is unfolded
  * (see [[Instantiation.itemClauses]]). Formulas assert that the calls and applications that they reach
  * don't fail, so that the paths that fail stay infeasible, while the distinguishing inputs of
  * functions tell apart a function that fails from one that doesn't (see [[instantiateWitness]]).
  * Free functions may be partial too: nothing constrains whether their applications fail, unless a
  * formula reaches them, and the extracted models of free functions fail where these do. */
trait PartialFunctions { self: Templates =>
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  import partialFunctionState._

  private[unrolling] object partialFunctionState extends IncrementalStateWrapper {
    private[PartialFunctions] val callFailures = new IncrementalMap[(Callee, Seq[Encoded]), Encoded]
    private[PartialFunctions] val appFailures = new IncrementalMap[(Encoded, FunctionType, Seq[Encoded]), Encoded]

    val incrementals: Seq[IncrementalState] = Seq(callFailures, appFailures)
  }

  /** Whether the call of `callee` on `args` fails. */
  private[unrolling] def callFailure(callee: Callee, args: Seq[Encoded]): Encoded =
    callFailures.cached(callee -> args)(encodeSymbol(Variable.fresh("fails", BooleanType(), true)))

  /** Whether the application of `caller` of type `tpe` to `args` fails.
    *
    * Unlike the bodies of functions, free functions aren't determined by their applications, so the
    * failures of applications are a first-order uninterpreted predicate of their caller and
    * arguments, whose congruence makes applications to equal arguments fail alike. */
  private[unrolling] def appFailure(caller: Encoded, tpe: FunctionType, args: Seq[Encoded]): Encoded =
    appFailures.cached((caller, tpe, args)) {
      val fails = appFailurePredicates.getOrElseUpdate(tpe, mkFunction("fails", tpe +: tpe.from, BooleanType()))
      // the predicate is mirrored by a literal, whose value models give on every backend
      val literal = encodeSymbol(Variable.fresh("fails", BooleanType(), true))
      failureDefinitions += mkEquals(literal, mkFunApp(fails, caller +: args))
      literal
    }
  private val appFailurePredicates = scala.collection.mutable.Map.empty[FunctionType, Function]
  private val failureDefinitions = scala.collection.mutable.ListBuffer.empty[Encoded]

  /** The definitions of the failure literals of the applications created since the last call. */
  private[unrolling] def newFailureDefinitions(): Clauses = {
    val clauses = failureDefinitions.toSeq
    failureDefinitions.clear()
    clauses
  }

  /** The failure literals of the applications of type `tpe`, by caller and arguments. */
  def appFailureLiterals(tpe: FunctionType): Seq[((Encoded, Seq[Encoded]), Encoded)] =
    appFailures.toSeq.collect { case ((caller, `tpe`, args), fails) => (caller, args) -> fails }

  private[unrolling] def callFailure(call: Call): Encoded = callFailure(call.callee, call.args.map(_.encoded))
  private[unrolling] def appFailure(app: App): Encoded = appFailure(app.caller, app.tpe, app.args.map(_.encoded))
}
