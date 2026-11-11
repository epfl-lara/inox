/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package unrolling

/** Regression suite for type unrolling and quantifier instantiation.
  *
  * Values of refinement, Sigma, Pi and ADT types are constrained by type templates (see
  * [[TypeTemplates]] and `TemplateGenerator.mkTypeClauses`). The tests below check these
  * constraints through their observable effect on queries, in the places where they matter:
  *
  *  - quantifier domains, where a type check may be false and must then simply disable the
  *    instantiation (positive polarity) or the counterexample (negative polarity);
  *  - predicates that may falsify their path (`assume`, `choose`, and calls into either);
  *  - ADT invariants, with the free and the contract generators;
  *  - type parameters and higher-order values, including closure captures;
  *  - the same type checked both inside and outside of a quantifier domain in one query.
  *
  * Most tests come in pairs: a valid query, and an invalid one that a too strong (or unsound)
  * encoding would prove. The queries that check positive quantifier domains have the form
  * `(forall (w: T) => g(w) == 1) ==> g(v) == 1`, which is valid iff `v` belongs to `T`, and those
  * that check negative quantifier domains have the form `forall (w: T) => p(w)`.
  *
  * The tests are the scripts in `regression/smtlib3/type-unrolling`. A valid query `e` is written
  * as `(assert (not e))` with status `unsat`, and an invalid one with status `sat`. The scripts in
  * `known-issues` currently get a wrong or no answer, and are ignored until fixed.
  */
class TypeUnrollingSuite extends ScriptTestSuite("type-unrolling") {
  import trees._

  // Model checks are set per query, see `queryContext`.
  override protected def optionMatrix = UnrollingTestSuite.combinations(
    UnrollingTestSuite.both(optFeelingLucky),
    UnrollingTestSuite.both(optUnrollAssumptions),
    UnrollingTestSuite.both(optAssumeChecked),
    Seq(optModelFinding(0), optModelFinding(1))
  )

  private def containsQuantifiers(query: tip.Parser.Query): Boolean = {
    val symbols = query.program.symbols
    def local(e: Expr) = exprOps.exists { case _: Forall => true case _ => false }(e)
    local(query.expr) || exprOps.functionCallsOf(query.expr).exists { fi =>
      (symbols.transitiveCallees(fi.id) + fi.id).exists(id => local(symbols.getFunction(id).fullBody))
    }
  }

  // Countermodels of quantified formulas can't be checked by evaluation, so models are only
  // checked for queries without quantifiers, and for which the script doesn't disable them
  // (models of functions with function-typed domains, whose validation quantifies over functions).
  override protected def queryContext(ctx: Context, query: tip.Parser.Query): Context = {
    val checkModels = !containsQuantifiers(query) && !query.options.get(optCheckModels.name).contains("false")
    super.queryContext(ctx, query).withOpts(optCheckModels(checkModels))
  }

  for (file <- resourceFiles("regression/smtlib3/type-unrolling/known-issues", _.endsWith(".smt3")).sortBy(_.getName)) {
    ignore("known issue: " + file.getName.stripSuffix(".smt3")) {
      for (query <- smtlib3.Parser(file).parseQueries) runQuery(query)
    }
  }
}
