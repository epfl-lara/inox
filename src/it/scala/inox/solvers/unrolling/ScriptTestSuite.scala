/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package unrolling

import java.io.File

/** Base class of the unrolling suites whose tests are SMT-LIB 3 scripts.
  *
  * Each script in `src/it/resources/regression/smtlib3/<directory>` is a test, which runs every
  * `check-sat` query of the script. The scripts are plain SMT-LIB 3 that the Inox command line
  * also accepts, and describe their expectations with attributes that solvers ignore:
  *
  *  - `(set-info :status sat|unsat|unknown)` is the expected result of the next queries, where
  *    `unknown` means neither satisfiable nor unsatisfiable.
  *  - `(set-info :inox-may-be-unknown true)` also accepts an unknown result, for queries that
  *    the solver can't decide but mustn't answer wrongly.
  *  - `(set-option :<name> <value>)` sets the Inox option `--<name>=<value>` for the next
  *    queries, e.g. `(set-option :feeling-lucky true)`.
  */
abstract class ScriptTestSuite(directory: String) extends UnrollingTestSuite with ResourceUtils {

  /** Whether and how `file` runs in the context `ctx`, e.g. to skip it on some solvers. */
  protected def filter(ctx: Context, file: File): FilterStatus = Test

  /** The context of a query, from the test's context and the query's options. */
  protected def queryContext(ctx: Context, query: tip.Parser.Query): Context = {
    val options = query.options.toSeq.map { case (name, value) =>
      val optDef = inox.Main.options.keys.find(_.name == name).getOrElse {
        fail(s"unknown option $name at ${query.pos}")
      }
      optDef.parse(value)(using ctx.reporter)
    }
    ctx.withOpts(options*)
  }

  protected def runQuery(query: tip.Parser.Query)(using ctx: Context): Unit = {
    val status = query.status.getOrElse(fail(s"no status for the query at ${query.pos}"))
    val mayBeUnknown = query.infos.get("inox-may-be-unknown").contains("true")
    val qctx = queryContext(ctx, query)
    // as in the command line, the quantifier mode is a mode of the program
    val inference = transformers.PropositionInference(inox.trees)
    val program = InoxProgram(inference.transform(query.program.symbols
      .withQuantifiers(qctx.options.findOptionOrDefault(ast.optQuantifiers))))
    val expr = inference.transform(query.expr)(using program.symbols)
    val factory = program.getSolver(qctx)
    // as in the command line, the timeout applies to each query
    val res = qctx.options.findOption(optTimeout) match {
      case Some(t) if query.options.contains(optTimeout.name) =>
        SimpleSolverAPI(factory.withTimeout(t)).solveSAT(expr)
      case _ =>
        SimpleSolverAPI(factory).solveSAT(expr)
    }
    val ok = status match {
      case "sat" => res.isSAT || (mayBeUnknown && !res.isUNSAT)
      case "unsat" => res.isUNSAT || (mayBeUnknown && !res.isSAT)
      case "unknown" => !res.isSAT && !res.isUNSAT
      case _ => fail(s"unexpected status $status at ${query.pos}")
    }
    assert(ok, s"expected $status but got $res for the query at ${query.pos}")
  }

  /** The scripts of the suite, in alphabetical order. */
  protected lazy val scripts: Seq[File] =
    resourceFiles(s"regression/smtlib3/$directory", _.endsWith(".smt3")).sortBy(_.getName)

  for (file <- scripts) {
    test(file.getName.stripSuffix(".smt3"), filter(_, file)) {
      for (query <- smtlib3.Parser(file).parseQueries) runQuery(query)
    }
  }
}
