/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._
import ast.FreshIdentifier

trait FunctionTemplates { self: Templates =>
  import program._
  import program.trees._
  import program.symbols._

  import functionsManager._

  object FunctionTemplate {

    def apply(
      tfd: TypedFunDef,
      pathVar: (Variable, Encoded),
      arguments: Seq[(Variable, Encoded)],
      condVars: Map[Variable, Encoded],
      exprVars: Map[Variable, Encoded],
      condTree: Map[Variable, Set[Variable]],
      guardedExprs: Map[Variable, Seq[Expr]],
      lambdas: Seq[LambdaTemplate],
      quantifications: Seq[QuantificationTemplate]
    ) : FunctionTemplate = {

      val (clauses, blockers, applications, matchers, templateString) =
        Template.encode(pathVar, arguments, condVars, exprVars, guardedExprs, lambdas, quantifications,
          optCall = Some(tfd))

      val funString : () => String = () => {
        "Template for def " + tfd.signature +
        "(" + tfd.params.map(a => a.id + " : " + a.getType).mkString(", ") + ") : " +
        tfd.returnType + " is :\n" + templateString()
      }

      new FunctionTemplate(
        tfd,
        pathVar,
        arguments.map(_._2),
        condVars,
        exprVars,
        condTree,
        clauses,
        blockers,
        applications,
        matchers,
        lambdas,
        quantifications,
        funString
      )
    }
  }

  class FunctionTemplate private(
    val tfd: TypedFunDef,
    val pathVar: (Variable, Encoded),
    val args: Seq[Encoded],
    val condVars: Map[Variable, Encoded],
    val exprVars: Map[Variable, Encoded],
    val condTree: Map[Variable, Set[Variable]],
    val clauses: Clauses,
    val blockers: Calls,
    val applications: Apps,
    val matchers: Matchers,
    val lambdas: Seq[LambdaTemplate],
    val quantifications: Seq[QuantificationTemplate],
    stringRepr: () => String) extends Template {

    private lazy val str : String = stringRepr()
    override def toString : String = str
  }

  def instantiateCall(blocker: Encoded, fi: Call): Clauses = {
    val gen = nextGeneration(currentGeneration)
    val notBlocker = mkNot(blocker)

    callInfos.get(blocker) match {
      case Some((exGen, origGen, _, exFis)) =>
        // PS: when recycling `b`s, this assertion becomes dangerous.
        // It's better to simply take the max of the generations.
        // assert(exGen == gen, "Mixing the same id "+id+" with various generations "+ exGen+" and "+gen)

        val minGen = gen min exGen

        callInfos += blocker -> (minGen, origGen, notBlocker, exFis + fi)
      case None =>
        callInfos += blocker -> (gen, gen, notBlocker, Set(fi))
    }

    Seq.empty
  }

  private[unrolling] object functionsManager extends Manager {
    // Function instantiations have their own defblocker
    private[FunctionTemplates] val defBlockers = new IncrementalMap[Call, Encoded]()

    // Keep which function invocation is guarded by which guard,
    // also specify the generation of the blocker.
    private[FunctionTemplates] val callInfos   = new IncrementalMap[Encoded, (Int, Int, Encoded, Set[Call])]()

    val incrementals: Seq[IncrementalState] = Seq(callInfos, defBlockers)

    def unrollGeneration: Option[Int] =
      if (callInfos.isEmpty) None
      else Some(callInfos.values.map(_._1).min)

    def satisfactionAssumptions: Seq[Encoded] = callInfos.map(_._2._3).toSeq
    def refutationAssumptions: Seq[Encoded] = Seq.empty

    def promoteBlocker(b: Encoded): Boolean = {
      if (callInfos contains b) {
        val (_, origGen, notB, fis) = callInfos(b)
        callInfos += b -> (currentGeneration, origGen, notB, fis)
        true
      } else {
        false
      }
    }

    def unroll: Clauses = if (callInfos.isEmpty) Seq.empty else {
      val blockers = callInfos.filter(_._2._1 <= currentGeneration).toSeq.map(_._1)

      val newClauses = new scala.collection.mutable.ListBuffer[Encoded]

      val newCallInfos = blockers.flatMap(id => callInfos.get(id).map(id -> _))
      callInfos --= blockers

      for ((blocker, (gen, _, _, calls)) <- newCallInfos; call @ Call(tfd, args) <- calls) {
        val newCls = new scala.collection.mutable.ListBuffer[Encoded]

        val defBlocker = defBlockers.get(call) match {
          case Some(defBlocker) =>
            // we already have defBlocker => f(args) = body
            defBlocker

          case None =>
            // we need to define this defBlocker and link it to definition
            val defBlocker = encodeSymbol(Variable(FreshIdentifier("d", true), BooleanType))
            defBlockers += call -> defBlocker

            val template = mkTemplate(tfd)
            //reporter.debug(template)

            val newExprs = template.instantiate(defBlocker, args)

            newCls ++= newExprs
            defBlocker
        }

        // We connect it to the defBlocker:   blocker => defBlocker
        if (defBlocker != blocker) {
          newCls += mkImplies(blocker, defBlocker)
        }

        ctx.reporter.debug("Unrolling behind "+call+" ("+newCls.size+")")
        for (cl <- newCls) {
          ctx.reporter.debug("  . "+cl)
        }

        newClauses ++= newCls
      }

      ctx.reporter.debug(s"   - ${newClauses.size} new clauses")

      newClauses.toSeq
    }
  }
}
