/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

import scala.collection.mutable.{Set => MutableSet, Map => MutableMap}

trait FunctionTemplates { self: Templates =>
  import program._
  import program.trees._
  import program.symbols._

  import functionsManager._

  object FunctionTemplate {
    private val cache: MutableMap[TypedFunDef, FunctionTemplate] = MutableMap.empty

    def apply(tfd: TypedFunDef): FunctionTemplate = cache.getOrElseUpdate(tfd, {
      val timer = ctx.timers.solvers.simplify.start()
      val lambdaBody: Expr = simplifyFormula(tfd.fullBody, simplify)
      timer.stop()

      val fdArgs: Seq[Variable] = tfd.params.map(_.toVariable)
      val lambdaArgs: Seq[Variable] = lambdaArguments(lambdaBody)
      val call: Expr = tfd.applied(fdArgs)

      val callEqBody: Seq[(Expr, Expr)] = liftedEquals(call, lambdaBody, lambdaArgs) :+ (call -> lambdaBody)

      val start = Variable.fresh("start", BooleanType, true)
      val pathVar = start -> encodeSymbol(start)
      val arguments = (fdArgs ++ lambdaArgs).map(v => v -> encodeSymbol(v))
      val substMap = arguments.toMap + pathVar

      val tmplClauses = callEqBody.foldLeft(emptyClauses) { case (clsSet, (app, body)) =>
        val (p, cls) = mkExprClauses(start, body, substMap)
        clsSet ++ cls + (start -> Equals(app, p))
      }

      val (contents, str) = Template.contents(
        pathVar, arguments, tmplClauses, optCall = Some(tfd))

      val funString : () => String = () => {
        "Template for def " + tfd.signature +
        "(" + tfd.params.map(a => a.id + " : " + a.getType).mkString(", ") + ") : " +
        tfd.returnType + " is :\n" + str()
      }

      new FunctionTemplate(contents, funString)
    })
  }

  class FunctionTemplate private(
    val contents: TemplateContents,
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

  def getCalls: Seq[(Encoded, Call)] = defBlockers.toList.map(p => p._2 -> p._1)

  protected def lambdaArguments(expr: Expr): Seq[Variable] = expr match {
    case Lambda(args, body) => args.map(_.toVariable.freshen) ++ lambdaArguments(body)
    case Assume(pred, body) => lambdaArguments(body)
    case IsTyped(_, FirstOrderFunctionType(from, to)) => from.map(tpe => Variable.fresh("x", tpe, true))
    case _ => Seq.empty
  }

  protected def liftedEquals(call: Expr, body: Expr, args: Seq[Variable], inlineFirst: Boolean = false) = {
    def rec(c: Expr, b: Expr, args: Seq[Variable], inline: Boolean): Seq[(Expr, Expr)] = c.getType match {
      case FunctionType(from, to) =>
        def apply(e: Expr, es: Seq[Expr]): Expr = e match {
          case _: Lambda if inline => application(e, es)
          case Assume(pred, l: Lambda) if inline => Assume(pred, application(l, es))
          case _ => Application(e, es)
        }

        val (currArgs, nextArgs) = args.splitAt(from.size)
        val (appliedCall, appliedBody) = (apply(c, currArgs), apply(b, currArgs))
        rec(appliedCall, appliedBody, nextArgs, false) :+ (appliedCall -> appliedBody)
      case _ =>
        assert(args.isEmpty, "liftedEquals should consume all provided arguments")
        Seq.empty
    }

    rec(call, body, args, inlineFirst)
  }

  protected def flatTypes(tfd: TypedFunDef): (Seq[Type], Type) = {
    val (appTps, appRes) = tfd.returnType match {
      case FirstOrderFunctionType(from, to) => (from, to)
      case tpe => (Seq.empty, tpe)
    }

    (tfd.params.map(_.tpe) ++ appTps, appRes)
  }

  private val callCache: MutableMap[TypedFunDef, (Seq[Encoded], Encoded)] = MutableMap.empty
  private[unrolling] def mkCall(tfd: TypedFunDef, args: Seq[Encoded]): Encoded = {
    val (asT, call) = callCache.getOrElseUpdate(tfd, {
      val as = flatTypes(tfd)._1.map(tpe => Variable.fresh("x", tpe, true))
      val asT = as.map(encodeSymbol)

      val (fdArgs, appArgs) = as.splitAt(tfd.params.size)
      val call = mkApplication(tfd.applied(fdArgs), appArgs)
      (asT, mkEncoder((as zip asT).toMap)(call))
    })

    mkSubstituter((asT zip args).toMap)(call)
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

      val thisCallInfos = blockers.flatMap(id => callInfos.get(id).map(id -> _))
      callInfos --= blockers

      val remainingBlockers = MutableSet.empty ++ blockers

      for ((blocker, (gen, _, _, calls)) <- thisCallInfos if calls.nonEmpty && !abort && !pause;
           _ = remainingBlockers -= blocker;
           call @ Call(tfd, args) <- calls if !abort) {
        val newCls = new scala.collection.mutable.ListBuffer[Encoded]

        val defBlocker = defBlockers.get(call) match {
          case Some(defBlocker) =>
            // we already have defBlocker => f(args) = body
            defBlocker

          case None =>
            // we need to define this defBlocker and link it to definition
            val defBlocker = encodeSymbol(Variable.fresh("d", BooleanType, true))

            // we generate helper equality clauses that stem from purity
            for ((pcall, pblocker) <- defBlockers if pcall.tfd == tfd) {
              val (argTpes, resTpe) = flatTypes(tfd)

              def makeEq(tpe: Type, e1: Encoded, e2: Encoded): Encoded =
                if (!unrollEquality(tpe)) mkEquals(e1, e2) else {
                  mkApp(equalitySymbol(tpe)._2, FunctionType(Seq(tpe, tpe), BooleanType), Seq(e1, e2))
                }

              if (argTpes.exists(unrollEquality) || unrollEquality(resTpe)) {
                val argPairs = (pcall.args zip args)
                val cond = mkAnd((argTpes zip argPairs).map {
                  case (tpe, (e1, e2)) => makeEq(tpe, e1.encoded, e2.encoded)
                } : _*)
                val entail = makeEq(resTpe,
                  mkCall(tfd, pcall.args.map(_.encoded)),
                  mkCall(tfd, args.map(_.encoded)))
                newClauses += mkImplies(mkAnd(pblocker, defBlocker, cond), entail)
              }
            }

            defBlockers += call -> defBlocker

            newCls ++= FunctionTemplate(tfd).instantiate(defBlocker, args)
            defBlocker
        }

        // We connect it to the defBlocker: blocker => defBlocker
        if (defBlocker != blocker) {
          registerImplication(blocker, defBlocker)
          newCls += mkImplies(blocker, defBlocker)
        }

        ctx.reporter.debug("Unrolling behind "+call+" ("+newCls.size+")")
        for (cl <- newCls) {
          ctx.reporter.debug("  . "+cl)
        }

        newClauses ++= newCls
      }

      for ((b, (gen, origGen, notB, calls)) <- thisCallInfos if remainingBlockers(b)) callInfos.get(b) match {
        case Some((newGen, _, _, newCalls)) => callInfos += b -> (gen min newGen, origGen, notB, calls ++ newCalls)
        case None => callInfos += b -> (gen, origGen, notB, calls)
      }

      ctx.reporter.debug(s"   - ${newClauses.size} new clauses")

      newClauses.toSeq
    }
  }
}
