/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._
import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

trait LambdaTemplates { self: Templates =>
  import program._
  import program.trees._
  import program.symbols._

  import lambdasManager._
  import datatypesManager._
  import quantificationsManager._

  /** Represents a POTENTIAL application of a first-class function in the unfolding procedure
    *
    * The [[equals]] condition guards the application for equality of the concrete caller with
    * the provided template in order to perform dynamic dispatch.
    */
  case class TemplateAppInfo(template: Either[LambdaTemplate, Encoded], equals: Encoded, args: Seq[Arg]) {
    override def toString = {
      val caller = template match {
        case Left(tmpl) => asString(tmpl.ids._2)
        case Right(c) => asString(c)
      }

      caller + "|" + asString(equals) + args.map {
        case Right(m) => m.toString
        case Left(v) => asString(v)
      }.mkString("(", ",", ")")
    }
  }

  object TemplateAppInfo {
    def apply(template: LambdaTemplate, equals: Encoded, args: Seq[Arg]): TemplateAppInfo =
      TemplateAppInfo(Left(template), equals, args)

    def apply(caller: Encoded, equals: Encoded, args: Seq[Arg]): TemplateAppInfo =
      TemplateAppInfo(Right(caller), equals, args)
  }


  /** Constructor object for [[LambdaTemplate]]
    *
    * The [[apply]] methods performs some pre-processing before creating
    * an instance of [[LambdaTemplate]].
    */
  object LambdaTemplate {

    def apply(
      pathVar: (Variable, Encoded),
      lambda: Lambda,
      substMap: Map[Variable, Encoded]
    ): LambdaTemplate = {
      val idArgs: Seq[Variable] = lambdaArguments(lambda)
      val trArgs: Seq[Encoded] = idArgs.map(v => substMap.getOrElse(v, encodeSymbol(v)))

      val (realLambda, structure, depSubst) = mkExprStructure(pathVar._1, lambda, substMap)
      val depClosures = exprOps.variablesOf(lambda).flatMap(substMap.get)

      val tpe = lambda.getType.asInstanceOf[FunctionType]
      val lid = Variable.fresh("lambda", tpe, true)
      val appEqBody: Seq[(Expr, Expr)] = liftedEquals(lid, realLambda, idArgs, inlineFirst = true)

      val clauseSubst: Map[Variable, Encoded] = depSubst ++ (idArgs zip trArgs)
      val tmplClauses = appEqBody.foldLeft(emptyClauses) { case (clsSet, (app, body)) =>
        val (p, cls) = mkExprClauses(pathVar._1, body, clauseSubst)
        clsSet ++ cls + (pathVar._1 -> Equals(app, p))
      }

      val lidT = encodeSymbol(lid)
      val (contents, str) = Template.contents(pathVar, idArgs zip trArgs, tmplClauses,
        substMap = depSubst + (lid -> lidT), optApp = Some(lidT -> tpe))

      val lambdaString : () => String = () => {
        "Template for lambda " + lid + ": " + lambda + " is :\n" + str()
      }

      new LambdaTemplate(lid -> lidT, contents, structure, depClosures, lambda, lambdaString, false)
    }
  }

  class LambdaTemplate private (
    val ids: (Variable, Encoded),
    val contents: TemplateContents,
    val structure: TemplateStructure,
    val closures: Set[Encoded],
    val lambda: Lambda,
    private[unrolling] val stringRepr: () => String,
    private val isConcrete: Boolean) extends Template {

    val tpe = bestRealType(ids._1.getType).asInstanceOf[FunctionType]

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): LambdaTemplate = new LambdaTemplate(
      ids._1 -> substituter(ids._2),
      contents.substitute(substituter, msubst),
      structure.substitute(substituter, msubst),
      closures.map(substituter),
      lambda, stringRepr, isConcrete)

    /** This must be called right before returning the clauses in [[structure]]`.instantiation` ! */
    def concretize(idT: Encoded): LambdaTemplate = {
      assert(!isConcrete, "Can't concretize concrete lambda template")
      val substituter = mkSubstituter(Map(ids._2 -> idT) ++ structure.instantiationSubst)
      new LambdaTemplate(ids._1 -> idT,
        contents.substitute(substituter, Map.empty),
        structure, closures, lambda, stringRepr, true)
    }

    override def instantiate(blocker: Encoded, args: Seq[Arg]): Clauses = {
      val (b, clauses) = encodeBlockers(Set(blocker, contents.pathVar._2))
      clauses ++ super.instantiate(b, args)
    }

    private lazy val str : String = stringRepr()
    override def toString : String = str
  }

  private val appCache: MutableMap[FunctionType, (Encoded, Seq[Encoded], Encoded)] = MutableMap.empty
  private[unrolling] def mkApp(caller: Encoded, tpe: FunctionType, args: Seq[Encoded]): Encoded = {
    val (vT, asT, app) = appCache.getOrElseUpdate(tpe, {
      val v = Variable.fresh("f", tpe)
      val as = tpe.from.map(tp => Variable.fresh("x", tp, true))
      val (vT, asT) = (encodeSymbol(v), as.map(encodeSymbol))
      (vT, asT, mkEncoder(Map(v -> vT) ++ (as zip asT))(Application(v, as)))
    })

    mkSubstituter(Map(vT -> caller) ++ (asT zip args))(app)
  }

  def mkFlatApp(caller: Encoded, tpe: FunctionType, args: Seq[Encoded]): Encoded = tpe.to match {
    case ft: FunctionType => mkFlatApp(mkApp(caller, tpe, args.take(tpe.from.size)), ft, args.drop(tpe.from.size))
    case _ => mkApp(caller, tpe, args)
  }

  def registerFunction(b: Encoded, tpe: FunctionType, f: Encoded): Clauses = {
    ctx.reporter.debug(s"-> registering free function $b ==> $f: $tpe")
    val ft = bestRealType(tpe).asInstanceOf[FunctionType]
    freeFunctions += ft -> (freeFunctions(ft) + (b -> f))

    var clauses: Clauses = Seq.empty
    lazy val gen = nextGeneration(currentGeneration)
    for (app @ (_, App(caller, _, args, _)) <- applications(ft)) {
      if (f == caller) {
        // We unroll this app immediately to increase performance for model finding with quantifiers
        val (lastB, nextB) = nextAppBlocker(app)
        clauses :+= mkEquals(lastB, mkOr(b, nextB))
      } else {
        val cond = mkAnd(b, mkEquals(f, caller))
        registerAppInfo(gen, app, Right(f), cond, args)
      }
    }

    if (ft.from.isEmpty) clauses ++= (for {
      template <- byType(ft).values.toList
      if canEqual(template.ids._2, f) && isPureTemplate(template)
    } yield {
      val (tmplApp, fApp) = (mkApp(template.ids._2, ft, Seq.empty), mkApp(f, ft, Seq.empty))
      mkImplies(mkAnd(b, template.start, mkEquals(tmplApp, fApp)), mkEquals(template.ids._2, f))
    })

    clauses
  }

  private def isPureTemplate(template: LambdaTemplate): Boolean = template.structure.body match {
    case Lambda(_, _: Variable) => true
    case _ => false
  }

  private def registerAppInfo(gen: Int, key: (Encoded, App), template: Either[LambdaTemplate, Encoded], equals: Encoded, args: Seq[Arg]): Unit = {
    val info = TemplateAppInfo(template, equals, args)
    appInfos.get(key) match {
      case Some((exGen, origGen, exInfo)) =>
        val minGen = gen min exGen
        appInfos += key -> (minGen, origGen, exInfo + info)

      case None =>
        appInfos += key -> (gen, gen, Set(info))
    }
  }

  private def registerAppBlocker(app: (Encoded, App), blocker: Encoded): Unit = {
    appBlockers.get(app).foreach(blockerToApps -= _)
    appBlockers += app -> blocker
    blockerToApps += blocker -> app
  }

  private def nextAppBlocker(app: (Encoded, App)): (Encoded, Encoded) = {
    val nextB = encodeSymbol(Variable.fresh("b_lambda", BooleanType, true))
    val lastB = appBlockers(app)
    registerAppBlocker(app, nextB)
    (lastB, nextB)
  }

  def registerLambda(pointer: Encoded, target: Encoded): Boolean = byID.get(target) match {
    case Some(template) =>
      byID += pointer -> template
      applications += template.tpe -> applications(template.tpe).filterNot(_._2.caller == pointer)

      for ((key @ (_, app), (gen, origGen, fis)) <- appInfos.toSeq if fis.nonEmpty && app.caller == pointer) {
        appInfos += key -> (gen, origGen, Set(TemplateAppInfo(template, trueT, app.args)))
      }

      true
    case None =>
      false
  }

  def instantiateLambda(template: LambdaTemplate): (Encoded, Clauses) = {
    byType(template.tpe).get(template.structure).map {
      t => (t.ids._2, Seq.empty)
    }.orElse {
      byType(template.tpe).collectFirst {
        case (s, t) if s subsumes template.structure => (t.ids._2, Seq.empty)
      }
    }.getOrElse {
      val idT = encodeSymbol(template.ids._1)
      val newTemplate = template.concretize(idT)

      val orderingClauses = newTemplate.structure.locals.flatMap {
        case (v, dep) => registerClosure(newTemplate.start, idT -> newTemplate.tpe, dep -> v.tpe)
      }

      val extClauses = for ((oldB, freeF) <- freeBlockers(newTemplate.tpe).toList if canEqual(freeF, idT)) yield {
        val nextB  = encodeSymbol(Variable.fresh("b_or", BooleanType, true))
        val ext = mkOr(mkAnd(newTemplate.start, mkEquals(idT, freeF)), nextB)
        freeBlockers += newTemplate.tpe -> (freeBlockers(newTemplate.tpe) - (oldB -> freeF) + (nextB -> freeF))
        mkEquals(oldB, ext)
      }

      // make sure we introduce sound equality constraints between closures that take no arguments
      val arglessEqClauses = if (newTemplate.tpe.from.nonEmpty || !isPureTemplate(newTemplate)) {
        Seq.empty[Encoded]
      } else {
        for ((b,f) <- freeFunctions(newTemplate.tpe) if canEqual(idT, f)) yield {
          val (tmplApp, fApp) = (mkApp(idT, newTemplate.tpe, Seq.empty), mkApp(f, newTemplate.tpe, Seq.empty))
          mkImplies(mkAnd(b, newTemplate.start, mkEquals(tmplApp, fApp)), mkEquals(idT, f))
        }
      }

      // make sure we have sound equality between the new lambda and previously defined ones
      val clauses = newTemplate.structure.instantiation ++
        equalityClauses(newTemplate) ++
        orderingClauses ++
        extClauses ++
        arglessEqClauses

      byID += idT -> newTemplate
      byType += newTemplate.tpe -> (byType(newTemplate.tpe) + (newTemplate.structure -> newTemplate))

      val gen = nextGeneration(currentGeneration)
      for (app @ (_, App(caller, _, args, _)) <- applications(newTemplate.tpe)) {
        val cond = mkAnd(newTemplate.start, mkEquals(idT, caller))
        registerAppInfo(gen, app, Left(newTemplate), cond, args)
      }

      (idT, clauses)
    }
  }

  def instantiateApp(blocker: Encoded, app: App): Clauses = {
    val App(caller, tpe @ FirstOrderFunctionType(from, to), args, encoded) = app

    val key = blocker -> app
    var clauses: Clauses = Seq.empty
    if (!instantiated(key)) {
      instantiated += key

      if (!appBlockers.isDefinedAt(key)) {
        val firstB = encodeSymbol(Variable.fresh("b_lambda", BooleanType, true))
        registerAppBlocker(key, firstB)
        clauses :+= mkImplies(mkNot(firstB), mkNot(blocker))
      }

      if (byID contains caller) {
        /* We register this app at the CURRENT generation to increase the performance
         * of fold-style higher-order functions (the first-class function will be
         * dispatched immediately after the fold-style function unrolling). */
        registerAppInfo(currentGeneration, key, Left(byID(caller)), trueT, args)
      } else {
        lazy val gen = nextGeneration(currentGeneration)
        for (template <- byType(tpe).values.toList if canEqual(caller, template.ids._2)) {
          val cond = mkAnd(template.start, mkEquals(template.ids._2, caller))
          registerAppInfo(gen, key, Left(template), cond, args)
        }

        for ((b,f) <- freeFunctions(tpe) if canEqual(caller, f)) {
          if (f == caller) {
            // We unroll this app immediately to increase performance for model finding with quantifiers
            val (lastB, nextB) = nextAppBlocker(key)
            clauses :+= mkEquals(lastB, mkOr(b, nextB))
          } else {
            val cond = mkAnd(b, mkEquals(f, caller))
            registerAppInfo(gen, key, Right(f), cond, args)
          }
        }

        /* Make sure that if `app` DOES NOT correspond to a concrete closure defined
         * within the program, then the ADT invariants are asserted on its return values. */
        if (DatatypeTemplate.unroll(to)) typeBlockers.get(encoded) match {
          case Some(typeBlocker) =>
            registerImplication(blocker, typeBlocker)
            clauses :+= mkImplies(blocker, typeBlocker)

          case None =>
            val typeBlocker = encodeSymbol(Variable.fresh("t", BooleanType))
            typeBlockers += encoded -> typeBlocker

            val firstB = encodeSymbol(Variable.fresh("b_free", BooleanType, true))
            val nextB  = encodeSymbol(Variable.fresh("b_or", BooleanType, true))
            freeBlockers += tpe -> (freeBlockers(tpe) + (nextB -> caller))

            val boundClauses = for (template <- byType(tpe).values if canEqual(caller, template.ids._2)) yield {
              mkAnd(template.start, mkEquals(caller, template.ids._2))
            }

            val extClause = mkEquals(firstB, mkAnd(blocker, mkNot(mkOr(boundClauses.toSeq :+ nextB : _*))))

            registerImplication(firstB, typeBlocker)
            val symClauses = registerSymbol(typeBlocker, encoded, to)

            clauses ++= symClauses :+ extClause :+ mkImplies(firstB, typeBlocker)
        }

        applications += tpe -> (applications(tpe) + key)
      }
    }

    clauses
  }

  private def equalityClauses(template: LambdaTemplate): Clauses = {
    byType(template.tpe).values.map { that =>
      val equals = mkEquals(template.ids._2, that.ids._2)
      val blocker = mkAnd(template.start, that.start)
      mkImplies(
        blocker,
        if (template.structure.body == that.structure.body) {
          val pairs = template.structure.locals zip that.structure.locals
          val filtered = pairs.filter(p => p._1 != p._2)
          if (filtered.isEmpty) {
            equals
          } else {
            val eqs = filtered.map { case ((v, e1), (_, e2)) =>
              if (!unrollEquality(v.tpe)) mkEquals(e1, e2) else {
                registerEquality(blocker, v.tpe, e1, e2)
              }
            }
            mkEquals(mkAnd(eqs : _*), equals)
          }
        } else {
          mkNot(equals)
        })
    }.toSeq
  }

  def getLambdaTemplates(tpe: FunctionType): Set[LambdaTemplate] = byType(tpe).values.toSet

  private[unrolling] object lambdasManager extends Manager {
    // Function instantiations have their own defblocker
    private[LambdaTemplates] val lambdaBlockers = new IncrementalMap[TemplateAppInfo, Encoded]()

    // Keep which function invocation is guarded by which guard,
    // also specify the generation of the blocker.
    private[LambdaTemplates] val appInfos      = new IncrementalMap[(Encoded, App), (Int, Int, Set[TemplateAppInfo])]()
    private[LambdaTemplates] val appBlockers   = new IncrementalMap[(Encoded, App), Encoded]()
    private[LambdaTemplates] val blockerToApps = new IncrementalMap[Encoded, (Encoded, App)]()

    val byID          = new IncrementalMap[Encoded, LambdaTemplate]
    val byType        = new IncrementalMap[FunctionType, Map[TemplateStructure, LambdaTemplate]].withDefaultValue(Map.empty)
    val applications  = new IncrementalMap[FunctionType, Set[(Encoded, App)]].withDefaultValue(Set.empty)
    val freeBlockers  = new IncrementalMap[FunctionType, Set[(Encoded, Encoded)]].withDefaultValue(Set.empty)
    val freeFunctions = new IncrementalMap[FunctionType, Set[(Encoded, Encoded)]].withDefaultValue(Set.empty)

    val instantiated = new IncrementalSet[(Encoded, App)]

    private[LambdaTemplates] val typeBlockers = new IncrementalMap[Encoded, Encoded]()

    val incrementals: Seq[IncrementalState] = Seq(
      lambdaBlockers, appInfos, appBlockers, blockerToApps,
      byID, byType, applications, freeBlockers, freeFunctions,
      instantiated, typeBlockers)

    def unrollGeneration: Option[Int] =
      if (appInfos.isEmpty) None
      else Some(appInfos.values.map(_._1).min)

    private def assumptions: Seq[Encoded] = freeBlockers.toSeq.flatMap(_._2.map(p => mkNot(p._1)))
    def satisfactionAssumptions = appBlockers.map(p => mkNot(p._2)).toSeq ++ assumptions
    def refutationAssumptions = assumptions

    def promoteBlocker(b: Encoded): Boolean = {
      if (blockerToApps contains b) {
        val app = blockerToApps(b)
        val (_, origGen, infos) = appInfos(app)
        appInfos += app -> (currentGeneration, origGen, infos)
        true
      } else {
        false
      }
    }

    def unroll: Clauses = if (appInfos.isEmpty) Seq.empty else {
      val newClauses = new scala.collection.mutable.ListBuffer[Encoded]

      val apps = appInfos.toList.filter(_._2._1 <= currentGeneration).map(_._1)
      val thisAppInfos = apps.map(app => app -> {
        val (gen, _, infos) = appInfos(app)
        (gen, infos)
      })

      val remainingApps = MutableSet.empty ++ apps

      blockerToApps --= apps.map(appBlockers)
      appInfos --= apps

      val newBlockers = (for ((app, (_, infos)) <- thisAppInfos if infos.nonEmpty) yield {
        app -> nextAppBlocker(app)
      }).toMap

      for ((app @ (b, _), (gen, infos)) <- thisAppInfos if infos.nonEmpty && !abort) {
        val (lastB, nextB) = newBlockers(app)
        if (pause) {
          newClauses += mkEquals(lastB, nextB)
        } else {
          remainingApps -= app

          val extension = mkOr((infos.map(info => info.template match {
            case Left(template) => mkAnd(template.start, info.equals)
            case Right(_) => info.equals
          }).toSeq :+ nextB) : _*)

          val clause = mkEquals(lastB, extension)
          ctx.reporter.debug(" -> extending lambda blocker: " + clause)
          newClauses += clause

          for (info @ TemplateAppInfo(tmpl, equals, args) <- infos if !abort; template <- tmpl.left) {
            val newCls = new scala.collection.mutable.ListBuffer[Encoded]

            val lambdaBlocker = lambdaBlockers.get(info) match {
              case Some(lambdaBlocker) => lambdaBlocker

              case None =>
                val lambdaBlocker = encodeSymbol(Variable.fresh("d", BooleanType, true))
                lambdaBlockers += info -> lambdaBlocker

                val instClauses: Clauses = template.instantiate(lambdaBlocker, args)

                newCls ++= instClauses
                lambdaBlocker
            }

            val enabler = if (equals == trueT) b else mkAnd(equals, b)
            registerImplication(b, lambdaBlocker)
            newCls += mkImplies(enabler, lambdaBlocker)

            ctx.reporter.debug("Unrolling behind "+info+" ("+newCls.size+")")
            for (cl <- newCls) {
              ctx.reporter.debug("  . "+cl)
            }

            newClauses ++= newCls
          }
        }
      }

      val remainingInfos = thisAppInfos.filter { case (app, _) => remainingApps(app) }
      for ((app, (gen, infos)) <- thisAppInfos if remainingApps(app)) appInfos.get(app) match {
        case Some((newGen, origGen, newInfos)) =>
          appInfos += app -> (gen min newGen, origGen, infos ++ newInfos)

        case None =>
          appInfos += app -> (gen, gen, infos)
          blockerToApps += appBlockers(app) -> app
      }

      ctx.reporter.debug(s"   - ${newClauses.size} new clauses")

      newClauses
    }
  }
}
