/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._
import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

trait LambdaTemplates { self: Templates =>
  import context._
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
      val idArgs: Seq[Variable] = lambda.args.map(_.toVariable)
      val trArgs: Seq[Encoded] = idArgs.map(v => substMap.getOrElse(v, encodeSymbol(v)))

      val (realLambda, structure, depSubst) = mkExprStructure(pathVar._1, lambda, substMap)
      val depClosures = exprOps.variablesOf(lambda).toSeq.sortBy(_.id.uniqueName).map(v => v -> substMap(v))

      val tpe = lambda.getType.asInstanceOf[FunctionType]
      val lid = Variable.fresh("lambda", tpe, true)
      val app = Application(lid, idArgs)

      val clauseSubst: Map[Variable, Encoded] = depSubst ++ (idArgs zip trArgs)
      val tmplClauses = {
        val (p, cls) = mkExprClauses(pathVar._1, application(realLambda, idArgs), clauseSubst)
        cls + (pathVar._1 -> Equals(app, p))
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
    val closures: Seq[(Variable, Encoded)],
    val lambda: Lambda,
    private[unrolling] val stringRepr: () => String,
    private val isConcrete: Boolean) extends Template {

    val tpe = ids._1.getType.asInstanceOf[FunctionType]

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): LambdaTemplate = new LambdaTemplate(
      ids._1 -> substituter(ids._2),
      contents.substitute(substituter, msubst),
      structure.substitute(substituter, msubst),
      closures.map(p => p._1 -> substituter(p._2)),
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

  def registerFunction(b: Encoded, r: Encoded, tpe: FunctionType, f: Encoded): Clauses = {
    reporter.debug(s"-> registering free function $b ==> $f: $tpe")
    freeFunctions += tpe -> (freeFunctions(tpe) + (b -> f))

    var clauses: Clauses = Seq.empty
    lazy val gen = nextGeneration(currentGeneration)
    for (app @ (_, App(caller, _, args, _)) <- applications(tpe)) {
      if (f == caller) {
        // We unroll this app immediately to increase performance for model finding
        val (lastB, nextB) = nextAppBlocker(app)
        clauses :+= mkEquals(lastB, mkOr(b, nextB))
      } else {
        val cond = mkAnd(b, mkEquals(f, caller))
        registerAppInfo(gen, app, Right(f), cond, args)
      }
    }

    val nextB  = encodeSymbol(Variable.fresh("b_and", BooleanType(), true))
    freeBlockers += tpe -> (freeBlockers(tpe) + (nextB -> f))

    clauses :+= mkImplies(b, mkEquals(r, mkAnd((for {
      app @ (_, App(caller, _, _, encoded)) <- applications(tpe)
      (b, res) <- typeBlockers.get(encoded)
    } yield {
      mkImplies(mkAnd(b, mkEquals(caller, f)), res)
    }).toSeq :+ nextB : _*)))

    if (tpe.from.isEmpty) clauses ++= (for {
      template <- byType(tpe).values.toList
      if canBeEqual(template.ids._2, f) && isPureTemplate(template)
    } yield {
      val (tmplApp, fApp) = (mkApp(template.ids._2, tpe, Seq.empty), mkApp(f, tpe, Seq.empty))
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
    val nextB = encodeSymbol(Variable.fresh("b_lambda", BooleanType(), true))
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

      val orderingClauses = newTemplate.closures.flatMap {
        case (v, dep) => registerClosure(newTemplate.start, idT -> newTemplate.tpe, dep -> v.tpe)
      }

      // make sure we introduce sound equality constraints between closures that take no arguments
      val arglessEqClauses: Clauses = if (newTemplate.tpe.from.nonEmpty || !isPureTemplate(newTemplate)) {
        Seq.empty
      } else {
        for ((b,f) <- freeFunctions(newTemplate.tpe).toSeq if canBeEqual(idT, f)) yield {
          val (tmplApp, fApp) = (mkApp(idT, newTemplate.tpe, Seq.empty), mkApp(f, newTemplate.tpe, Seq.empty))
          mkImplies(mkAnd(b, newTemplate.start, mkEquals(tmplApp, fApp)), mkEquals(idT, f))
        }
      }

      // make sure we have sound equality between the new lambda and previously defined ones
      val clauses = newTemplate.structure.instantiation ++
        equalityClauses(newTemplate) ++
        orderingClauses ++
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
    val App(caller, tpe @ FunctionType(from, to), args, encoded) = app

    val key = blocker -> app
    var clauses: Clauses = Seq.empty
    if (!instantiated(key)) {
      instantiated += key

      if (!appBlockers.isDefinedAt(key)) {
        val firstB = encodeSymbol(Variable.fresh("b_lambda", BooleanType(), true))
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
        for (template <- byType(tpe).values.toList if canBeEqual(caller, template.ids._2)) {
          val cond = mkAnd(template.start, mkEquals(template.ids._2, caller))
          registerAppInfo(gen, key, Left(template), cond, args)
        }

        for ((b,f) <- freeFunctions(tpe) if canBeEqual(caller, f)) {
          if (f == caller) {
            // We unroll this app immediately to increase performance for model finding
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
          case Some((typeBlocker, _)) =>
            registerImplication(blocker, typeBlocker)
            clauses :+= mkImplies(blocker, typeBlocker)

          case None =>
            val typeBlocker = encodeSymbol(Variable.fresh("t", BooleanType()))
            val (symResult, symClauses) = registerSymbol(typeBlocker, encoded, to)
            typeBlockers += encoded -> ((typeBlocker, symResult))

            val freeAppClauses = for (old @ (oldB,f) <- freeBlockers(tpe).toList if canBeEqual(caller, f)) yield {
              val nextB  = encodeSymbol(Variable.fresh("b_and", BooleanType(), true))
              val ext = mkAnd(mkImplies(mkAnd(typeBlocker, mkEquals(caller, f)), symResult), nextB)
              freeBlockers += tpe -> (freeBlockers(tpe) - (old) + (nextB -> f))
              mkEquals(oldB, ext)
            }

            clauses ++= symClauses ++ freeAppClauses :+ mkImplies(blocker, typeBlocker)
        }

        applications += tpe -> (applications(tpe) + key)
      }
    }

    clauses
  }

  private def equalityClauses(template: LambdaTemplate): Clauses = {
    byType(template.tpe).values.flatMap { that =>
      val equals = mkEquals(template.ids._2, that.ids._2)
      val (blocker, blockerClauses) = encodeBlockers(Set(template.start, that.start))
      blockerClauses :+ mkImplies(
        blocker,
        if (template.structure.body == that.structure.body) {
          val pairs = template.structure.locals zip that.structure.locals
          val filtered = pairs.filter(p => p._1 != p._2)
          if (filtered.isEmpty) {
            equals
          } else {
            val eqs = filtered.map { case ((v, e1), (_, e2)) =>
              mkEqualities(blocker, v.tpe, e1, e2, register = false)
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

    /** This map holds the mapping from lambda identifiers to the corresponding template.
      * The map is populated during lambda instantiation in [[instantiateLambda]].
      */
    val byID          = new IncrementalMap[Encoded, LambdaTemplate]

    /** This is a mapping from function types to all known lambda instantiations of that type
      * keyed by their structure (for faster lookup).
      * This map is also populated during lambda instantiation in [[instantiateLambda]] and
      * is used to relate different lambdas that share a same type (eg. for equality).
      * The templates contained within `byType` and `byID` are the same.
      */
    val byType        = new IncrementalMap[FunctionType, Map[TemplateStructure, LambdaTemplate]].withDefaultValue(Map.empty)

    /** This is a mapping from function types to all known function applications of functions
      * of that type. The aim is to dispatch these applications to members of the `byType` map
      * while carefuly instrumenting the resulting formulas so that satisfiability has to wait
      * for the correct lambda to be found.
      */
    val applications  = new IncrementalMap[FunctionType, Set[(Encoded, App)]].withDefaultValue(Set.empty)

    /** This mapping is used to keep track of an instrumentation that makes sure that quantifying
      * over empty function types won't lead to invalid proofs (see [[DatatypeTemplates.DatatypeTemplate]]).
      * The instrumentation basically associates some boolean variable with each free function
      * symbol within the quantified variable and if the function turns out to be empty (has an
      * empty return type) AND is applied somewhere, then the variable will be set to false.
      */
    val freeBlockers  = new IncrementalMap[FunctionType, Set[(Encoded, Encoded)]].withDefaultValue(Set.empty)

    /** This mapping is used for
      * 1. to cache datatype unfoldings of free function application results, and
      * 2. to keep track of the boolean variable that must be set to false as described above in
      *    [[freeBlockers]].
      * The map is keyed by the encoding field of an `App` (which is unique for each `App`).
      */
    val typeBlockers  = new IncrementalMap[Encoded, (Encoded, Encoded)]()

    /** This mapping maintains the set of all known free functions within the input formula
      * and is used to ensure sound models for functions that take no arguments.
      */
    val freeFunctions = new IncrementalMap[FunctionType, Set[(Encoded, Encoded)]].withDefaultValue(Set.empty)

    val instantiated = new IncrementalSet[(Encoded, App)]

    val incrementals: Seq[IncrementalState] = Seq(
      lambdaBlockers, appInfos, appBlockers, blockerToApps,
      byID, byType, applications, freeBlockers, freeFunctions,
      instantiated, typeBlockers)

    def unrollGeneration: Option[Int] =
      if (appInfos.isEmpty) None
      else Some(appInfos.values.map(_._1).min)

    private def assumptions: Seq[Encoded] = freeBlockers.toSeq.flatMap(_._2.map(_._1))
    def satisfactionAssumptions = appBlockers.map(p => mkNot(p._2)).toSeq ++ assumptions
    def refutationAssumptions = assumptions

    def promoteBlocker(b: Encoded): Boolean = {
      if (blockerToApps contains b) {
        val app = blockerToApps(b)
        if (appInfos contains app) {
          val (_, origGen, infos) = appInfos(app)
          appInfos += app -> (currentGeneration, origGen, infos)
          true
        } else {
          false
        }
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
          reporter.debug(" -> extending lambda blocker: " + clause)
          newClauses += clause

          for (info @ TemplateAppInfo(tmpl, equals, args) <- infos if !abort; template <- tmpl.left) {
            val newCls = new scala.collection.mutable.ListBuffer[Encoded]

            val lambdaBlocker = lambdaBlockers.get(info) match {
              case Some(lambdaBlocker) => lambdaBlocker

              case None =>
                val lambdaBlocker = encodeSymbol(Variable.fresh("d", BooleanType(), true))
                lambdaBlockers += info -> lambdaBlocker

                val instClauses: Clauses = template.instantiate(lambdaBlocker, args)

                newCls ++= instClauses
                lambdaBlocker
            }

            val enabler = if (equals == trueT) b else mkAnd(equals, b)
            registerImplication(b, lambdaBlocker)
            newCls += mkImplies(enabler, lambdaBlocker)

            reporter.debug("Unrolling behind "+info+" ("+newCls.size+")")
            for (cl <- newCls) {
              reporter.debug("  . "+cl)
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

      reporter.debug(s"   - ${newClauses.size} new clauses")

      newClauses
    }
  }
}
