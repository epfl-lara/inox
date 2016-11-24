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
      ids: (Variable, Encoded),
      pathVar: (Variable, Encoded),
      arguments: Seq[(Variable, Encoded)],
      condVars: Map[Variable, Encoded],
      exprVars: Map[Variable, Encoded],
      condTree: Map[Variable, Set[Variable]],
      guardedExprs: Map[Variable, Seq[Expr]],
      equations: Seq[Expr],
      lambdas: Seq[LambdaTemplate],
      quantifications: Seq[QuantificationTemplate],
      structure: TemplateStructure,
      closures: Set[Encoded],
      baseSubstMap: Map[Variable, Encoded],
      lambda: Lambda
    ) : LambdaTemplate = {

      val id = ids._2
      val tpe = ids._1.getType.asInstanceOf[FunctionType]
      val (contents, str) = Template.contents(
        pathVar, arguments, condVars, exprVars, condTree, guardedExprs, equations,
        lambdas, quantifications, substMap = baseSubstMap + ids, optApp = Some(id -> tpe))

      val lambdaString : () => String = () => {
        "Template for lambda " + ids._1 + ": " + lambda + " is :\n" + str()
      }

      new LambdaTemplate(ids, contents, structure, closures, lambda, lambdaString, false)
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

    /** This must be called right before returning the clauses in [[structure.instantiation]]! */
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
  def mkApp(caller: Encoded, tpe: FunctionType, args: Seq[Encoded], rec: Boolean = false): Encoded = {
    val (vT, asT, app) = appCache.getOrElseUpdate(tpe, {
      val v = Variable(FreshIdentifier("f"), tpe)
      val as = tpe.from.map(tp => Variable(FreshIdentifier("x", true), tp))
      val (vT, asT) = (encodeSymbol(v), as.map(encodeSymbol))
      (vT, asT, mkEncoder(Map(v -> vT) ++ (as zip asT))(Application(v, as)))
    })

    val (currArgs, restArgs) = args.splitAt(tpe.from.size)
    val firstApp = mkSubstituter(Map(vT -> caller) ++ (asT zip currArgs))(app)

    tpe.to match {
      case ft: FunctionType if rec => mkApp(firstApp, ft, restArgs)
      case _ => firstApp
    }
  }

  def mkFlatApp(caller: Encoded, tpe: FunctionType, args: Seq[Encoded]): Encoded = tpe.to match {
    case ft: FunctionType => mkFlatApp(mkApp(caller, tpe, args.take(tpe.from.size)), ft, args.drop(tpe.from.size))
    case _ => mkApp(caller, tpe, args)
  }

  def registerFunction(b: Encoded, tpe: FunctionType, f: Encoded): Clauses = {
    val ft = bestRealType(tpe).asInstanceOf[FunctionType]
    freeFunctions += ft -> (freeFunctions(ft) + (b -> f))

    lazy val gen = nextGeneration(currentGeneration)
    for (app @ (_, App(caller, _, args, _)) <- applications(ft)) {
      val cond = mkAnd(b, mkEquals(f, caller))
      registerAppBlocker(gen, app, Right(f), cond, args)
    }

    if (ft.from.nonEmpty) Seq.empty else {
      for (template <- byType(ft).values.toSeq if canEqual(template.ids._2, f)) yield {
        val (tmplApp, fApp) = (mkApp(template.ids._2, ft, Seq.empty), mkApp(f, ft, Seq.empty))
        mkImplies(mkAnd(b, template.start, mkEquals(tmplApp, fApp)), mkEquals(template.ids._2, f))
      }
    }
  }

  private def registerAppBlocker(gen: Int, key: (Encoded, App), template: Either[LambdaTemplate, Encoded], equals: Encoded, args: Seq[Arg]): Unit = {
    val info = TemplateAppInfo(template, equals, args)
    appInfos.get(key) match {
      case Some((exGen, origGen, b, notB, exInfo)) =>
        val minGen = gen min exGen
        appInfos += key -> (minGen, origGen, b, notB, exInfo + info)

      case None =>
        val b = appBlockers(key)
        val notB = mkNot(b)
        appInfos += key -> (gen, gen, b, notB, Set(info))
        blockerToApps += b -> key
    }
  }

  def registerLambda(pointer: Encoded, target: Encoded): Boolean = byID.get(target) match {
    case Some(template) =>
      byID += pointer -> template
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

      val extClauses = for ((oldB, freeF) <- freeBlockers(newTemplate.tpe) if canEqual(freeF, idT)) yield {
        val nextB  = encodeSymbol(Variable(FreshIdentifier("b_or", true), BooleanType))
        val ext = mkOr(mkAnd(newTemplate.start, mkEquals(idT, freeF)), nextB)
        mkEquals(oldB, ext)
      }

      val arglessEqClauses = if (newTemplate.tpe.from.nonEmpty) Seq.empty[Encoded] else {
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
        registerAppBlocker(gen, app, Left(newTemplate), cond, args)
      }

      (idT, clauses)
    }
  }

  def instantiateApp(blocker: Encoded, app: App): Clauses = {
    val App(caller, tpe @ FirstOrderFunctionType(from, to), args, encoded) = app

    val key = blocker -> app
    if (instantiated(key)) Seq.empty else {
      instantiated += key

      val freshAppClause = if (appBlockers.isDefinedAt(key)) None else {
        val firstB = encodeSymbol(Variable(FreshIdentifier("b_lambda", true), BooleanType))
        val clause = mkImplies(mkNot(firstB), mkNot(blocker))

        // blockerToApps will be updated by the following registerAppBlocker call
        appBlockers += key -> firstB
        Some(clause)
      }

      val typeClauses: Clauses = if (byID contains caller) {
        /* We register this app at the CURRENT generation to increase the performance
         * of fold-style higher-order functions (the first-class function will be
         * dispatched immediately after the fold-style function unrolling). */
        registerAppBlocker(currentGeneration, key, Left(byID(caller)), trueT, args)

        // don't unroll type as lambda is defined within the program
        Seq.empty
      } else {
        lazy val gen = nextGeneration(currentGeneration)
        for (template <- byType(tpe).values if canEqual(caller, template.ids._2)) {
          val cond = mkAnd(template.start, mkEquals(template.ids._2, caller))
          registerAppBlocker(gen, key, Left(template), cond, args)
        }

        for ((b,f) <- freeFunctions(tpe) if canEqual(caller, f)) {
          val cond = mkAnd(b, mkEquals(f, caller))
          registerAppBlocker(gen, key, Right(f), cond, args)
        }

        /* Make sure that if `app` DOES NOT correspond to a concrete closure defined
         * within the program, then the ADT invariants are asserted on its return values. */
        val tpeClauses: Clauses = if (!DatatypeTemplate.unroll(to)) {
          Seq.empty
        } else typeBlockers.get(encoded) match {
          case Some(typeBlocker) =>
            registerImplication(blocker, typeBlocker)
            Seq(mkImplies(blocker, typeBlocker))

          case None =>
            val typeBlocker = encodeSymbol(Variable(FreshIdentifier("t"), BooleanType))
            typeBlockers += encoded -> typeBlocker

            val firstB = encodeSymbol(Variable(FreshIdentifier("b_free", true), BooleanType))
            typeEnablers += firstB

            val nextB  = encodeSymbol(Variable(FreshIdentifier("b_or", true), BooleanType))
            freeBlockers += tpe -> (freeBlockers(tpe) + (nextB -> caller))

            val boundClauses = for (template <- byType(tpe).values if canEqual(caller, template.ids._2)) yield {
              mkAnd(template.start, mkEquals(caller, template.ids._2))
            }

            val extClause = mkEquals(firstB, mkAnd(blocker, mkNot(mkOr(boundClauses.toSeq :+ nextB : _*))))

            registerImplication(firstB, typeBlocker)
            val symClauses = registerSymbol(typeBlocker, encoded, to)

            symClauses :+ extClause :+ mkImplies(firstB, typeBlocker)
        }

        applications += tpe -> (applications(tpe) + key)

        tpeClauses
      }

      typeClauses ++ freshAppClause
    }
  }

  private def equalityClauses(template: LambdaTemplate): Clauses = {
    byType(template.tpe).values.map { that =>
      val equals = mkEquals(template.ids._2, that.ids._2)
      mkImplies(
        mkAnd(template.start, that.start),
        if (template.structure.body == that.structure.body) {
          val pairs = template.structure.locals zip that.structure.locals
          val filtered = pairs.filter(p => p._1 != p._2)
          if (filtered.isEmpty) {
            equals
          } else {
            val eqs = filtered.map(p => mkEquals(p._1._2, p._2._2))
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
    val lambdaBlockers = new IncrementalMap[TemplateAppInfo, Encoded]()

    // Keep which function invocation is guarded by which guard,
    // also specify the generation of the blocker.
    val appInfos      = new IncrementalMap[(Encoded, App), (Int, Int, Encoded, Encoded, Set[TemplateAppInfo])]()
    val appBlockers   = new IncrementalMap[(Encoded, App), Encoded]()
    val blockerToApps = new IncrementalMap[Encoded, (Encoded, App)]()

    val byID          = new IncrementalMap[Encoded, LambdaTemplate]
    val byType        = new IncrementalMap[FunctionType, Map[TemplateStructure, LambdaTemplate]].withDefaultValue(Map.empty)
    val applications  = new IncrementalMap[FunctionType, Set[(Encoded, App)]].withDefaultValue(Set.empty)
    val freeBlockers  = new IncrementalMap[FunctionType, Set[(Encoded, Encoded)]].withDefaultValue(Set.empty)
    val freeFunctions = new IncrementalMap[FunctionType, Set[(Encoded, Encoded)]].withDefaultValue(Set.empty)

    val instantiated = new IncrementalSet[(Encoded, App)]

    val typeBlockers = new IncrementalMap[Encoded, Encoded]()
    val typeEnablers: MutableSet[Encoded] = MutableSet.empty

    override val incrementals: Seq[IncrementalState] = Seq(
      lambdaBlockers, appInfos, appBlockers, blockerToApps,
      byID, byType, applications, freeBlockers, freeFunctions,
      instantiated, typeBlockers)

    def unrollGeneration: Option[Int] =
      if (appInfos.isEmpty) None
      else Some(appInfos.values.map(_._1).min)

    private def assumptions: Seq[Encoded] = freeBlockers.toSeq.flatMap(_._2.map(p => mkNot(p._1)))
    def satisfactionAssumptions = appInfos.map(_._2._4).toSeq ++ assumptions
    def refutationAssumptions = assumptions

    def promoteBlocker(b: Encoded): Boolean = {
      if (blockerToApps contains b) {
        val app = blockerToApps(b)
        val (_, origGen, _, notB, infos) = appInfos(app)
        appInfos += app -> (currentGeneration, origGen, b, notB, infos)
        true
      } else {
        false
      }
    }

    def unroll: Clauses = if (appInfos.isEmpty) Seq.empty else {
      val newClauses = new scala.collection.mutable.ListBuffer[Encoded]

      val blockers = appInfos.values.filter(_._1 <= currentGeneration).toSeq.map(_._3)
      val apps = blockers.flatMap(blocker => blockerToApps.get(blocker))
      val thisAppInfos = apps.map(app => app -> {
        val (gen, _, _, _, infos) = appInfos(app)
        (gen, infos)
      })

      val remainingApps = MutableSet.empty ++ apps

      blockerToApps --= blockers
      appInfos --= apps

      val newBlockers = (for ((app, (_, infos)) <- thisAppInfos if infos.nonEmpty) yield {
        val nextB = encodeSymbol(Variable(FreshIdentifier("b_lambda", true), BooleanType))
        val lastB = appBlockers(app)

        blockerToApps += nextB -> app
        appBlockers += app -> nextB

        app -> ((lastB, nextB))
      }).toMap

      for ((app @ (b, _), (gen, infos)) <- thisAppInfos if infos.nonEmpty) {
        val (lastB, nextB) = newBlockers(app)
        if (interrupted) {
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

          for (info @ TemplateAppInfo(tmpl, equals, args) <- infos; template <- tmpl.left) {
            val newCls = new scala.collection.mutable.ListBuffer[Encoded]

            val lambdaBlocker = lambdaBlockers.get(info) match {
              case Some(lambdaBlocker) => lambdaBlocker

              case None =>
                val lambdaBlocker = encodeSymbol(Variable(FreshIdentifier("d", true), BooleanType))
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
        case Some((newGen, origGen, b, notB, newInfos)) =>
          appInfos += app -> (gen min newGen, origGen, b, notB, infos ++ newInfos)

        case None =>
          val b = appBlockers(app)
          val notB = mkNot(b)
          appInfos += app -> (gen, gen, b, notB, infos)
      }

      ctx.reporter.debug(s"   - ${newClauses.size} new clauses")

      newClauses
    }
  }
}
