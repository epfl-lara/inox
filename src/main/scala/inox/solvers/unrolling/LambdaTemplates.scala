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

  /** Represents a POTENTIAL application of a first-class function in the unfolding procedure
    *
    * The [[equals]] condition guards the application for equality of the concrete caller with
    * the provided template in order to perform dynamic dispatch.
    */
  case class TemplateAppInfo(template: Either[LambdaTemplate, Encoded], equals: Encoded, args: Seq[Arg]) {
    override def toString = {
      val caller = template match {
        case Left(tmpl) => tmpl.ids._2.asString
        case Right(c) => c.asString
      }

      caller + "|" + equals.asString + args.map {
        case Right(m) => m.toString
        case Left(v) => v.asString
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
      lambdas: Seq[LambdaTemplate],
      quantifications: Seq[QuantificationTemplate],
      structure: LambdaStructure,
      baseSubstMap: Map[Variable, Encoded],
      lambda: Lambda
    ) : LambdaTemplate = {

      val id = ids._2
      val tpe = ids._1.getType.asInstanceOf[FunctionType]
      val (clauses, blockers, applications, matchers, templateString) =
        Template.encode(pathVar, arguments, condVars, exprVars, guardedExprs, lambdas, quantifications,
          substMap = baseSubstMap + ids, optApp = Some(id -> tpe))

      val lambdaString : () => String = () => {
        "Template for lambda " + ids._1 + ": " + lambda + " is :\n" + templateString()
      }

      new LambdaTemplate(
        ids,
        pathVar,
        arguments,
        condVars,
        exprVars,
        condTree,
        clauses,
        blockers,
        applications,
        matchers,
        lambdas,
        quantifications,
        structure,
        lambda,
        lambdaString
      )
    }
  }

  /** Semi-template used for hardcore function equality
    *
    * Function equality, while unhandled in general, can be very useful for certain
    * proofs that refer specifically to first-class functions. In order to support
    * such proofs, flexible notions of equality on first-class functions are
    * necessary. These are provided by [[LambdaStructure]] which, much like a
    * [[Template]], will generate clauses that represent equality between two
    * functions.
    *
    * To support complex cases of equality where closed portions of the first-class
    * function rely on complex program features (function calls, introducing lambdas,
    * foralls, etc.), we use a structure that resembles a [[Template]] that is
    * instantiated when function equality is of interest.
    *
    * Note that lambda creation now introduces clauses to determine equality between
    * closed portions (that are independent of the lambda arguments).
    */
  class LambdaStructure private[unrolling] (
    /** The normalized lambda that is shared between all "equal" first-class functions.
      * First-class function equality is conditionned on `lambda` equality.
      *
      * @see [[dependencies]] for the other component of equality between first-class functions
      */
    val lambda: Lambda,

    /** The closed expressions (independent of the arguments to [[lambda]] contained in
      * the first-class function. Equality is conditioned on equality of `dependencies`
      * (inside the solver).
      *
      * @see [[lambda]] for the other component of equality between first-class functions
      */
    val dependencies: Seq[Encoded],
    val pathVar: (Variable, Encoded),

    /** The set of closed variables that exist in the associated lambda.
      *
      * This set is necessary to determine whether other closures have been
      * captured by this particular closure when deciding the order of
      * lambda instantiations in [[Template.substitution]].
      */
    val closures: Seq[Encoded],
    val condVars: Map[Variable, Encoded],
    val exprVars: Map[Variable, Encoded],
    val condTree: Map[Variable, Set[Variable]],
    val clauses: Clauses,
    val blockers: Calls,
    val applications: Apps,
    val matchers: Matchers,
    val lambdas: Seq[LambdaTemplate],
    val quantifications: Seq[QuantificationTemplate]) {

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]) = new LambdaStructure(
      lambda,
      dependencies.map(substituter),
      pathVar._1 -> substituter(pathVar._2),
      closures.map(substituter), condVars, exprVars, condTree,
      clauses.map(substituter),
      blockers.map { case (b, fis) => substituter(b) -> fis.map(_.substitute(substituter, msubst)) },
      applications.map { case (b, fas) => substituter(b) -> fas.map(_.substitute(substituter, msubst)) },
      matchers.map { case (b, ms) => substituter(b) -> ms.map(_.substitute(substituter, msubst)) },
      lambdas.map(_.substitute(substituter, msubst)),
      quantifications.map(_.substitute(substituter, msubst)))

    /** The [[key]] value (tuple of [[lambda]] and [[dependencies]]) is used
      * to determine syntactic equality between lambdas. If the keys of two
      * closures are equal, then they must necessarily be equal in every model.
      *
      * The [[instantiation]] consists of the clause set instantiation (in the
      * sense of [[Template.instantiate]] that is required for [[dependencies]]
      * to make sense in the solver (introduces blockers, quantifications, other
      * lambdas, etc.) Since [[dependencies]] CHANGE during instantiation and
      * [[key]] makes no sense without the associated instantiation, the implicit
      * contract here is that whenever a new key appears during unfolding, its
      * associated instantiation MUST be added to the set of instantiations
      * managed by the solver. However, if an identical pre-existing key has
      * already been found, then the associated instantiations must already appear
      * in those handled by the solver.
      */
    lazy val (key, instantiation) = {
      val (substMap, substInst) = Template.substitution(
        condVars, exprVars, condTree, lambdas, quantifications, Map.empty, pathVar._1, pathVar._2)
      val tmplInst = Template.instantiate(clauses, blockers, applications, matchers, substMap)

      val substituter = mkSubstituter(substMap.mapValues(_.encoded))
      val key = (lambda, dependencies.map(substituter))
      val instantiation = substInst ++ tmplInst
      (key, instantiation)
    }

    override def equals(that: Any): Boolean = that match {
      case (struct: LambdaStructure) => key == struct.key
      case _ => false
    }

    override def hashCode: Int = key.hashCode
  }

  class LambdaTemplate private (
    val ids: (Variable, Encoded),
    val pathVar: (Variable, Encoded),
    val arguments: Seq[(Variable, Encoded)],
    val condVars: Map[Variable, Encoded],
    val exprVars: Map[Variable, Encoded],
    val condTree: Map[Variable, Set[Variable]],
    val clauses: Clauses,
    val blockers: Calls,
    val applications: Apps,
    val matchers: Matchers,
    val lambdas: Seq[LambdaTemplate],
    val quantifications: Seq[QuantificationTemplate],
    val structure: LambdaStructure,
    val lambda: Lambda,
    stringRepr: () => String) extends Template {

    val args = arguments.map(_._2)
    val tpe = bestRealType(ids._1.getType).asInstanceOf[FunctionType]

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): LambdaTemplate = new LambdaTemplate(
      ids._1 -> substituter(ids._2),
      pathVar._1 -> substituter(pathVar._2),
      arguments, condVars, exprVars, condTree,
      clauses.map(substituter),
      blockers.map { case (b, fis) => substituter(b) -> fis.map(_.substitute(substituter, msubst)) },
      applications.map { case (b, apps) => substituter(b) -> apps.map(_.substitute(substituter, msubst)) },
      matchers.map { case (b, ms) => substituter(b) -> ms.map(_.substitute(substituter, msubst)) },
      lambdas.map(_.substitute(substituter, msubst)),
      quantifications.map(_.substitute(substituter, msubst)),
      structure.substitute(substituter, msubst),
      lambda, stringRepr)

    def withId(idT: Encoded): LambdaTemplate = {
      val substituter = mkSubstituter(Map(ids._2 -> idT))
      new LambdaTemplate(
        ids._1 -> idT, pathVar, arguments, condVars, exprVars, condTree,
        clauses map substituter, // make sure the body-defining clause is inlined!
        blockers, applications, matchers, lambdas, quantifications,
        structure, lambda, stringRepr
      )
    }

    private lazy val str : String = stringRepr()
    override def toString : String = str

    override def instantiate(substMap: Map[Encoded, Arg]): Clauses = {
      super.instantiate(substMap) ++ instantiateAxiom(this, substMap)
    }
  }

  def registerFunction(b: Encoded, tpe: FunctionType, f: Encoded): Clauses = {
    val ft = bestRealType(tpe).asInstanceOf[FunctionType]
    val bs = fixpoint((bs: Set[Encoded]) => bs ++ bs.flatMap(blockerParents))(Set(b))

    val (known, neqClauses) = if ((bs intersect typeEnablers).nonEmpty) {
      maybeFree += ft -> (maybeFree(ft) + (b -> f))
      (false, byType(ft).values.toSeq.map { t =>
        mkImplies(b, mkNot(mkEquals(t.ids._2, f)))
      })
    } else {
      knownFree += ft -> (knownFree(ft) + f)
      (true, byType(ft).values.toSeq.map(t => mkNot(mkEquals(t.ids._2, f))))
    }

    val extClauses = freeBlockers(tpe).map { case (oldB, freeF) =>
      val equals = mkEquals(f, freeF)
      val nextB  = encodeSymbol(Variable(FreshIdentifier("b_or", true), BooleanType))
      val extension = mkOr(if (known) equals else mkAnd(b, equals), nextB)
      mkEquals(oldB, extension)
    }

    lazy val gen = nextGeneration(currentGeneration)
    for (app @ (_, App(caller, _, args, _)) <- applications(tpe)) {
      val equals = mkAnd(b, mkEquals(f, caller))
      registerAppBlocker(gen, app, Right(f), equals, args)
    }

    neqClauses ++ extClauses
  }

  private def typeUnroller(blocker: Encoded, app: App): Clauses = typeBlockers.get(app.encoded) match {
    case Some(typeBlocker) =>
      impliesBlocker(blocker, typeBlocker)
      Seq(mkImplies(blocker, typeBlocker))

    case None =>
      val App(caller, tpe @ FirstOrderFunctionType(_, to), args, value) = app
      val typeBlocker = encodeSymbol(Variable(FreshIdentifier("t"), BooleanType))
      typeBlockers += value -> typeBlocker
      impliesBlocker(blocker, typeBlocker)

      val clauses = registerSymbol(typeBlocker, value, to)

      val (b, extClauses) = if (knownFree(tpe) contains caller) {
        (blocker, Seq.empty)
      } else {
        val firstB = encodeSymbol(Variable(FreshIdentifier("b_free", true), BooleanType))
        impliesBlocker(firstB, typeBlocker)
        typeEnablers += firstB

        val nextB  = encodeSymbol(Variable(FreshIdentifier("b_or", true), BooleanType))
        freeBlockers += tpe -> (freeBlockers(tpe) + (nextB -> caller))

        val clause = mkEquals(firstB, mkAnd(blocker, mkOr(
          knownFree(tpe).map(idT => mkEquals(caller, idT)).toSeq ++
          maybeFree(tpe).map { case (b, idT) => mkAnd(b, mkEquals(caller, idT)) } :+
          nextB : _*)))
        (firstB, Seq(clause))
      }

      clauses ++ extClauses :+ mkImplies(b, typeBlocker)
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

  def instantiateLambda(template: LambdaTemplate): (Encoded, Clauses) = {
    byType(template.tpe).get(template.structure) match {
      case Some(template) =>
        (template.ids._2, Seq.empty)

      case None =>
        val idT = encodeSymbol(template.ids._1)
        val newTemplate = template.withId(idT)

        // make sure the new lambda isn't equal to any free lambda var
        val clauses = newTemplate.structure.instantiation ++
          equalityClauses(newTemplate) ++
          knownFree(newTemplate.tpe).map(f => mkNot(mkEquals(idT, f))).toSeq ++
          maybeFree(newTemplate.tpe).map { p =>
            mkImplies(p._1, mkNot(mkEquals(idT, p._2)))
          }

        byID += idT -> newTemplate
        byType += newTemplate.tpe -> (byType(newTemplate.tpe) + (newTemplate.structure -> newTemplate))

        val gen = nextGeneration(currentGeneration)
        for (app @ (_, App(caller, _, args, _)) <- applications(newTemplate.tpe)) {
          val equals = mkEquals(idT, caller)
          registerAppBlocker(gen, app, Left(newTemplate), equals, args)
        }

        (idT, clauses)
    }
  }

  def instantiateApp(blocker: Encoded, app: App): Clauses = {
    val App(caller, tpe @ FunctionType(_, to), args, encoded) = app

    val clauses: Clauses =
      if (byID contains caller) Seq.empty
      else typeUnroller(blocker, app)

    val key = blocker -> app
    if (instantiated(key)) clauses else {
      instantiated += key

      if (knownFree(tpe) contains caller) {
        clauses
      } else if (byID contains caller) {
        // we register this app at the CURRENT generation to increase the performance
        // of fold-style higher-order functions (the first-class function will be
        // dispatched immediately after the fold-style function unrolling)
        registerAppBlocker(currentGeneration, key, Left(byID(caller)), trueT, args)
        clauses
      } else {
        val freshAppClause = if (appBlockers.isDefinedAt(key)) None else {
          val firstB = encodeSymbol(Variable(FreshIdentifier("b_lambda", true), BooleanType))
          val clause = mkImplies(mkNot(firstB), mkNot(blocker))

          appBlockers += key -> firstB
          Some(clause)
        }

        lazy val gen = nextGeneration(currentGeneration)
        for (template <- byType(tpe).values) {
          val equals = mkEquals(template.ids._2, caller)
          registerAppBlocker(gen, key, Left(template), equals, args)
        }

        applications += tpe -> (applications(tpe) + key)

        clauses ++ freshAppClause
      }
    }
  }

  private def equalityClauses(template: LambdaTemplate): Clauses = {
    byType(template.tpe).values.map { that =>
      val equals = mkEquals(template.ids._2, that.ids._2)
      mkImplies(
        mkAnd(template.pathVar._2, that.pathVar._2),
        if (template.structure.lambda == that.structure.lambda) {
          val pairs = template.structure.dependencies zip that.structure.dependencies
          val filtered = pairs.filter(p => p._1 != p._2)
          if (filtered.isEmpty) {
            equals
          } else {
            val eqs = filtered.map(p => mkEquals(p._1, p._2))
            mkEquals(mkAnd(eqs : _*), equals)
          }
        } else {
          mkNot(equals)
        })
    }.toSeq
  }

  private[unrolling] object lambdasManager extends Manager {
    // Function instantiations have their own defblocker
    val lambdaBlockers = new IncrementalMap[TemplateAppInfo, Encoded]()

    // Keep which function invocation is guarded by which guard,
    // also specify the generation of the blocker.
    val appInfos      = new IncrementalMap[(Encoded, App), (Int, Int, Encoded, Encoded, Set[TemplateAppInfo])]()
    val appBlockers   = new IncrementalMap[(Encoded, App), Encoded]()
    val blockerToApps = new IncrementalMap[Encoded, (Encoded, App)]()

    val byID            = new IncrementalMap[Encoded, LambdaTemplate]
    val byType          = new IncrementalMap[FunctionType, Map[LambdaStructure, LambdaTemplate]].withDefaultValue(Map.empty)
    val applications    = new IncrementalMap[FunctionType, Set[(Encoded, App)]].withDefaultValue(Set.empty)
    val knownFree       = new IncrementalMap[FunctionType, Set[Encoded]].withDefaultValue(Set.empty)
    val maybeFree       = new IncrementalMap[FunctionType, Set[(Encoded, Encoded)]].withDefaultValue(Set.empty)
    val freeBlockers    = new IncrementalMap[FunctionType, Set[(Encoded, Encoded)]].withDefaultValue(Set.empty)

    val instantiated = new IncrementalSet[(Encoded, App)]

    val typeBlockers = new IncrementalMap[Encoded, Encoded]()
    val typeEnablers: MutableSet[Encoded] = MutableSet.empty

    override val incrementals: Seq[IncrementalState] = Seq(
      lambdaBlockers, appInfos, appBlockers, blockerToApps,
      byID, byType, applications, knownFree, maybeFree, freeBlockers,
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

      blockerToApps --= blockers
      appInfos --= apps

      for ((app, (_, infos)) <- thisAppInfos if infos.nonEmpty) {
        val nextB = encodeSymbol(Variable(FreshIdentifier("b_lambda", true), BooleanType))
        val extension = mkOr((infos.map(_.equals).toSeq :+ nextB) : _*)
        val clause = mkEquals(appBlockers(app), extension)

        appBlockers += app -> nextB

        ctx.reporter.debug(" -> extending lambda blocker: " + clause)
        newClauses += clause
      }

      for ((app @ (b, _), (gen, infos)) <- thisAppInfos;
           info @ TemplateAppInfo(tmpl, equals, args) <- infos;
           template <- tmpl.left) {
        val newCls = new scala.collection.mutable.ListBuffer[Encoded]

        val lambdaBlocker = lambdaBlockers.get(info) match {
          case Some(lambdaBlocker) => lambdaBlocker

          case None =>
            val lambdaBlocker = encodeSymbol(Variable(FreshIdentifier("d", true), BooleanType))
            lambdaBlockers += info -> lambdaBlocker

            val newExprs = template.instantiate(lambdaBlocker, args)

            newCls ++= newExprs
            lambdaBlocker
        }

        val enabler = if (equals == trueT) b else mkAnd(equals, b)
        newCls += mkImplies(enabler, lambdaBlocker)
        impliesBlocker(b, lambdaBlocker)

        ctx.reporter.debug("Unrolling behind "+info+" ("+newCls.size+")")
        for (cl <- newCls) {
          ctx.reporter.debug("  . "+cl)
        }

        newClauses ++= newCls
      }

      ctx.reporter.debug(s"   - ${newClauses.size} new clauses")

      newClauses
    }
  }
}
