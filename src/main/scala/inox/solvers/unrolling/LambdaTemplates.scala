/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._
import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

trait LambdaTemplates { self: Templates =>
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  import typesManager._
  import lambdasManager._
  import quantificationsManager._

  private lazy val assumeChecked = options.findOptionOrDefault(optAssumeChecked)

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
      val idArgs: Seq[Variable] = lambda.params.map(_.toVariable)
      val trArgs: Seq[Encoded] = idArgs.map(v => substMap.getOrElse(v, encodeSymbol(v)))

      val (realLambda, structure, depSubst) = mkExprStructure(pathVar._1, lambda, substMap)
      val depClosures = exprOps.variablesOf(lambda).toSeq.sortBy(_.id).map(v => v -> substMap(v))

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
    val (vT, asT, app) = appCache.getOrElse(tpe, {
      val v = Variable.fresh("f", tpe)
      val as = tpe.from.map(tp => Variable.fresh("x", tp, true))
      val (vT, asT) = (encodeSymbol(v), as.map(encodeSymbol))
      val res = (vT, asT, mkEncoder(Map(v -> vT) ++ (as zip asT))(Application(v, as)))
      appCache(tpe) = res
      res
    })

    mkSubstituter(Map(vT -> caller) ++ (asT zip args))(app)
  }

  /* Generates (and caches) a type blocker for the pair `(f, app)`, and then generates the clauses
   * corresponding to the type obtained by applying `f` to the arguments of `app`. Note that this
   * is required for dependent types and ADT invariants.
   *
   * Note that the pair (f, app) uniquely determines b, tpe, and free so these don't need
   * to be part of the cache key.
   *
   * @param b - the blocker under which `f` appeared
   * @param f - the function that is being applied (either a free function from the input, or
   *            a function that was output by some named function in the program)
   * @param tpe - the type of the function `f`, either a [[FunctionType]] or a [[PiType]]
   * @param app - the app for which we are instantiating type clauses
   * @param closures - the closures that are bound in the type `tpe`
   * @param free - whether `f` corresponds to a free function in the program or a result from
   *               a named function
   */
  private def registerApplication(
    b: Encoded, f: Encoded, app: App, tpe: Type, closures: Seq[Arg], free: Boolean
  ): Option[(Encoded, Encoded, Clauses)] = {
    val tpeUnrolling: TypeUnrolling = if (free) FreeUnrolling else ContractUnrolling
    if (tpeUnrolling.unroll(tpe)) {
      val clauses = new scala.collection.mutable.ListBuffer[Encoded]

      val (typeBlocker, appResult) = typeBlockers.cached(f -> app) {
        val typeBlocker = encodeSymbol(Variable.fresh("t", BooleanType()))
        val freshBlocker = encodeSymbol(Variable.fresh("tb", BooleanType()))

        registerImplication(typeBlocker, freshBlocker)
        clauses += mkImplies(mkAnd(b, mkEquals(f, app.caller), typeBlocker), freshBlocker)

        val vars = typeOps.variablesOf(tpe).toSeq.sortBy(_.id)
        // A function type `A => B` is the non-dependent Pi type `Pi(x: A). B`, so both are
        // handled alike: the parameters are bound to the arguments of the application.
        val (params, to) = tpe match {
          case PiType(params, to) => (params, to)
          case FunctionType(from, to) => (from.map(tpe => ValDef.fresh("x", tpe, true)), to)
          case _ => throw new InternalSolverError("Unexpected function type " + tpe.asString)
        }
        val subst = (params.map(_.toVariable) zip app.args).toMap ++ (vars zip closures)

        val toVars = typeOps.variablesOf(to).toSeq.sortBy(_.id)
        val toClosures = toVars.map(subst)
        val toResult = encodeSymbol(Variable.fresh("result", BooleanType(), true))
        // the application result descends from both `f` and the arguments of `app`
        val depth = currentWitnessDepth max witnessDepths.getOrElse(f, 0) max appDepths.getOrElse(app, 0)
        clauses ++= withWitnessDepth(depth) {
          instantiateType(freshBlocker, Typing(to, app.encoded, Constraint(toResult, toClosures, free)))
        }

        // A function of type `Pi(x: A). B` only maps arguments in `A` to results in `B`, so the
        // codomain must only be assumed (or checked) for arguments that lie in the domain.
        // Under `optAssumeChecked`, the front-end has checked that applications only receive
        // arguments in the domain, so the codomain is assumed directly. This spares a membership
        // check per application, which is costly when the domain is an ADT with refined fields.
        val domainResults = if (assumeChecked) Seq.empty else (params zip app.args).collect {
          case (vd, arg) if ContractUnrolling.unroll(vd.tpe) =>
            val domResult = encodeSymbol(Variable.fresh("dom", BooleanType(), true))
            val domClosures = typeOps.variablesOf(vd.tpe).toSeq.sortBy(_.id).map(subst)
            clauses ++= withWitnessDepth(depth) {
              instantiateType(freshBlocker, Typing(vd.tpe, arg.encoded, Membership(domResult, domClosures)))
            }
            domResult
        }

        val appResult = if (domainResults.isEmpty) toResult else {
          val appResult = encodeSymbol(Variable.fresh("result", BooleanType(), true))
          clauses += mkImplies(freshBlocker, mkEquals(appResult, mkImplies(mkAnd(domainResults*), toResult)))
          appResult
        }

        (typeBlocker, appResult)
      }

      Some((typeBlocker, appResult, clauses.toSeq))
    } else {
      None
    }
  }

  def registerFunction(b: Encoded, r: Encoded, tpe: Type, f: Encoded, closures: Seq[Arg], free: Boolean): Clauses = {
    reporter.debug(s"-> registering free function $b ==> $f: $tpe")
    val ft @ FunctionType(_, _) = tpe.getType: @unchecked
    freeFunctions += ft -> (freeFunctions(ft) + (b -> f))

    val clauses = new scala.collection.mutable.ListBuffer[Encoded]

    // The blocker of a function-typed application result only bounds whether its typing holds,
    // so the result is also considered active whenever the application is (see [[resultGuards]])
    val active = resultGuards.get(f).map(a => mkOr(b, a)).getOrElse(b)

    // Add non-free blocker clause
    val isFree = encodeSymbol(Variable.fresh("b_free", BooleanType(), true))
    locally {
      val nextB = encodeSymbol(Variable.fresh("b_next", BooleanType(), true))
      nonFreeBlockers += f -> ((isFree, nextB))

      clauses += mkImplies(active, mkEquals(isFree, mkNot(mkOr((for {
        template <- byType(ft).values
        if canBeEqual(template.ids._2, f)
      } yield {
        mkAnd(template.start, mkEquals(template.ids._2, f))
      }).toSeq :+ nextB*))))
    }

    // Add type blocker clause
    locally {
      val nextB  = encodeSymbol(Variable.fresh("b_and", BooleanType(), true))
      freeBlockers += ft -> (freeBlockers(ft) + ((nextB, b, tpe, f, closures, free)))

      val blockedResults = for {
        (bApp, app @ App(caller, _, _, _)) <- applications(ft)
        if canBeEqual(caller, f)
        (typeBlocker, appResult, appClauses) <- registerApplication(b, f, app, tpe, closures, free)
      } yield {
        clauses ++= appClauses
        clauses += mkImplies(bApp, typeBlocker)
        mkImplies(typeBlocker, appResult)
      }

      clauses += mkImplies(b, mkEquals(r, mkAnd(blockedResults.toSeq :+ nextB*)))
    }

    if (ft.from.isEmpty) clauses ++= (for {
      template <- byType(ft).values.toList
      if canBeEqual(template.ids._2, f) && isPureTemplate(template)
    } yield arglessEquality(b, isFree, f, ft, template))

    lazy val gen = nextGeneration(currentGeneration)
    for (app @ (_, App(caller, _, args, _)) <- applications(ft)) {
      if (f == caller) {
        // We unroll this app immediately to increase performance for model finding
        val cond = mkAnd(b, isFree)
        registerAppInfo(currentGeneration, app, Right(f), cond, args)
      } else {
        val cond = mkAnd(b, isFree, mkEquals(f, caller))
        registerAppInfo(gen, app, Right(f), cond, args)
      }
    }

    // Make sure `f` has a distinguishing input with every other function it differs from
    if (free && functionWitnesses) {
      val guard = mkAnd(active, isFree)
      if (currentWitnessDepth > 0) witnessDepths += f -> currentWitnessDepth

      for ((otherGuard, other) <- witnessFunctions(ft).toSeq if other != f) {
        clauses ++= registerWitness(mkAnd(guard, otherGuard), ft, f, other, onDemand = onDemandFreeWitnesses)
      }

      for (template <- byType(ft).values.toSeq) {
        clauses ++= registerWitness(mkAnd(guard, template.start), ft, f, template.ids._2, onDemand = onDemandFreeWitnesses)
      }

      witnessFunctions += ft -> (witnessFunctions(ft) + (guard -> f))
    }

    clauses.toSeq
  }

  private def isPureTemplate(template: LambdaTemplate): Boolean = template.structure.body match {
    case Lambda(_, _: Variable) => true
    case _ => false
  }

  /** Equates the free function `f` with the pure, argument-less lambda of `template` when they
    * return the same value.
    *
    * A free function's model is the lambda that returns its value (`() => f()`), which is
    * structurally equal to the pure lambda's model when the values agree, so the solver must not
    * consider them distinct. This only holds while `f` is free: when `f` is equal to another lambda,
    * the model of `f` is that lambda, and agreeing on their value doesn't make the two lambdas
    * equal. Without the `isFree` guard, `f == () => g(x)` and `() => Uu` (both of type `() => Unit`)
    * would force `() => g(x) == () => Uu`, which is UNSAT although both lambdas exist.
    */
  private def arglessEquality(b: Encoded, isFree: Encoded, f: Encoded, ft: FunctionType, template: LambdaTemplate): Encoded = {
    val lambda = template.ids._2
    val (tmplApp, fApp) = (mkApp(lambda, ft, Seq.empty), mkApp(f, ft, Seq.empty))
    mkImplies(mkAnd(b, isFree, template.start, mkEquals(tmplApp, fApp)), mkEquals(lambda, f))
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
        case (s, t) if s `subsumes` template.structure => (t.ids._2, Seq.empty)
      }
    }.getOrElse {
      val idT = encodeSymbol(template.ids._1)
      val newTemplate = template.concretize(idT)

      val orderingClauses = newTemplate.closures.flatMap {
        case (v, dep) => registerClosure(newTemplate.start, idT -> newTemplate.tpe, dep -> v.getType)
      }

      // make sure we introduce sound equality constraints between closures that take no arguments
      val arglessEqClauses: Clauses = if (newTemplate.tpe.from.nonEmpty || !isPureTemplate(newTemplate)) {
        Seq.empty
      } else {
        for ((b,f) <- freeFunctions(newTemplate.tpe).toSeq if canBeEqual(idT, f)) yield {
          arglessEquality(b, nonFreeBlockers(f)._1, f, newTemplate.tpe, newTemplate)
        }
      }

      val nonFreeClauses = for ((b,f) <- freeFunctions(newTemplate.tpe).toSeq if canBeEqual(idT, f)) yield {
        val (blocker, lastB) = nonFreeBlockers(f)
        val nextB = encodeSymbol(Variable.fresh("b_next", BooleanType(), true))
        nonFreeBlockers += f -> ((blocker, nextB))

        mkImplies(b, mkEquals(lastB, mkOr(mkAnd(newTemplate.start, mkEquals(newTemplate.ids._2, f)), nextB)))
      }

      // make sure we have sound equality between the new lambda and previously defined ones
      val clauses = newTemplate.structure.instantiation ++
        equalityClauses(newTemplate) ++
        orderingClauses ++
        arglessEqClauses ++
        nonFreeClauses

      byID += idT -> newTemplate
      if (currentWitnessDepth > 0) witnessDepths += idT -> currentWitnessDepth
      byType += newTemplate.tpe -> (byType(newTemplate.tpe) + (newTemplate.structure -> newTemplate))

      val gen = nextGeneration(currentGeneration)
      for (app @ (_, App(caller, _, args, _)) <- applications(newTemplate.tpe)) {
        val cond = mkAnd(newTemplate.start, mkEquals(idT, caller))
        registerAppInfo(gen, app, Left(newTemplate), cond, args)
      }

      // make sure free functions have a distinguishing input with the new lambda (if they differ)
      val witnessClauses = for ((guard, f) <- witnessFunctions(newTemplate.tpe).toSeq) yield {
        registerWitness(mkAnd(guard, newTemplate.start), newTemplate.tpe, f, idT, onDemand = onDemandFreeWitnesses)
      }

      (idT, clauses ++ witnessClauses.flatten)
    }
  }

  def instantiateApp(blocker: Encoded, app: App): Clauses = {
    val App(caller, ft @ FunctionType(from, to), args, encoded) = app

    val key = blocker -> app
    var clauses: Clauses = Seq.empty
    if (!instantiated(key)) {
      instantiated += key

      if (functionWitnesses && ft.to.isInstanceOf[FunctionType]) {
        val active = resultGuards.cached(app.encoded)(encodeSymbol(Variable.fresh("b_active", BooleanType(), true)))
        clauses :+= mkImplies(blocker, active)
      }

      if (!appBlockers.isDefinedAt(key)) {
        val firstB = encodeSymbol(Variable.fresh("b_lambda", BooleanType(), true))
        registerAppBlocker(key, firstB)
        clauses :+= mkImplies(mkNot(firstB), mkNot(blocker))
      }

      if (byID `contains` caller) {
        /* We register this app at the CURRENT generation to increase the performance
         * of fold-style higher-order functions (the first-class function will be
         * dispatched immediately after the fold-style function unrolling). */
        registerAppInfo(currentGeneration, key, Left(byID(caller)), trueT, args)
      } else {
        lazy val gen = nextGeneration(currentGeneration)
        for (template <- byType(ft).values.toList if canBeEqual(caller, template.ids._2)) {
          val cond = mkAnd(template.start, mkEquals(template.ids._2, caller))
          registerAppInfo(gen, key, Left(template), cond, args)
        }

        for ((b,f) <- freeFunctions(ft) if canBeEqual(caller, f)) {
          val (isFree, _) = nonFreeBlockers(f)
          if (f == caller) {
            // We unroll this app immediately to increase performance for model finding
            val cond = mkAnd(b, isFree)
            registerAppInfo(currentGeneration, key, Right(f), cond, args)
          } else {
            val cond = mkAnd(b, isFree, mkEquals(f, caller))
            registerAppInfo(gen, key, Right(f), cond, args)
          }
        }

        /* Make sure that if `app` correspond to an input function, then the ADT
         * invariants are asserted on its return values. */
        for {
          old @ (oldB, b, tpe, f, closures, free) <- freeBlockers(ft).toList
          if canBeEqual(caller, f)
          (typeBlocker, appResult, appClauses) <- registerApplication(b, f, app, tpe, closures, free)
        } {
          clauses ++= appClauses

          registerImplication(blocker, typeBlocker)
          clauses :+= mkImplies(blocker, typeBlocker)

          val nextB  = encodeSymbol(Variable.fresh("b_and", BooleanType(), true))
          val ext = mkAnd(mkImplies(typeBlocker, appResult), nextB)
          freeBlockers += ft -> (freeBlockers(ft) - old + ((nextB, b, tpe, f, closures, free)))
          clauses :+= mkEquals(oldB, ext)
        }

        clauses ++= congruenceClauses(blocker, app)
        applications += ft -> (applications(ft) + key)
        if (currentWitnessDepth > 0) appDepths += app -> (currentWitnessDepth max appDepths.getOrElse(app, 0))
      }
    }

    clauses
  }

  /** Function applications are congruent with respect to custom equalities: applying a
    * function to equal arguments must give equal results. SMT solvers only ensure this for
    * structurally equal arguments, so we relate `app` to the previous applications of the
    * same type whose arguments require equality unrolling.
    *
    * The equalities are registered, so that they are unrolled before a model is accepted.
    * Otherwise, the solver could pick unrelated results for the applications of a free
    * function to equal arguments, which is not a valid model.
    */
  private def congruenceClauses(blocker: Encoded, app: App): Clauses = {
    val App(caller, FunctionType(from, to), args, encoded) = app
    if (!from.exists(unrollEquality)) Seq.empty else {
      val clauses = new scala.collection.mutable.ListBuffer[Encoded]
      for ((b, that) <- applications(app.tpe) if that != app && canBeEqual(caller, that.caller)) {
        val bc = encodeSymbol(Variable.fresh("b_cong", BooleanType(), true))
        clauses += mkEquals(bc, mkAnd(blocker, b, mkEquals(caller, that.caller)))

        val argEqs = (from zip (args zip that.args)).map { case (tpe, (a1, a2)) =>
          val (equality, equalityClauses) = mkEqualities(bc, tpe, a1.encoded, a2.encoded)
          clauses ++= equalityClauses
          equality
        }

        val (resEq, resClauses) = mkEqualities(bc, to, encoded, that.encoded)
        clauses ++= resClauses
        clauses += mkImplies(mkAnd(bc +: argEqs*), resEq)
      }
      clauses.toSeq
    }
  }

  /** Without function equality, the equality of two lambdas can't be observed, and their distinguishing
    * input is only needed when model extraction must tell them apart (see [[onDemandWitnesses]]).
    * Under extensional equality, lambdas that differ structurally are only equal when they agree on
    * their distinguishing input, and nothing else can refute their equality. Their distinguishing
    * input is then unfolded like those of free functions (see [[witnessEqualities]]): the lambdas are
    * assumed equal when looking for a model, and the input is instantiated when that equality is
    * part of an unsat core.
    *
    * Instantiating them with each new lambda instead doesn't terminate: distinguishing inputs can
    * create lambdas on the spot (eg. in the typing constraints of applications), and each new lambda
    * is compared to all the previous ones. */
  private lazy val onDemandLambdaWitnesses: Boolean =
    options.findOptionOrDefault(optFunctionEquality) == FunctionEquality.None

  /** Unless function equality is extensional, whether two functions are equal never constrains their
    * applications, so their distinguishing input is only needed when a model shows both of them. The
    * pairs that involve a free function are therefore left out of the unfolding until then (see
    * [[promoteWitnesses]]). Unfolding all of them instead can make queries much harder: each function
    * term that the unrolling creates is paired with all the previous ones of its type, and the
    * equalities of these pairs are assumed by every model check. */
  private lazy val onDemandFreeWitnesses: Boolean =
    options.findOptionOrDefault(optFunctionEquality) != FunctionEquality.Extensional

  /** Equality between the new lambda `template` and the previously instantiated ones.
    *
    * Lambdas with the same structure are equal when their closures are. Under intensional equality,
    * the others are distinct. Otherwise, lambdas that differ in structure (or closures) may still be
    * extensionally equal, so the pair is instead given a distinguishing input, like pairs of free
    * functions (see [[optFunctionEquality]]). */
  private def equalityClauses(template: LambdaTemplate): Clauses = {
    val clauses = new scala.collection.mutable.ListBuffer[Encoded]
    for (that <- byType(template.tpe).values) {
      val equals = mkEquals(template.ids._2, that.ids._2)
      val (blocker, blockerClauses) = encodeBlockers(Set(template.start, that.start))
      clauses ++= blockerClauses

      val sameBody = typeOps.simplify(template.structure.body) == typeOps.simplify(that.structure.body)
      val differingLocals = (template.structure.locals zip that.structure.locals).filter(p => p._1 != p._2)
      val closuresEqual: Option[Encoded] =
        if (sameBody && differingLocals.isEmpty) {
          Some(trueT)
        } else if (sameBody) {
          Some(mkAnd(differingLocals.map { case ((v, e1), (_, e2)) =>
            // The equality is registered so that it is unrolled before a model is accepted:
            // the identifiers of lambdas with equal closures must be equal in the model.
            val (equality, equalityClauses) = mkEqualities(blocker, v.getType, e1, e2, register = true)
            clauses ++= equalityClauses
            equality
          }*))
        } else {
          None
        }

      closuresEqual match {
        case Some(eqs) if !functionWitnesses => clauses += mkImplies(blocker, mkEquals(eqs, equals))
        case None if !functionWitnesses => clauses += mkImplies(blocker, mkNot(equals))
        case _ =>
          for (eqs <- closuresEqual) clauses += mkImplies(mkAnd(blocker, eqs), equals)
          if (!sameBody || differingLocals.nonEmpty) {
            clauses ++= registerWitness(blocker, template.tpe, template.ids._2, that.ids._2, onDemand = onDemandLambdaWitnesses)
          }
      }
    }
    clauses.toSeq
  }

  def getLambdaTemplates(tpe: FunctionType): Set[LambdaTemplate] = byType(tpe).values.toSet

  /** The templates of all the lambdas that have been unrolled. */
  def getLambdaTemplates: Seq[LambdaTemplate] = byType.values.toSeq.flatMap(_.values)

  /** The witness nesting depth of the symbols currently being instantiated (0 for regular inputs).
    *
    * Everything that descends from a distinguishing input inherits its depth: the free functions in
    * its type unfolding (including ADT fields that are unfolded at later generations, see
    * [[TypeTemplates]]) and the results of the applications it takes part in. Otherwise, the free
    * functions that appear in these could get fresh distinguishing inputs of their own without bound
    * (eg. lambdas that are created anew in each distinguishing input). */
  private var currentWitnessDepth = 0

  protected def witnessDepth: Int = currentWitnessDepth

  protected def withWitnessDepth[T](depth: Int)(body: => T): T = {
    val previous = currentWitnessDepth
    currentWitnessDepth = depth
    try body finally currentWitnessDepth = previous
  }

  /** Registers a distinguishing input for `f1` and `f2` (needed when `cond` holds), to be
    * instantiated by [[instantiateWitnesses]]. Until then, the returned clause lets the solver
    * assume that `f1 == f2` through the [[PendingWitness.equality]] literal. */
  private def registerWitness(
    cond: Encoded, tpe: FunctionType, f1: Encoded, f2: Encoded, onDemand: Boolean = false
  ): Clauses = {
    val depth = (witnessDepths.getOrElse(f1, 0) max witnessDepths.getOrElse(f2, 0)) + 1
    val equality = encodeSymbol(Variable.fresh("b_eq", BooleanType(), true))
    pendingWitnesses += PendingWitness(cond, tpe, f1, f2, depth, equality, onDemand)
    // the equality of on-demand pairs isn't assumed until they are promoted, and a free literal
    // implying it lets the solver merge lambdas in models, which extraction then can't tell apart
    if (onDemand) Seq.empty else Seq(mkImplies(mkAnd(equality, cond), mkEquals(f1, f2)))
  }

  /** The equality literals of the pending distinguishing inputs, along with their depth.
    *
    * Distinguishing inputs are unfolded progressively, much like function calls: once it has found
    * a model, the solver assumes that the pairs of functions that don't have a distinguishing input
    * yet are equal. A model under these assumptions needs no more distinguishing inputs, and if they
    * make the formula unsatisfiable, the solver instantiates the ones whose equalities are in the
    * unsat core (see [[instantiateWitnesses]]). This keeps distinguishing inputs away from unsatisfiable
    * queries and from the pairs of functions that a model can keep equal.
    *
    * To stay fair with the rest of the unfolding, the solver only instantiates distinguishing inputs
    * up to a depth that grows by one with each unrolling. Each round stays finite: the free functions
    * and lambdas a distinguishing input creates on the spot inherit its depth, and the others are only
    * created by later unrollings. */
  def witnessEqualities: Map[Encoded, Int] =
    pendingWitnesses.toSeq.filterNot(_.onDemand).map(w => w.equality -> w.depth).toMap

  /** The pending distinguishing inputs that are only unfolded when model extraction needs them,
    * as the compared functions and the equality literal to instantiate them with.
    *
    * Without function equality, whether two lambdas of the program are equal can't be observed, so
    * their equality is left open. Their distinguishing input is only needed when an extracted function
    * must tell them apart, and instantiating it for every pair of lambdas can make queries much harder.
    * Pairs that involve a free function are on demand as well unless equality is extensional (see
    * [[onDemandFreeWitnesses]]), and join the regular unfolding once a model shows them. */
  def onDemandWitnesses: Seq[(FunctionType, (Encoded, Encoded, Encoded, Int))] =
    pendingWitnesses.toSeq.filter(_.onDemand).map(w => w.tpe -> (w.f1, w.f2, w.equality, w.depth))

  /** Turns the on-demand distinguishing inputs with the given equality literals into regular ones,
    * which are unfolded through their equality (see [[witnessEqualities]]). */
  def promoteWitnesses(equalities: Set[Encoded]): Clauses = {
    pendingWitnesses.toSeq.filter(w => w.onDemand && equalities(w.equality)).map { w =>
      pendingWitnesses -= w
      pendingWitnesses += w.copy(onDemand = false)
      mkImplies(mkAnd(w.equality, w.cond), mkEquals(w.f1, w.f2))
    }
  }

  /** Instantiates the pending distinguishing inputs with the given equality literals. */
  def instantiateWitnesses(equalities: Set[Encoded]): Clauses = {
    pendingWitnesses.toSeq.filter(w => equalities(w.equality)).sortBy(_.depth).flatMap { w =>
      pendingWitnesses -= w
      withWitnessDepth(w.depth)(instantiateWitness(w.cond, w.tpe, w.f1, w.f2))
    }
  }

  /** Whether distinct functions have a distinguishing input, that is whether function equality is
    * extensional or unobservable (see [[optFunctionEquality]]).
    *
    * For a pair of functions `f` and `g`, we then introduce fresh witness arguments `ws` such that
    * `f != g ==> f(ws) != g(ws)`, so that extracted models are meaningfully distinct, and lambdas
    * aren't compared structurally. Witnesses of function type are themselves free functions, so the
    * construction recurses on higher-order argument types (see `function-witnesses.md`). Under
    * intensional equality, distinct functions may agree on every input, and models compare them
    * structurally instead. */
  protected lazy val functionWitnesses: Boolean =
    options.findOptionOrDefault(optFunctionEquality) != FunctionEquality.Intensional

  /** Whether `e` is the argument of a distinguishing input (see [[Templates.instantiateWitness]]). */
  def isWitnessArgument(e: Encoded): Boolean = witnessArguments(e)

  /** The instantiated distinguishing inputs, as the arguments on which each pair of functions
    * is compared (see [[Templates.instantiateWitness]]). */
  def distinguishingInputs: Seq[((Encoded, Encoded), (FunctionType, Seq[Encoded]))] = witnessInputs.toSeq

  protected case class PendingWitness(
    cond: Encoded, tpe: FunctionType, f1: Encoded, f2: Encoded, depth: Int, equality: Encoded, onDemand: Boolean)

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
    val byID = new IncrementalMap[Encoded, LambdaTemplate]

    /** This is a mapping from function types to all known lambda instantiations of that type
      * keyed by their structure (for faster lookup).
      * This map is also populated during lambda instantiation in [[instantiateLambda]] and
      * is used to relate different lambdas that share a same type (eg. for equality).
      * The templates contained within `byType` and `byID` are the same.
      */
    val byType = new IncrementalMap[FunctionType, Map[TemplateStructure, LambdaTemplate]].withDefaultValue(Map.empty)

    /** This is a mapping from function types to all known function applications of functions
      * of that type. The aim is to dispatch these applications to members of the `byType` map
      * while carefuly instrumenting the resulting formulas so that satisfiability has to wait
      * for the correct lambda to be found.
      */
    val applications = new IncrementalMap[FunctionType, Set[(Encoded, App)]].withDefaultValue(Set.empty)

    /** This is a mapping from function types to all known functions which require unfolding.
      * The instrumentation associates some boolean variable with each free function symbol
      * within the quantified variable and if the function turns out to be empty (has an empty
      * return type) AND is applied somewhere, then the variable will be set to false.
      *
      * We rely on this mapping to keep track of an instrumentation that makes sure that quantifying
      * over empty function types won't lead to invalid proofs (see [[TypeTemplates.ConstraintTemplate]]).
      */
    val freeBlockers = new IncrementalMap[FunctionType, Set[(Encoded, Encoded, Type, Encoded, Seq[Arg], Boolean)]].withDefaultValue(Set.empty)

    /** This mapping is used to keep track of functions that ARE NOT equal to some lambda in the
      * program. We need this to make sure that applications of free functions that are equal to
      * some lambda are correctly dispatched to their actual bodies.
      */
    val nonFreeBlockers = new IncrementalMap[Encoded, (Encoded, Encoded)]

    /** This mapping is used for
      * 1. to cache datatype unfoldings of free function application results, and
      * 2. to keep track of the boolean variable that must be set to false as described above in
      *    [[freeBlockers]].
      * The map is keyed by a free function and an app.
      */
    val typeBlockers = new IncrementalMap[(Encoded, App), (Encoded, Encoded)]()

    /** This mapping maintains the set of all known free functions within the input formula
      * and is used to ensure sound models for functions that take no arguments.
      */
    val freeFunctions = new IncrementalMap[FunctionType, Set[(Encoded, Encoded)]].withDefaultValue(Set.empty)

    val instantiated = new IncrementalSet[(Encoded, App)]

    /** This mapping maintains the set of free functions (along with the condition under which
      * they are free) which require distinguishing inputs with other functions of the same type.
      * @see [[Templates.instantiateWitness]]
      */
    val witnessFunctions = new IncrementalMap[FunctionType, Set[(Encoded, Encoded)]].withDefaultValue(Set.empty)

    /** Witness nesting depth of the free functions that were introduced as distinguishing inputs. */
    val witnessDepths = new IncrementalMap[Encoded, Int]

    /** Witness nesting depth of the applications that were registered while instantiating distinguishing inputs. */
    val appDepths = new IncrementalMap[App, Int]

    /** For function-typed applications, a literal that holds whenever the application is reached.
      * Results of applications are registered as free functions under a blocker that is only an
      * upper bound, which would let a model keep two distinct results without distinguishing them. */
    val resultGuards = new IncrementalMap[Encoded, Encoded]

    /** The witness arguments of the instantiated distinguishing inputs. */
    val witnessArguments = new IncrementalSet[Encoded]

    /** The type and arguments of the distinguishing input of each pair of functions that received one. */
    val witnessInputs = new IncrementalMap[(Encoded, Encoded), (FunctionType, Seq[Encoded])]

    /** The distinguishing inputs that haven't been instantiated yet. */
    val pendingWitnesses = new IncrementalSet[PendingWitness]

    val incrementals: Seq[IncrementalState] = Seq(
      lambdaBlockers, appInfos, appBlockers, blockerToApps,
      byID, byType, applications, freeBlockers, nonFreeBlockers, freeFunctions,
      instantiated, typeBlockers, witnessFunctions, witnessDepths, appDepths, resultGuards, witnessArguments, witnessInputs, pendingWitnesses)

    def unrollGeneration: Option[Int] =
      if (appInfos.isEmpty) None
      else Some(appInfos.values.map(_._1).min)

    private def assumptions: Seq[Encoded] =
      freeBlockers.toSeq.flatMap(_._2.map(_._1)) ++
      nonFreeBlockers.toSeq.map(p => mkNot(p._2._2))

    def satisfactionAssumptions = appBlockers.map(p => mkNot(p._2)).toSeq ++ assumptions
    def refutationAssumptions = assumptions

    def promoteBlocker(b: Encoded): Boolean = {
      if (blockerToApps `contains` b) {
        val app = blockerToApps(b)
        if (appInfos `contains` app) {
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
          }).toSeq :+ nextB)*)

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

                // the lambda body is instantiated on the arguments of `app`, so it inherits their witness depth
                val depth = appDepths.getOrElse(app._2, 0) max witnessDepths.getOrElse(template.ids._2, 0)
                val instClauses: Clauses = withWitnessDepth(depth)(template.instantiate(lambdaBlocker, args))

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

      newClauses.toSeq
    }
  }
}
