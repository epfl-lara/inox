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

  import lambdasManager._

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
      // The closures that order lambdas are those of the normalized lambda, whose equality is that of
      // its closures: a lambda that lifts a call `f()` only captures its value, not `f`, and can equal `f`
      val depClosures = exprOps.variablesOf(realLambda).toSeq.sortBy(_.id).map(v => v -> depSubst(v))

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
        substMap = depSubst + (lid -> lidT), optApp = Some(lidT -> tpe), partial = true)

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

    override def instantiate(blocker: Encoded, args: Seq[Arg], failure: Encoded): Clauses = {
      val (b, clauses) = encodeBlockers(Set(blocker, contents.pathVar._2))
      clauses ++ super.instantiate(b, args, failure)
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
        clauses ++= Rule.Enables(mkAnd(b, mkEquals(f, app.caller), typeBlocker), freshBlocker).clauses

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
        val depth = witnessDepth max functionDepth(f) max appDepth(app)
        clauses ++= withWitnessDepth(depth) {
          instantiateType(freshBlocker, Typing(to, app.encoded, Constraint(toResult, toClosures, free)))
        }

        // A function of type `Pi(x: A). B` only maps arguments in `A` to results in `B`, so the
        // codomain must only be assumed (or checked) for arguments that lie in the domain.
        // Under `optAssumeChecked`, the front-end has checked that applications only receive
        // arguments in the domain, so the codomain is assumed directly. This spares a membership
        // check per application, which is costly when the domain is an ADT with refined fields.
        val domainResults = if (modes.assumeChecked) Seq.empty else (params zip app.args).collect {
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
          clauses ++= Rule.Define(Some(freshBlocker), appResult, mkImplies(mkAnd(domainResults*), toResult)).clauses
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
      val equalLambdas = OpenOr("b_next", AssumedComplete.Always)
      nonFreeBlockers += f -> ((isFree, equalLambdas))

      clauses ++= Rule.Define(Some(active), isFree, mkNot(equalLambdas.withOperands((for {
        template <- byType(ft).values
        if canBeEqual(template.ids._2, f)
      } yield {
        mkAnd(template.start, mkEquals(template.ids._2, f))
      }).toSeq))).clauses
    }

    // Add type blocker clause
    locally {
      val typedResults = OpenAnd("b_and", AssumedComplete.Always)
      freeBlockers += ft -> (freeBlockers(ft) + ((typedResults, b, tpe, f, closures, free)))

      val blockedResults = for {
        (bApp, app @ App(caller, _, _, _)) <- applications(ft)
        if canBeEqual(caller, f)
        (typeBlocker, appResult, appClauses) <- registerApplication(b, f, app, tpe, closures, free)
      } yield {
        clauses ++= appClauses
        clauses ++= Rule.Enables(bApp, typeBlocker).clauses
        mkImplies(typeBlocker, appResult)
      }

      clauses ++= Rule.Define(Some(b), r, typedResults.withOperands(blockedResults.toSeq)).clauses
    }

    if (ft.from.isEmpty) clauses ++= (for {
      template <- byType(ft).values.toList
      if canBeEqual(template.ids._2, f) && isPureTemplate(template)
      clause <- arglessEquality(b, isFree, f, ft, template)
    } yield clause)

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
    if (free && modes.functionWitnesses) {
      val guard = mkAnd(active, isFree)
      recordFunctionDepth(f)

      for ((otherGuard, other) <- witnessedFunctions(ft).toSeq if other != f) {
        clauses ++= registerWitness(mkAnd(guard, otherGuard), ft, f, other, onDemand = modes.onDemandFreeWitnesses)
      }

      for (template <- byType(ft).values.toSeq) {
        clauses ++= registerWitness(mkAnd(guard, template.start), ft, f, template.ids._2, onDemand = modes.onDemandFreeWitnesses)
      }

      registerWitnessedFunction(ft, guard, f)
    }

    clauses.toSeq
  }

  /** The lambdas and the functions of their type that they capture, which the unrolling hasn't
    * related yet (see [[TypeTemplates.registerCapturedFunctions]]), as the lambda's start blocker,
    * the lambda and the function. A model that makes them equal must relate them first. */
  protected def equalCaptures: Seq[(Encoded, Encoded, Encoded)] = for {
    (ft, templates) <- byType.toSeq
    functions = (freeFunctions(ft).toSeq.map(_._2) ++ applications(ft).toSeq.map(_._2.caller)).distinct
    template <- templates.values.toSeq
    f <- functions if !canBeEqual(template.ids._2, f)
  } yield (template.start, template.ids._2, f)

  /** Adds the clauses that follow from the equality of `lambda` and a function `f` that it captures,
    * which the unrolling left out (see [[equalCaptures]]). */
  protected def relateCapture(lambda: Encoded, f: Encoded): Clauses = {
    relateCaptured(lambda, f)
    val template = byID(lambda)
    val ft = template.tpe
    val clauses = new scala.collection.mutable.ListBuffer[Encoded]

    for ((b, g) <- freeFunctions(ft) if g == f) {
      if (ft.from.isEmpty && isPureTemplate(template)) {
        clauses ++= arglessEquality(b, nonFreeBlockers(f)._1, f, ft, template)
      }

      val (isFree, equalLambdas) = nonFreeBlockers(f)
      val next = equalLambdas.next
      nonFreeBlockers += f -> ((isFree, next))
      clauses ++= equalLambdas.link(next, Seq(mkAnd(template.start, mkEquals(lambda, f))), Some(b))
    }

    // the model that made them equal is only checked again once these applications are unrolled
    for (app @ (_, App(caller, _, args, _)) <- applications(ft) if caller == f) {
      registerAppInfo(currentGeneration, app, Left(template), mkAnd(template.start, mkEquals(lambda, caller)), args)
    }

    clauses.toSeq
  }

  private def isPureTemplate(template: LambdaTemplate): Boolean = template.structure.body match {
    case Lambda(_, _: Variable) => true
    case _ => false
  }

  /** Equates the free function `f` with the pure, argument-less lambda of `template` when they
    * return the same value (see [[Rule.ArglessEquality]]).
    *
    * A free function's model is the lambda that returns its value (`() => f()`), which is
    * structurally equal to the pure lambda's model when the values agree, so the solver must not
    * consider them distinct. This only holds while `f` is free: when `f` is equal to another lambda,
    * the model of `f` is that lambda, and agreeing on their value doesn't make the two lambdas
    * equal. Without the `isFree` guard, `f == () => g(x)` and `() => Uu` (both of type `() => Unit`)
    * would force `() => g(x) == () => Uu`, which is UNSAT although both lambdas exist.
    */
  private def arglessEquality(b: Encoded, isFree: Encoded, f: Encoded, ft: FunctionType, template: LambdaTemplate): Clauses =
    Rule.ArglessEquality(b, isFree, f, ft, template.start, template.ids._2).clauses

  private def registerAppInfo(gen: Int, key: (Encoded, App), template: Either[LambdaTemplate, Encoded], equals: Encoded, args: Seq[Arg]): Unit = {
    appInfos.register(key, gen, Set(TemplateAppInfo(template, equals, args)))
  }

  private def registerAppBlocker(app: (Encoded, App), dispatch: OpenOr): Unit = {
    appBlockers.get(app).foreach(j => blockerToApps -= j.rest)
    appBlockers += app -> dispatch
    blockerToApps += dispatch.rest -> app
  }

  private def nextAppBlocker(app: (Encoded, App)): (OpenOr, OpenOr) = {
    val last = appBlockers(app)
    val next = last.next
    registerAppBlocker(app, next)
    (last, next)
  }

  def registerLambda(pointer: Encoded, target: Encoded): Boolean = byID.get(target) match {
    case Some(template) =>
      byID += pointer -> template
      applications += template.tpe -> applications(template.tpe).filterNot(_._2.caller == pointer)

      for ((key @ (_, app), _, fis) <- appInfos.entries if fis.nonEmpty && app.caller == pointer) {
        appInfos.replace(key, Set(TemplateAppInfo(template, trueT, app.args)))
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

      // A lambda that captures a function can't be equal to it as a value (a lambda value doesn't
      // contain itself), so captured functions are ordered before the lambdas that capture them.
      // Equality is only that of values under intensional equality: otherwise, `() => f()` captures
      // `f` and agrees with it on every input, so it is equal to `f`.
      //
      // Otherwise, the unrolling only relates a lambda to the functions it captures once a model
      // makes them equal (see [[registerCapturedFunctions]]).
      val orderingClauses = if (modes.functionWitnesses) Seq.empty else newTemplate.closures.flatMap {
        case (v, dep) => registerClosure(newTemplate.start, idT -> newTemplate.tpe, dep -> v.getType)
      }
      if (modes.functionWitnesses) registerCapturedFunctions(idT, newTemplate.closures.collect {
        case (v, dep) if v.getType.isInstanceOf[FunctionType] => dep
      })

      // make sure we introduce sound equality constraints between closures that take no arguments
      val arglessEqClauses: Clauses = if (newTemplate.tpe.from.nonEmpty || !isPureTemplate(newTemplate)) {
        Seq.empty
      } else {
        for ((b,f) <- freeFunctions(newTemplate.tpe).toSeq if canBeEqual(idT, f);
             clause <- arglessEquality(b, nonFreeBlockers(f)._1, f, newTemplate.tpe, newTemplate)) yield clause
      }

      val nonFreeClauses = (for ((b,f) <- freeFunctions(newTemplate.tpe).toSeq if canBeEqual(idT, f)) yield {
        val (isFree, equalLambdas) = nonFreeBlockers(f)
        val next = equalLambdas.next
        nonFreeBlockers += f -> ((isFree, next))

        equalLambdas.link(next, Seq(mkAnd(newTemplate.start, mkEquals(newTemplate.ids._2, f))), Some(b))
      }).flatten

      // make sure we have sound equality between the new lambda and previously defined ones
      val clauses = newTemplate.structure.instantiation ++
        equalityClauses(newTemplate) ++
        orderingClauses ++
        arglessEqClauses ++
        nonFreeClauses

      byID += idT -> newTemplate
      recordFunctionDepth(idT)
      byType += newTemplate.tpe -> (byType(newTemplate.tpe) + (newTemplate.structure -> newTemplate))

      val gen = nextGeneration(currentGeneration)
      for (app @ (_, App(caller, _, args, _)) <- applications(newTemplate.tpe)) {
        val cond = mkAnd(newTemplate.start, mkEquals(idT, caller))
        registerAppInfo(gen, app, Left(newTemplate), cond, args)
      }

      // make sure free functions have a distinguishing input with the new lambda (if they differ)
      val witnessClauses = for ((guard, f) <- witnessedFunctions(newTemplate.tpe).toSeq) yield {
        registerWitness(mkAnd(guard, newTemplate.start), newTemplate.tpe, f, idT, onDemand = modes.onDemandFreeWitnesses)
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

      if (modes.functionWitnesses && ft.to.isInstanceOf[FunctionType]) {
        val active = resultGuards.cached(app.encoded)(encodeSymbol(Variable.fresh("b_active", BooleanType(), true)))
        clauses ++= Rule.Enables(blocker, active).clauses
      }

      if (!appBlockers.isDefinedAt(key)) {
        val dispatch = OpenOr("b_lambda", AssumedComplete.ForModels)
        registerAppBlocker(key, dispatch)
        clauses ++= Rule.Dispatched(blocker, dispatch).clauses
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
          old @ (typedResults, b, tpe, f, closures, free) <- freeBlockers(ft).toList
          if canBeEqual(caller, f)
          (typeBlocker, appResult, appClauses) <- registerApplication(b, f, app, tpe, closures, free)
        } {
          clauses ++= appClauses

          registerImplication(blocker, typeBlocker)
          clauses ++= Rule.Enables(blocker, typeBlocker).clauses

          val next = typedResults.next
          freeBlockers += ft -> (freeBlockers(ft) - old + ((next, b, tpe, f, closures, free)))
          clauses ++= typedResults.link(next, Seq(mkImplies(typeBlocker, appResult)))
        }

        clauses ++= congruenceClauses(blocker, app)
        applications += ft -> (applications(ft) + key)
        recordAppDepth(app)
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

        val argEqs = (from zip (args zip that.args)).map { case (tpe, (a1, a2)) =>
          registeredEquality(bc, tpe, a1.encoded, a2.encoded)
        }
        val resEq = registeredEquality(bc, to, encoded, that.encoded)
        clauses ++= Rule.Define(None, bc, mkAnd(blocker, b, mkEquals(caller, that.caller))).clauses
        clauses ++= Rule.Congruence(bc +: argEqs, resEq).clauses
      }
      clauses.toSeq
    }
  }


  /** Equality between the new lambda `template` and the previously instantiated ones.
    *
    * Lambdas with the same structure are equal when their closures are. Under intensional equality,
    * the others are distinct. Otherwise, lambdas that differ in structure (or closures) may still be
    * extensionally equal, so the pair is instead given a distinguishing input, like pairs of free
    * functions (see [[optFunctionEquality]]). */
  private def equalityClauses(template: LambdaTemplate): Clauses = {
    val clauses = new scala.collection.mutable.ListBuffer[Encoded]
    val body = typeOps.simplify(template.structure.body)

    // The lambdas with the same body and closures (that only differ by the path they are defined on,
    // see [[TemplateStructure.key]]) are equal wherever they are defined. They are all equated to a
    // shared symbol, which keeps the number of clauses linear in the number of such lambdas: these
    // arise from each unfolding of a function that defines a lambda, eg. Stainless's type predicates.
    val classKey = (template.tpe, body, template.structure.locals)
    val representative = lambdaClasses.getOrElse(classKey, {
      val symbol = encodeSymbol(Variable.fresh("lc", template.tpe, true))
      lambdaClasses += classKey -> symbol
      symbol
    })
    clauses ++= Rule.SameLambda(template.start, template.ids._2, representative).clauses

    for (that <- byType(template.tpe).values) {
      val sameBody = body == typeOps.simplify(that.structure.body)
      val differingLocals = (template.structure.locals zip that.structure.locals).filter(p => p._1 != p._2)
      if (!sameBody || differingLocals.nonEmpty) {
        val (blocker, blockerClauses) = encodeBlockers(Set(template.start, that.start))
        clauses ++= blockerClauses

        val closuresEqual: Option[Encoded] =
          if (sameBody) {
            Some(mkAnd(differingLocals.map { case ((v, e1), (_, e2)) =>
              // The equality is registered so that it is unrolled before a model is accepted:
              // the identifiers of lambdas with equal closures must be equal in the model.
              registeredEquality(blocker, v.getType, e1, e2)
            }*))
          } else {
            None
          }

        val intensional = !modes.functionWitnesses
        clauses ++= Rule.LambdaEquality(blocker, template.ids._2, that.ids._2, closuresEqual, intensional).clauses
        if (!intensional) {
          clauses ++= registerWitness(blocker, template.tpe, template.ids._2, that.ids._2, onDemand = modes.onDemandLambdaWitnesses)
        }
      }
    }
    clauses.toSeq
  }

  protected def getLambdaTemplates(tpe: FunctionType): Set[LambdaTemplate] = byType(tpe).values.toSet

  /** The templates of all the lambdas that have been unrolled. */
  protected def getLambdaTemplates: Seq[LambdaTemplate] = byType.values.toSeq.flatMap(_.values)


  /** The template of the instantiated lambda whose identifier is `id`. */
  private[unrolling] def lambdaTemplate(id: Encoded): Option[LambdaTemplate] = byID.get(id)

  /** The templates of the instantiated lambdas of type `tpe`. */
  private[unrolling] def lambdaTemplates(tpe: FunctionType): Iterable[LambdaTemplate] = byType(tpe).values

  /** The templates of all the instantiated lambdas. */
  private[unrolling] def lambdaTemplates: Iterable[LambdaTemplate] = byID.values

  private[unrolling] object lambdasManager extends Manager {
    // Function instantiations have their own defblocker
    private[LambdaTemplates] val lambdaBlockers = new IncrementalMap[TemplateAppInfo, (Encoded, Encoded)]()

    // The lambdas (or free functions) that each application may be dispatched to, which are
    // unfolded with it, under the application's current blocker (see [[appBlockers]])
    private[LambdaTemplates] val appInfos      = new UnrollingQueue[(Encoded, App), TemplateAppInfo]

    /** The dispatch of each application: the disjunction of the conditions under which it is
      * dispatched to each lambda or free function found so far. The application's blocker implies
      * the disjunction (see [[instantiateApp]]), and each unrolling of the application extends it.
      *
      * Assumed complete only in model checks: until then, the application may be dispatched to a
      * lambda that is still to come, and a model must not rely on an application whose target
      * isn't unrolled yet. Its rest is also the blocker under which the application is promoted
      * (see [[blockerToApps]]). */
    private[LambdaTemplates] val appBlockers   = new IncrementalMap[(Encoded, App), OpenOr]()
    private[LambdaTemplates] val blockerToApps = new IncrementalMap[Encoded, (Encoded, App)]()

    /** This map holds the mapping from lambda identifiers to the corresponding template.
      * The map is populated during lambda instantiation in [[instantiateLambda]].
      */
    private[LambdaTemplates] val byID = new IncrementalMap[Encoded, LambdaTemplate]

    /** This is a mapping from function types to all known lambda instantiations of that type
      * keyed by their structure (for faster lookup).
      * This map is also populated during lambda instantiation in [[instantiateLambda]] and
      * is used to relate different lambdas that share a same type (eg. for equality).
      * The templates contained within `byType` and `byID` are the same.
      */
    private[LambdaTemplates] val byType = new IncrementalMap[FunctionType, Map[TemplateStructure, LambdaTemplate]].withDefaultValue(Map.empty)

    /** The lambdas that only differ by the path they are defined on are equal wherever they are
      * defined. Each such class of lambdas, keyed by type, normalized body and closures, is equated
      * to a shared symbol rather than to each of its members (see [[equalityClauses]]). */
    private[LambdaTemplates] val lambdaClasses = new IncrementalMap[(FunctionType, Expr, Seq[(Variable, Encoded)]), Encoded]

    /** This is a mapping from function types to all known function applications of functions
      * of that type. The aim is to dispatch these applications to members of the `byType` map
      * while carefuly instrumenting the resulting formulas so that satisfiability has to wait
      * for the correct lambda to be found.
      */
    private[LambdaTemplates] val applications = new IncrementalMap[FunctionType, Set[(Encoded, App)]].withDefaultValue(Set.empty)

    /** This is a mapping from function types to all known functions which require unfolding.
      * The instrumentation associates some boolean variable with each free function symbol
      * within the quantified variable and if the function turns out to be empty (has an empty
      * return type) AND is applied somewhere, then the variable will be set to false.
      *
      * We rely on this mapping to keep track of an instrumentation that makes sure that quantifying
      * over empty function types won't lead to invalid proofs (see [[TypeTemplates.ConstraintTemplate]]).
      */
    /** Each entry holds the conjunction of the typings of the function's application results
      * found so far, which defines the function's typing result (see [[registerFunction]]). It is
      * extended with each new application, and is assumed complete in every check: the typing holds when the
      * results of the applications unrolled so far are typed. */
    private[LambdaTemplates] val freeBlockers = new IncrementalMap[FunctionType, Set[(OpenAnd, Encoded, Type, Encoded, Seq[Arg], Boolean)]].withDefaultValue(Set.empty)

    /** This mapping is used to keep track of functions that ARE NOT equal to some lambda in the
      * program. We need this to make sure that applications of free functions that are equal to
      * some lambda are correctly dispatched to their actual bodies.
      *
      * Each free function maps to its `isFree` literal and the disjunction of its equalities to the
      * lambdas of its type found so far: `isFree` holds iff the function equals none of them (see
      * [[registerFunction]]). The disjunction is extended with each new lambda, and is assumed
      * complete in every check, so that `isFree` means "equal to none of the lambdas unrolled so far".
      */
    private[LambdaTemplates] val nonFreeBlockers = new IncrementalMap[Encoded, (Encoded, OpenOr)]

    /** This mapping is used for
      * 1. to cache datatype unfoldings of free function application results, and
      * 2. to keep track of the boolean variable that must be set to false as described above in
      *    [[freeBlockers]].
      * The map is keyed by a free function and an app.
      */
    private[LambdaTemplates] val typeBlockers = new IncrementalMap[(Encoded, App), (Encoded, Encoded)]()

    /** This mapping maintains the set of all known free functions within the input formula
      * and is used to ensure sound models for functions that take no arguments.
      */
    private[LambdaTemplates] val freeFunctions = new IncrementalMap[FunctionType, Set[(Encoded, Encoded)]].withDefaultValue(Set.empty)

    private[LambdaTemplates] val instantiated = new IncrementalSet[(Encoded, App)]

    /** For function-typed applications, a literal that holds whenever the application is reached.
      * Results of applications are registered as free functions under a blocker that is only an
      * upper bound, which would let a model keep two distinct results without distinguishing them. */
    private[LambdaTemplates] val resultGuards = new IncrementalMap[Encoded, Encoded]



    val incrementals: Seq[IncrementalState] = Seq(
      lambdaBlockers, appInfos, appBlockers, blockerToApps,
      byID, byType, lambdaClasses, applications, freeBlockers, nonFreeBlockers, freeFunctions,
      instantiated, typeBlockers, resultGuards)

    def unrollGeneration: Option[Int] = appInfos.generation

    private def junctions: Seq[OpenJunction[?]] =
      freeBlockers.toSeq.flatMap(_._2.map(_._1)) ++ nonFreeBlockers.toSeq.map(_._2._2)

    def satisfactionAssumptions = completenessAssumptions(appBlockers.map(_._2).toSeq ++ junctions, refuting = false)
    def refutationAssumptions = completenessAssumptions(junctions, refuting = true)

    def promoteBlocker(b: Encoded): Boolean = blockerToApps.get(b).exists(appInfos.promote)

    def unroll: Clauses = if (appInfos.isEmpty) Seq.empty else {
      val newClauses = new scala.collection.mutable.ListBuffer[Encoded]

      val thisAppInfos = appInfos.dequeue().map { case (app, gen, infos) => app -> (gen, infos) }
      val apps = thisAppInfos.map(_._1)

      val remainingApps = MutableSet.empty ++ apps

      blockerToApps --= apps.map(appBlockers(_).rest)

      val newBlockers = (for ((app, (_, infos)) <- thisAppInfos if infos.nonEmpty) yield {
        app -> nextAppBlocker(app)
      }).toMap

      for ((app @ (b, _), (gen, infos)) <- thisAppInfos if infos.nonEmpty) {
        val (last, next) = newBlockers(app)
        if (interrupted) {
          // the application is dispatched later, from `next`: `last` is linked to it with no
          // operands, so that the disjunction stays open
          newClauses ++= last.link(next, Seq.empty)
        } else {
          remainingApps -= app

          val linkClauses = last.link(next, infos.map(info => info.template match {
            case Left(template) => mkAnd(template.start, info.equals)
            case Right(_) => info.equals
          }).toSeq)
          reporter.debug(" -> extending lambda blocker: " + linkClauses.mkString(", "))
          newClauses ++= linkClauses

          for (info @ TemplateAppInfo(tmpl, equals, args) <- infos; template <- tmpl.left) {
            val newCls = new scala.collection.mutable.ListBuffer[Encoded]

            val (lambdaBlocker, lambdaFailure) = lambdaBlockers.get(info) match {
              case Some(blockerAndFailure) => blockerAndFailure

              case None =>
                val lambdaBlocker = encodeSymbol(Variable.fresh("d", BooleanType(), true))
                val lambdaFailure = encodeSymbol(Variable.fresh("fails", BooleanType(), true))
                lambdaBlockers += info -> (lambdaBlocker, lambdaFailure)

                // the lambda body is instantiated on the arguments of `app`, so it inherits their witness depth
                val depth = appDepth(app._2) max functionDepth(template.ids._2)
                val instClauses: Clauses =
                  withWitnessDepth(depth)(Rule.Unfold(template, lambdaBlocker, args, Some(lambdaFailure)).clauses)

                newCls ++= instClauses
                (lambdaBlocker, lambdaFailure)
            }

            val enabler = if (equals == trueT) b else mkAnd(equals, b)
            registerImplication(b, lambdaBlocker)
            newCls ++= Rule.Enables(enabler, lambdaBlocker).clauses
            // the application fails iff the body of the lambda it is dispatched to does
            if (modes.partialFunctions) newCls ++= Rule.DispatchFailure(enabler, appFailure(app._2), lambdaFailure).clauses

            reporter.debug("Unrolling behind "+info+" ("+newCls.size+")")
            for (cl <- newCls) {
              reporter.debug("  . "+cl)
            }

            newClauses ++= newCls
          }
        }
      }

      // the applications that an interruption left out are unfolded later
      for ((app, (gen, infos)) <- thisAppInfos if remainingApps(app)) {
        if (!appInfos.contains(app)) blockerToApps += appBlockers(app).rest -> app
        appInfos.register(app, gen, infos)
      }

      newClauses ++= newFailureDefinitions()
      reporter.debug(s"   - ${newClauses.size} new clauses")

      newClauses.toSeq
    }
  }
}
