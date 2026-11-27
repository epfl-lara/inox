/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._
import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}
import scala.collection.immutable.{ListSet, VectorMap}

/** The functions that the sources of templates name, which are no functions of the program (see
  * [[Templates.Source]]). They are Boolean uninterpreted calls whose type argument is the type
  * that they are about, and print as their symbol qualified by the SMT-LIB 3 sort of that type
  * (see [[smtlib.CVC5Certificates]]), with its refinements:
  *  - `((as typing S) "<mode>" x <closures>)`: that `x` lies in the type `T` of sort `S`, which is
  *    checked the way the mode says (see [[TypingGenerator]]): `free`, `contract` or `membership`,
  *    then `-domain` when the check is the domain of a quantifier, and `-ground` when `x` is a
  *    fresh ground;
  *  - `((as typing S) "capture" x f)`: that the functions that the value `x` of type `T` holds
  *    come before the lambda `f` that captures `x` (see [[TypeTemplates.CaptureTemplate]]);
  *  - `((as reads S) "<mode>" x <closures>)`: that the values that the reads of the collection
  *    `x` of type `T` give lie in their type (see [[Collection]]);
  *  - `(as inhabited S)`: that the type parameter `T` has values. */
object TemplateGenerator {
  val typing: Identifier = FreshIdentifier("typing")
  val reads: Identifier = FreshIdentifier("reads")
  val inhabited: Identifier = FreshIdentifier("inhabited")

  val markers: Set[Identifier] = Set(typing, reads, inhabited)
}

trait TemplateGenerator { self: Templates =>
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  /** Whether the equalities of a sort with the equality function `id` are also encoded by the
    * body of the function where their polarity is known: the simplifier inlines the calls of the
    * function, for the polarity of its quantifiers, and keeps the equalities of the sort (see
    * `FormulaSimplifier.inlines`). */
  private def inlinedEquality(id: Identifier): Boolean =
    formulaSimplifier(using PurityOptions(context)).inlines(id)

  /** The clauses that [[mkExprClauses]] generates for an expression, before [[Template.encode]]
    * encodes them.
    *
    * @param condVars        the condition variables, which guard the branches of the expression
    * @param exprVars        the variables that stand for the values of subexpressions
    * @param condTree        the condition variables that each condition variable guards
    * @param guardedExprs    the clauses under each condition variable
    * @param equations       the unguarded clauses
    * @param types           the typing constraints under each condition variable
    * @param equalities      the equalities to unroll under each condition variable
    * @param lambdas         the templates of the lambdas in the expression
    * @param quantifications the templates of the quantifiers in the expression
    * @param definitions     the definitions of condition variables that hold their own guard: these
    *                        clauses aren't guarded, but the calls and other items of each belong
    *                        under the condition variable it is listed under
    * @param meanings        the meanings of the markers that sources name, and of symbols of the
    *                        clauses (see [[Source]])
    * @param bound           the symbols that the variables of lets are replaced with (see [[sourceExpr]])
    * @param abstracted      the expressions that sources name by what the clauses have of them (see [[sourceExpr]])
    */
  protected case class TemplateClauses(
    condVars: Map[Variable, Encoded] = Map.empty,
    exprVars: Map[Variable, Encoded] = Map.empty,
    condTree: Map[Variable, Set[Variable]] = Map.empty,
    guardedExprs: Map[Variable, Seq[Expr]] = VectorMap.empty,
    equations: Seq[Expr] = Seq.empty,
    types: Types = VectorMap.empty,
    equalities: Equalities = VectorMap.empty,
    lambdas: Seq[LambdaTemplate] = Seq.empty,
    quantifications: Seq[QuantificationTemplate] = Seq.empty,
    definitions: Map[Variable, Seq[Expr]] = VectorMap.empty,
    meanings: Seq[(Expr, Expr)] = Seq.empty,
    bound: Map[Expr, Expr] = Map.empty,
    abstracted: Map[Expr, Expr] = Map.empty
  ) {
    def ++(that: TemplateClauses): TemplateClauses = TemplateClauses(
      condVars ++ that.condVars,
      exprVars ++ that.exprVars,
      condTree `merge` that.condTree,
      guardedExprs `merge` that.guardedExprs,
      equations ++ that.equations,
      types `merge` that.types,
      equalities `merge` that.equalities,
      lambdas ++ that.lambdas,
      quantifications ++ that.quantifications,
      definitions `merge` that.definitions,
      meanings ++ that.meanings,
      bound ++ that.bound,
      abstracted ++ that.abstracted
    )

    def +(pair: (Variable, Expr)): TemplateClauses = copy(guardedExprs = guardedExprs `merge` pair)

    /** The encodings of the symbols that the clauses introduce. */
    def symbols: Map[Variable, Encoded] =
      condVars ++ exprVars ++ lambdas.map(_.ids) ++ quantifications.flatMap(_.mapping) ++
        equalities.flatMap(_._2.map(_.symbols))
  }

  /** The interpretation of the uninterpreted function `id` at `tps` in the model that the solver
    * operates under (see [[AbstractUnrollingSolver.partialModel]]), if the model interprets it. */
  def interpretation(id: Identifier, tps: Seq[Type]): Option[Lambda]

  /** The free functions that stand for the uninterpreted functions at their type arguments, whose
    * applications are the uninterpreted calls. They are shared by all templates, and their models are
    * those of the uninterpreted functions. */
  protected val uninterpretedFunctions: MutableMap[(Identifier, Seq[Type]), (Variable, Encoded)] = MutableMap.empty
  private[unrolling] val uninterpretedSubst: MutableMap[Variable, Encoded] = MutableMap.empty

  /** The uninterpreted functions without parameters that the model doesn't interpret, which stand
    * for constants: their free functions are free variables of their result types, whose values are
    * the calls (as for any value, some solvers can't extract the results of nullary functions). */
  protected val uninterpretedConstants: MutableSet[(Identifier, Seq[Type])] = MutableSet.empty

  /** The free functions of the uninterpreted functions that the model interprets, whose applications
    * are calls that unfold the interpretation, as calls of the functions of the program unfold their
    * bodies (see [[FunctionTemplates]]). Their interpretations may then be recursive. */
  private[unrolling] val interpretedFunctions: MutableMap[Variable, Interpreted] = MutableMap.empty

  /** The types of the uninterpreted functions, whose free functions only have their erased types,
    * so that their models are extracted within their codomains. */
  protected val uninterpretedTypes: MutableMap[(Identifier, Seq[Type]), Type] = MutableMap.empty

  private def uninterpretedFunction(uc: UninterpretedCall): Variable =
    uninterpretedFunctions.getOrElseUpdate(uc.id -> uc.tps, {
      uninterpretedTypes(uc.id -> uc.tps) = uc.tpe
      val constant = uc.tpe match {
        case FunctionType(Seq(), to) if interpretation(uc.id, uc.tps).isEmpty => Some(to)
        case _ => None
      }
      if (constant.isDefined) uninterpretedConstants += uc.id -> uc.tps
      val f = Variable.fresh(uc.id.name, constant.getOrElse(uc.tpe).getType, true)
      val fT = encodeSymbol(f)
      uninterpretedSubst(f) = fT
      if (interpretation(uc.id, uc.tps).isDefined) interpretedFunctions(f) = Interpreted(uc.id, uc.tps)
      (f, fT)
    })._1

  /** `expr` as the source of a template whose clauses encode the lambdas of `lambdas`: its lambdas
    * are the symbols that their templates define the applications of, its quantifiers are what
    * `abstracted` has of them, and its calls of uninterpreted functions are applications of their
    * free functions, which are assumed to lie in their types (see the case of
    * [[UninterpretedCall]] in [[mkExprClauses]]). The lambdas and quantifiers of the clauses have
    * the symbols that `bound` gives to the variables of lets. */
  private[unrolling] def sourceExpr(expr: Expr, lambdas: Seq[LambdaTemplate], bound: Map[Expr, Expr],
                                    abstracted: Map[Expr, Expr]): Expr = {
    val ids = lambdas.map(t => (t.lambda: Expr) -> (t.ids._1: Expr)).toMap ++ abstracted
    // the form of an axiom has the axiom itself, which is not abstracted again, and the variables
    // of the lets of the source where the clauses have their symbols
    val unbound: Map[Expr, Expr] = bound.toSeq.collect { case (v, s: Variable) => s -> v }
      .groupBy(_._1).collect { case (s, Seq((_, v))) => (s: Expr) -> v }
    def named(e: Expr, seen: Set[Expr]): Expr = e match {
      case (_: Lambda | _: Forall) if !seen(e) && ids.get(exprOps.replace(bound, e)).exists(_ != e) =>
        ids(exprOps.replace(bound, e)) match {
          case v: Variable => v
          case form => named(exprOps.replace(unbound, form), seen + e)
        }
      case Operator(es, recons) => recons(es.map(named(_, seen)))
    }
    exprOps.postMap {
      case uc @ UninterpretedCall(id, tps, args, _) if uninterpretedFunctions.contains(id -> tps) =>
        val f = uninterpretedFunctions(id -> tps)._1
        val (app, resTpe) = uninterpretedApplication(uc, f, args)
        val (baseTpe, preds) = refinements(resTpe, app)
        Some(Assume(freeTyping(f.tpe, f), Assume(andJoin(freeTyping(baseTpe, app) +: preds), app)))
      // a construction needs the sort's invariant (see the case of [[ADT]] in [[mkExprClauses]])
      case adt: ADT if guard(adt).isDefined => constructionInvariant(adt).map(Assume(_, adt))
      // an equality that is unrolled is an application of the equality symbol of its type
      case Equals(e1, e2) if unrollEquality(e1.getType) => Some(Application(equalitySymbol(e1.getType)._1, Seq(e1, e2)))
      case _ => None
    }(named(expr, Set.empty))
  }

  /** The application of the free function `f` that stands for the uninterpreted call `uc` on the
    * arguments `args`, with the type of its result, whose parameters are bound to the arguments. */
  private def uninterpretedApplication(uc: UninterpretedCall, f: Variable, args: Seq[Expr]): (Expr, Type) = {
    val app = if (uninterpretedConstants(uc.id -> uc.tps)) f else Application(f, args).copiedFrom(uc)
    (app, uc.tpe match {
      case PiType(params, to) => typeOps.replaceFromSymbols((params zip args).toMap, to)
      case FunctionType(_, to) => to
      case tpe => throw new IllegalArgumentException(s"Uninterpreted call with type $tpe: $uc")
    })
  }

  /** The type that `tpe` refines, with what its refinements say of `value`. */
  private def refinements(tpe: Type, value: Expr): (Type, Seq[Expr]) = tpe match {
    case RefinementType(vd, pred) =>
      val (base, preds) = refinements(vd.tpe, value)
      (base, preds :+ exprOps.replaceFromSymbols(Map(vd -> value), pred))
    case _ => (tpe, Seq.empty)
  }

  private def guard(expr: Expr): Option[Expr] =
    if (modes.guardPartialOperations) definedness(expr) else None

  /** The facts that hold when `cond` holds. */
  private def conjuncts(cond: Expr): Set[Expr] = cond match {
    case And(es) => es.toSet.flatMap(conjuncts)
    case Not(Or(es)) => es.toSet.flatMap(negated)
    case Not(Not(e)) => conjuncts(e)
    case BooleanLiteral(true) => Set.empty
    case _ => Set(cond)
  }

  /** The facts that hold when `cond` doesn't hold. */
  private def negated(cond: Expr): Set[Expr] = cond match {
    case Or(es) => es.toSet.flatMap(negated)
    case Not(e) => conjuncts(e)
    case Implies(l, r) => conjuncts(l) ++ negated(r)
    case _ => Set(Not(cond))
  }

  /** Whether `expr` holds a partial operation that needs a guard, i.e. one that the conditions
    * around it don't already guard, as in `s.is(Cons) ==> s.head > 0` or
    * `if (d != 0) n / d else 0`. Facts are the conditions that are known to hold at `expr`. */
  private def hasUnguardedOperation(expr: Expr, facts: Set[Expr]): Boolean = {
    def rec(e: Expr, facts: Set[Expr]): Boolean = e match {
      case IfExpr(c, t, el) =>
        rec(c, facts) || rec(t, facts ++ conjuncts(c)) || rec(el, facts ++ negated(c))
      case And(es) =>
        es.foldLeft((false, facts)) { case ((res, fs), e) => (res || rec(e, fs), fs ++ conjuncts(e)) }._1
      case Or(es) =>
        es.foldLeft((false, facts)) { case ((res, fs), e) => (res || rec(e, fs), fs ++ negated(e)) }._1
      case Implies(l, r) =>
        rec(l, facts) || rec(r, facts ++ conjuncts(l))
      case _ if guard(e).isDefined =>
        guard(e).exists(g => !facts(g)) || rec2(e, facts)
      case _ => rec2(e, facts)
    }
    def rec2(e: Expr, facts: Set[Expr]): Boolean = {
      val Operator(es, _) = e: @unchecked
      es.exists(rec(_, facts))
    }

    modes.guardPartialOperations && rec(expr, facts)
  }

  private def isSimple(expr: Expr, facts: Set[Expr] = Set.empty): Boolean = {
    exprOps.isSimple(expr) && !exprOps.exists {
      case Equals(e1, e2) => unrollEquality(e1.getType)
      case _ => false
    } (expr) && !hasUnguardedOperation(expr, facts) // unguarded operations are encoded on their own path
  }

  // Due to a Scala 3 bug, if we name the following two methods the same, we encounter a strange error.
  // The following open ticket should be related to our problems:
  // https://github.com/lampepfl/dotty/issues/11226
  def mkClauses0(pathVar: Variable, expr: Expr, substMap: Map[Variable, Encoded], polarity: Option[Boolean] = None): TemplateClauses = {
    val (p, tmplClauses) = mkExprClauses(pathVar, expr, substMap, polarity)
    tmplClauses + (pathVar -> p)
  }

  def mkClauses1(pathVar: Variable, tpe: Type, expr: Expr, substMap: Map[Variable, Encoded])
                (using TypingGenerator): TemplateClauses = {
    val (p, tmplClauses) = mkTypeClauses(pathVar, tpe, expr, substMap)
    tmplClauses + (pathVar -> p)
  }

  /** The literals that hold where evaluation fails (see [[Builder.storeFailure]]).
    *
    * Templates for the bodies of functions and lambdas define whether their evaluation fails from
    * these literals and the failures of the calls and applications they reach (see [[Template.encode]]),
    * and only the templates of formulas assert that their evaluation doesn't fail. */
  private[unrolling] val failureSymbols: MutableSet[Variable] = MutableSet.empty

  def mergeCalls(pathVar: Variable, condVar: Variable, substMap: Map[Variable, Encoded],
                thenClauses: TemplateClauses, elseClauses: TemplateClauses): TemplateClauses = {
    val builder = new Builder(pathVar, substMap)
    builder ++= thenClauses
    builder ++= elseClauses

    // Clear all guardedExprs in builder since we're going to transform them by merging calls.
    // The transformed guardedExprs will be added to builder at the end of the function.
    builder.guardedExprs = VectorMap.empty

    def collectCalls(expr: Expr): Seq[FunctionInvocation] =
      exprOps.collectPreorder { case fi: FunctionInvocation => Seq(fi) case _ => Seq.empty[FunctionInvocation] }(expr)
    def countCalls(expr: Expr): Int =
      exprOps.count { case fi: FunctionInvocation => 1 case _ => 0}(expr)
    def replaceCall(call: FunctionInvocation, newExpr: Expr)(e: Expr): Expr =
      exprOps.replace(Map(call -> newExpr), e)

    // The calls are ordered by their first occurrence, with the blockers in insertion order, rather
    // than by hash codes, which depend on the global ids of the identifiers
    def getCalls(guardedExprs: Map[Variable, Seq[Expr]]): Seq[(TypedFunDef, Seq[(FunctionInvocation, Set[Variable])])] = {
      val occurrences = for {
        (b, es) <- guardedExprs.toSeq; e <- es; fi <- collectCalls(e)
      } yield (b -> fi)
      val blockers = occurrences.groupMap(_._2)(_._1)
      val calls = occurrences.map(_._2).distinct.map(fi => (fi, ListSet.from(blockers(fi)): Set[Variable]))
      val tfds = calls.map(_._1.tfd).distinct
      val byTfd = calls.groupBy(_._1.tfd)
      tfds.map(tfd => tfd -> byTfd(tfd).sortBy(p => countCalls(p._1)))  // place inner calls first
    }

    var thenGuarded = thenClauses.guardedExprs
    var elseGuarded = elseClauses.guardedExprs

    val thenCalls = getCalls(thenGuarded)
    val elseCalls = getCalls(elseGuarded).toMap

    // We sort common function calls in order to merge nested calls first.
    var toMerge: Seq[((FunctionInvocation, Set[Variable]), (FunctionInvocation, Set[Variable]))] =
      thenCalls
        .collect { case (tfd, calls) if elseCalls.contains(tfd) => calls zip elseCalls(tfd) }
        .flatten
        .sortBy(p => countCalls(p._1._1) + countCalls(p._2._1))

    val mergedBlockers = MutableMap.empty[Set[Variable], Variable]

    while (toMerge.nonEmpty) {
      val ((thenCall, thenBlockers), (elseCall, elseBlockers)) = toMerge.head
      toMerge = toMerge.tail

      val newExpr: Variable = Variable.fresh("call", thenCall.tfd.getType, true)
      builder.storeExpr(newExpr)

      val replaceThen = replaceCall(thenCall, newExpr)
      val replaceElse = replaceCall(elseCall, newExpr)

      thenGuarded = VectorMap.from(thenGuarded).map { case (b, es) => b -> es.map(replaceThen) }
      elseGuarded = VectorMap.from(elseGuarded).map { case (b, es) => b -> es.map(replaceElse) }
      toMerge = toMerge.map(p => (
        (replaceThen(p._1._1).asInstanceOf[FunctionInvocation], p._1._2),
        (replaceElse(p._2._1).asInstanceOf[FunctionInvocation], p._2._2)
      ))

      // the calls that are merged on the same paths share their blocker
      val newBlocker: Variable = mergedBlockers.getOrElseUpdate(thenBlockers ++ elseBlockers, {
        val newBlocker: Variable = Variable.fresh("bm", BooleanType(), true)
        builder.storeConds(thenBlockers ++ elseBlockers, newBlocker)
        builder.iff(orJoin((thenBlockers ++ elseBlockers).toSeq), newBlocker)
        newBlocker
      })

      val newArgs = (thenCall.args zip elseCall.args).map { case (thenArg, elseArg) =>
        val (newArg, argClauses) = mkExprClauses(newBlocker, ifExpr(condVar, thenArg, elseArg), builder.localSubst)
        builder ++= argClauses
        newArg
      }

      val newCall = thenCall.tfd.applied(newArgs)
      builder.storeDefinition(newBlocker, newExpr, newCall)
    }

    for ((b, es) <- thenGuarded; e <- es) builder.storeGuarded(b, e)
    for ((b, es) <- elseGuarded; e <- es) builder.storeGuarded(b, e)
    builder.result
  }

  protected def mkExprStructure(
    pathVar: Variable,
    expr: Expr,
    substMap: Map[Variable, Encoded]
  ): (Expr, TemplateStructure, Map[Variable, Encoded]) = {
    val (struct, depsByScope) = normalizeStructure(expr)
    val deps = depsByScope.map { case (v, e, _) => v -> e }.toMap

    // the dependencies that aren't simple, which the source of their clauses is of, when the
    // rules are logged (see [[dependenciesSource]])
    val encoded = scala.collection.mutable.ListBuffer[EncodedDependency]()

    val (depSubst, depContents0) =
      depsByScope.foldLeft(substMap, TemplateContents.empty(pathVar -> substMap(pathVar), Seq())) {
        case ((depSubst, contents), (v, expr, conditions)) =>
          if (isSimple(expr)) {
            // Note that we can ignore conditions in this case as the underlying
            // solver is able to find satisfying assignments for all simple terms
            val encoder = mkEncoder(depSubst)
            val ePointers = Template.lambdaPointers(encoder)(expr)
            (depSubst + (v -> encoder(expr)), contents.copy(pointers = contents.pointers ++ ePointers))
          } else if (!isSimple(expr) && conditions.isEmpty) {
            // We optimize for the case where conditions is empty as the quantifier
            // instantiation procedure relies on path condition variables staying the
            // same whenever possible.
            val (e, cls) = mkExprClauses(pathVar, expr, depSubst)

            // setup the full encoding substMap
            val clauseSubst: Map[Variable, Encoded] = depSubst ++ cls.symbols

            val extracted = Template.extractCalls(e, clauseSubst)
            val encoding = Template.encode(pathVar -> substMap(pathVar), Seq.empty, cls, clauseSubst)
            if (loggingRules) encoded += EncodedDependency(e, expr, Seq.empty, cls, clauseSubst)

            (depSubst + (v -> mkEncoder(clauseSubst)(e)), contents `merge` (
              cls.condVars, cls.exprVars, cls.condTree, encoding.clauses,
              encoding.items `merge` Map(substMap(pathVar) -> extracted.items),
              cls.lambdas, cls.quantifications, encoding.pointers ++ extracted.pointers
            ))
          } else {
            val condVar = Variable.fresh("p", BooleanType())
            val exprVar = Variable.fresh("r", v.getType)

            val localSubst = depSubst + (condVar -> encodeSymbol(condVar)) + (exprVar -> encodeSymbol(exprVar))
            val cls: TemplateClauses = mkClauses0(pathVar, Equals(condVar, andJoin(conditions)), localSubst) ++
              mkClauses0(condVar, Equals(exprVar, expr), localSubst)

            // setup the full encoding substMap
            val clauseSubst: Map[Variable, Encoded] = localSubst ++ cls.symbols

            val encoding = Template.encode(pathVar -> substMap(pathVar), Seq.empty, cls, clauseSubst)
            if (loggingRules) encoded += EncodedDependency(exprVar, expr, conditions, cls, clauseSubst)

            (depSubst + (v -> localSubst(exprVar)), contents `merge` (
              cls.condVars + (condVar -> localSubst(condVar)),
              cls.exprVars + (exprVar -> localSubst(exprVar)),
              cls.condTree `merge` Map(pathVar -> Set(condVar)),
              encoding.clauses, encoding.items, cls.lambdas, cls.quantifications, encoding.pointers
            ))
          }
      }

    val depContents = if (!loggingRules) depContents0 else
      depContents0.copy(source = dependenciesSource(pathVar -> substMap(pathVar), substMap, depSubst, encoded.toSeq))

    val sortedDeps = exprOps.variablesOf(struct).map(v => v -> deps(v)).toSeq.sortBy(_._1.id)
    val dependencies = sortedDeps.map(p => depSubst(p._1))
    val structure = new TemplateStructure(struct, dependencies, depContents)

    val freshSubst = exprOps.variablesOf(struct).map(v => v -> v.freshen).toMap
    val freshDeps = depSubst.map { case (v, e) => freshSubst.getOrElse(v, v) -> e }
    (exprOps.replaceFromSymbols(freshSubst, struct), structure, freshDeps)
  }

  /** A dependency of a structure that isn't simple: the `result` that the `clauses` give to `expr`
    * where the `conditions` hold, and the `symbols` of the clauses. */
  private case class EncodedDependency(result: Expr, expr: Expr, conditions: Seq[Expr], clauses: TemplateClauses,
                                       symbols: Map[Variable, Encoded])

  /** What the clauses of the dependencies of a structure are of (see [[Template.contents]]): the
    * values of the dependencies, each under its conditions. */
  private def dependenciesSource(pathVar: (Variable, Encoded), substMap: Map[Variable, Encoded], depSubst: Map[Variable, Encoded],
                                 deps: Seq[EncodedDependency]): Option[Source] = {
    val clauses = deps.map(_.clauses).foldLeft(TemplateClauses())(_ ++ _)
    val symbols = Template.symbols(pathVar, Seq.empty, clauses, deps.flatMap(_.symbols).toMap ++ depSubst)
    // a result that is a symbol of the clauses means the dependency
    val meanings = deps.collect { case EncodedDependency(r: Variable, expr, _, _, _) if !substMap.contains(r) => r -> expr }
    val values = deps.map { dep =>
      // a result that is a term over the symbols of the clauses, such as a product with the
      // value of a conditional, is only reached: its symbols are those that the clauses define
      val value = dep.result match {
        case r: Variable if !substMap.contains(r) => Equals(r, dep.expr)
        case _ => Let(ValDef.fresh("dep", dep.expr.getType), dep.expr, BooleanLiteral(true))
      }
      if (dep.conditions.isEmpty) value else IfExpr(andJoin(dep.conditions), value, BooleanLiteral(true))
    }
    templateSource(clauses, symbols, None, andJoin(values), meanings)
  }

  final private class Builder(pathVar: Variable, substMap: Map[Variable, Encoded]) {
    var condVars = Map[Variable, Encoded]()
    var condTree = Map[Variable, Set[Variable]](pathVar -> Set.empty)
    def storeCond(pathVar: Variable, id: Variable): Unit = {
      condVars += id -> encodeSymbol(id)
      condTree += pathVar -> (condTree.getOrElse(pathVar, Set.empty) + id)
    }

    def storeConds(pathVars: Set[Variable], id: Variable): Unit = {
      condVars += id -> encodeSymbol(id)
      for (pathVar <- pathVars) {
        condTree += pathVar -> (condTree.getOrElse(pathVar, Set.empty) + id)
      }
    }

    @inline def encodedCond(id: Variable): Encoded = substMap.getOrElse(id, condVars(id))

    var exprVars = Map[Variable, Encoded]()
    @inline def storeExpr(id: Variable): Unit = exprVars += id -> encodeSymbol(id)

    // Represents clauses of the form:
    //    id => expr && ... && expr
    var guardedExprs: Map[Variable, Seq[Expr]] = VectorMap.empty
    def storeGuarded(guardVar: Variable, expr: Expr): Unit = {
      assert(expr.getType == BooleanType(), expr.asString + " is not of type Boolean. " + explainTyping(expr))

      val prev = guardedExprs.getOrElse(guardVar, Nil)
      guardedExprs += guardVar -> (expr +: prev)
    }

    // Represents the failure of evaluation on the path `guardVar` when `cond` doesn't hold, as a
    // literal that holds exactly when the path is taken and `cond` doesn't hold (see [[failureSymbols]])
    def storeFailure(guardVar: Variable, cond: Expr): Unit = if (!modes.partialFunctions) storeGuarded(guardVar, cond) else {
      val fail = Variable.fresh("fail", BooleanType(), true)
      storeExpr(fail)
      failureSymbols += fail
      storeGuarded(guardVar, Equals(fail, Not(cond)))
      equations :+= Implies(fail, guardVar)
    }

    // The typings and equalities are kept in the order in which they are stored (see [[Items]])
    var types: Map[Encoded, Set[Typing]] = VectorMap.empty
    def storeType(pathVar: Variable, tpe: Type, arg: Expr, inDomain: Boolean = false, ground: Boolean = false)
                 (using generator: TypingGenerator): Check = {
      val b = encodedCond(pathVar)
      val encoder = mkEncoder(localSubst)
      val closures = typeOps.variablesOf(tpe).toSeq.sortBy(_.id).map(encoder).map(Left(_))
      // the source names the typing that another template unfolds (see [[instantiateTyping]])
      val (result, typing, source) = generator match {
        case FreeGenerator | ContractGenerator=>
          val typeCall: Variable = Variable.fresh("tp", BooleanType(), true)
          storeExpr(typeCall)

          // Function types are unfolded by `registerFunction`, which doesn't use the flag, unless they
          // are checked as fresh grounds (see `ensureGrounds`)
          val domain = inDomain && (ground || !tpe.isInstanceOf[FunctionType | PiType])
          val constraint = Constraint(exprVars(typeCall), closures, generator == FreeGenerator, domain, ground && domain)
          (typeCall, Typing(tpe, encoder(arg), constraint), typingMarker(typingMode(generator, domain, ground && domain), tpe, arg))

        case MembershipGenerator =>
          val typeCall: Variable = Variable.fresh("tp", BooleanType(), true)
          storeExpr(typeCall)

          (typeCall, Typing(tpe, encoder(arg), Membership(exprVars(typeCall), closures)),
            typingMarker(typingMode(generator, true, false), tpe, arg))

        case g @ CaptureGenerator(container, containerType, variable) =>
          // a function that a lambda captures comes before it, which the capture template assumes
          // (see [[CaptureTemplate]]), and the functions in the other values do, which another
          // capture template assumes
          val ordered = if (!loggingRules) BooleanLiteral(true) else Assume(tpe.getType match {
            case ft: FunctionType =>
              LessThan(Application(orderFunction(ft)._1, Seq(arg)), Application(orderFunction(containerType)._1, Seq(variable)))
            case _ => typingSource(g, tpe.getType, arg, false, false)
          }, BooleanLiteral(true))
          // @nv: note that we only store the non-dependent type here as we don't need
          //      to consider dependent types when looking at captures
          (BooleanLiteral(true), Typing(tpe.getType, encoder(arg), Capture(container, containerType)), ordered)
      }

      types = types `merge` (b -> typing)
      named(result, source)
    }

    // Types the reads of a collection whose elements have contracts or ADT invariants (see [[Collection]]).
    // The elements that only need unrolling as free values (e.g. sets, functions or type parameters) aren't typed:
    // their reads may be many (e.g. those of the heap in Stainless) and typing them doesn't help proofs.
    def storeReads(pathVar: Variable, tpe: Type, elemTpe: Type, arg: Expr, inDomain: Boolean)
                  (using generator: TypingGenerator): Check =
      if (!(generator == FreeGenerator || (generator == ContractGenerator && !inDomain)) ||
          !(ReadUnrolling `unroll` elemTpe)) Check.trivial
      else {
        val b = encodedCond(pathVar)
        val encoder = mkEncoder(localSubst)
        val closures = typeOps.variablesOf(tpe).toSeq.sortBy(_.id).map(encoder).map(Left(_))
        val readsCall: Variable = Variable.fresh("tp", BooleanType(), true)
        storeExpr(readsCall)
        val typing = Typing(tpe, encoder(arg), Collection(exprVars(readsCall), closures, generator == FreeGenerator))
        types = types `merge` (b -> typing)
        named(readsCall, typingMarker(typingMode(generator, false, false), tpe, arg, TemplateGenerator.reads))
      }

    // Represents equations (simple formulas)
    var equations = Seq[Expr]()
    @inline def iff(e1: Expr, e2: Expr): Unit = equations :+= Equals(e1, e2)

    // Defines the condition variable `id` as the path `guardVar` on which `cond` holds. Unlike an
    // equation, `cond` may hold calls and other items, which belong under `guardVar`.
    var definitions: Map[Variable, Seq[Expr]] = VectorMap.empty
    def define(guardVar: Variable, id: Variable, cond: Expr): Unit = {
      val prev = definitions.getOrElse(guardVar, Nil)
      definitions += guardVar -> (Equals(id, and(guardVar, cond)) +: prev)
    }

    var lambdas = Seq[LambdaTemplate]()
    @inline def registerLambda(lambda: LambdaTemplate): Unit = lambdas :+= lambda

    var quantifications = Seq[QuantificationTemplate]()
    @inline def registerQuantification(quantification: QuantificationTemplate): Unit =
      quantifications :+= quantification

    var equalities: Map[Encoded, Set[Equality]] = VectorMap.empty
    @inline def storeEquality(guardVar: Variable, e1: Expr, e2: Expr, defined: Boolean = false): Unit = {
      val b = encodedCond(guardVar)
      val encoder: Expr => Encoded = mkEncoder(localSubst)
      equalities = equalities `merge` (b -> Equality(e1.getType, encoder(e1), encoder(e2), defined))
    }

    @inline def localSubst: Map[Variable, Encoded] =
      substMap ++ uninterpretedSubst ++ condVars ++ exprVars ++ lambdas.map(_.ids)

    // The meanings of the symbols and markers that sources name (see [[Source]]), and of the
    // symbols that the clauses don't define with one equation, such as the result of a
    // conditional, whose value is given on each branch. Each is stored where its symbol is
    // created. They are only kept, as the bindings and abstractions below are, when the rules
    // are logged
    var meanings = Seq[(Expr, Expr)]()
    def storeMeaning(lhs: Expr, rhs: Expr): Unit =
      if (loggingRules && lhs != rhs && !lhs.isInstanceOf[Literal[?]]) meanings :+= lhs -> rhs

    /** Defines `symbol` as `value` under `guard`, with the meaning `meaning` that sources give it. */
    def storeDefinition(guard: Variable, symbol: Variable, value: Expr): Unit = storeDefinition(guard, symbol, value, value)
    def storeDefinition(guard: Variable, symbol: Variable, value: Expr, meaning: Expr): Unit = {
      storeGuarded(guard, Equals(symbol, value))
      storeMeaning(symbol, meaning)
    }

    // The check whose result is `symbol`, which another template defines, and whose source names
    // what that template is of
    def named(symbol: Expr, source: Expr): Check = { storeMeaning(symbol, source); Check(symbol, source) }

    // The check `body` under the assumption `clause`, which is a clause on the path `pathVar`
    def assuming(pathVar: Variable, clause: Expr)(body: => Check): Check = {
      storeGuarded(pathVar, clause)
      body.assuming(clause)
    }

    // The symbols that the variables of lets are replaced with
    var bound = Map[Expr, Expr]()

    // The expressions that sources name by what the clauses have of them
    var abstracted = Map[Expr, Expr]()

    def result: TemplateClauses =
      TemplateClauses(condVars, exprVars, condTree, guardedExprs, equations, types, equalities, lambdas, quantifications,
        definitions, meanings, bound, abstracted)

    def ++=(that: TemplateClauses): this.type = {
      condVars ++= that.condVars
      exprVars ++= that.exprVars
      condTree = condTree `merge` that.condTree
      guardedExprs = guardedExprs `merge` that.guardedExprs
      equations ++= that.equations
      types = types `merge` that.types
      equalities ++= that.equalities
      lambdas ++= that.lambdas
      quantifications ++= that.quantifications
      definitions = definitions `merge` that.definitions
      meanings ++= that.meanings
      bound ++= that.bound
      abstracted ++= that.abstracted
      this
    }
  }

  protected def mkExprClauses(
    pathVar: Variable,
    expr: Expr,
    substMap: Map[Variable, Encoded],
    polarity: Option[Boolean] = None,
    facts: Set[Expr] = Set.empty
  ): (Expr, TemplateClauses) = {
    exprOps.preTraversal {
      case e if unsupportedContainer(e.getType) =>
        throw new Unsupported(s"${e.getType.asString} relies on a custom equality inside a set, bag or map")
      case _ =>
    } (expr)

    val builder = new Builder(pathVar, substMap)
    import builder._

    // The facts known to hold on each path, so that the partial operations they guard need no guard
    val pathFacts = MutableMap[Variable, Set[Expr]](pathVar -> facts)
    def factsOf(v: Variable): Set[Expr] = pathFacts.getOrElse(v, Set.empty)

    // Groups the consecutive simple parts of a conjunction or disjunction, where each part may
    // rely on the facts that the parts before it give (see `conjuncts` and `negated`)
    def simpleGroups(pathVar: Variable, parts: Seq[Expr], next: Expr => Set[Expr]): Seq[Seq[Expr]] = {
      val facts = parts.scanLeft(factsOf(pathVar))((fs, e) => fs ++ next(e))
      SeqUtils.groupWhile(parts zip facts)(isSimple(_, _)).map(_.map(_._1))
    }

    def rec(pathVar: Variable, expr: Expr, pol: Option[Boolean]): Expr = expr match {
      case a @ Assume(cond, body) =>
        // The condition only holds positively unless the assumption may fail (see [[storeFailure]]),
        // where its failure literal is equal to its negation, so quantifiers need both polarities
        val e = rec(pathVar, cond, if (modes.partialFunctions) None else Some(true))
        storeFailure(pathVar, e)
        rec(pathVar, body, pol)

      case uc @ UninterpretedCall(id, tps, args, tpe) =>
        // An application of the free function that stands for the uninterpreted function, whose
        // result is an arbitrary value of the call's type, or is given by the interpretation of the
        // function once the call is unfolded
        val f = uninterpretedFunction(uc)
        val (fExpr, fClauses) = mkTypeClauses(pathVar, f.tpe, f, localSubst)(using FreeGenerator)
        storeGuarded(pathVar, fExpr)
        builder ++= fClauses

        val (app, resTpe) = uninterpretedApplication(uc, f, args.map(rec(pathVar, _, None)))
        val newExpr = Variable.fresh("uc", resTpe.getType, true)
        storeExpr(newExpr)
        storeDefinition(pathVar, newExpr, app)

        // The refinements of the result are assumed under the path, and the type that they refine
        // is the type of the result
        val (baseTpe, preds) = refinements(resTpe, newExpr)

        val (tpeExpr, tmplClauses) = mkTypeClauses(pathVar, baseTpe, newExpr, localSubst)(using FreeGenerator)
        storeGuarded(pathVar, tpeExpr)
        builder ++= tmplClauses

        for (pred <- preds) storeGuarded(pathVar, rec(pathVar, pred, Some(true)))
        newExpr

      case Error(tpe, _) =>
        // Evaluation fails on the path that leads to an error
        storeFailure(pathVar, BooleanLiteral(false))
        val newExpr = Variable.fresh("err", tpe, true)
        storeExpr(newExpr)
        // The symbol stands for the error of the source, which no clause defines it as
        storeMeaning(newExpr, expr)
        newExpr

      case l @ Let(i, e: Lambda, b) =>
        val re = rec(pathVar, e, None) // guaranteed variable!
        if (loggingRules) bound += i.toVariable -> re
        val rb = rec(pathVar, exprOps.replace(Map(i.toVariable -> re), b), pol)
        rb

      case l @ Let(i, e, b) =>
        val re = rec(pathVar, e, None)
        val bound = re match {
          // The bound expression (e.g. a conditional or a nested let) already got its own
          // variable, so we use that one instead of introducing an alias for it
          case _: Variable => re
          case _ =>
            val newExpr: Variable = Variable.fresh("lt", i.getType, true)
            storeExpr(newExpr)
            storeGuarded(pathVar, Equals(newExpr, re))
            newExpr
        }
        if (loggingRules) builder.bound += i.toVariable -> bound
        rec(pathVar, exprOps.replace(Map(i.toVariable -> bound), b), pol)

      case n @ Not(e) =>
        Not(rec(pathVar, e, pol.map(!_)))

      case i @ Implies(lhs, rhs) =>
        if (!isSimple(i, factsOf(pathVar))) {
          rec(pathVar, Or(Not(lhs), rhs), pol)
        } else {
          implies(rec(pathVar, lhs, None), rec(pathVar, rhs, None))
        }

      case a @ And(parts) =>
        val partitions = simpleGroups(pathVar, parts, conjuncts)
        partitions.map(andJoin) match {
          case Seq(e) => e
          case seq =>
            val newExpr: Variable = Variable.fresh("e", BooleanType(), true)
            storeExpr(newExpr)

            def recAnd(pathVar: Variable, partitions: Seq[Expr]): Expr = partitions match {
              case x :: Nil =>
                val xrec = rec(pathVar, x, pol)
                storeGuarded(pathVar, Equals(newExpr, xrec))
                xrec

              case x :: xs =>
                // Only a conjunction that must hold forces each conjunct to hold. When it must not
                // hold (e.g. under a negation), any conjunct may be the false one, so we cannot
                // propagate the polarity: a universal quantifier inside `x` would otherwise be
                // asserted under `pathVar`. This mirrors the non-last disjuncts in `Or` below.
                val xrec = rec(pathVar, x, pol.filter(identity))

                // the rest is evaluated on the path where `x` holds, and the conjunction is false
                // on the other one
                val newBool: Variable = Variable.fresh("b", BooleanType(), true)
                storeCond(pathVar, newBool)

                define(pathVar, newBool, xrec)
                storeGuarded(pathVar, implies(not(newBool), not(newExpr)))
                pathFacts(newBool) = factsOf(pathVar) ++ conjuncts(x)

                And(xrec, recAnd(newBool, xs))

              case Nil => scala.sys.error("Should never happen!")
            }

            storeMeaning(newExpr, recAnd(pathVar, seq))
            newExpr
        }

      case o @ Or(parts) =>
        val partitions = simpleGroups(pathVar, parts, negated)
        partitions.map(orJoin) match {
          case Seq(e) => e
          case seq =>
            val newExpr: Variable = Variable.fresh("e", BooleanType(), true)
            storeExpr(newExpr)

            def recOr(pathVar: Variable, partitions: Seq[Expr]): Expr = partitions match {
              case x :: Nil =>
                val xrec = rec(pathVar, x, pol)
                storeGuarded(pathVar, Equals(newExpr, xrec))
                xrec

              case x :: xs =>
                val xrec = rec(pathVar, x, None)

                // the rest is evaluated on the path where `x` doesn't hold, and the disjunction is
                // true on the other one
                val newBool: Variable = Variable.fresh("b", BooleanType(), true)
                storeCond(pathVar, newBool)

                define(pathVar, newBool, not(xrec))
                storeGuarded(pathVar, implies(not(newBool), newExpr))
                pathFacts(newBool) = factsOf(pathVar) ++ negated(x)

                Or(xrec, recOr(newBool, xs))

              case Nil => scala.sys.error("Should never happen!")
            }

            storeMeaning(newExpr, recOr(pathVar, seq))
            newExpr
        }

      case i @ IfExpr(cond, thenn, elze) => {
        if (isSimple(i, factsOf(pathVar))) {
          i
        } else {
          val newBool1 : Variable = Variable.fresh("b", BooleanType(), true)
          val newBool2 : Variable = Variable.fresh("b", BooleanType(), true)
          val newExpr  : Variable = Variable.fresh("e", i.getType, true)

          storeCond(pathVar, newBool1)
          storeCond(pathVar, newBool2)
          storeExpr(newExpr)

          // The path of each branch is defined from the condition, rather than the second from the
          // first, which solvers do worse with. The path of the then branch stands for the condition
          // on `pathVar`.
          val crec = rec(pathVar, cond, None)
          define(pathVar, newBool1, crec)
          define(pathVar, newBool2, not(crec))

          val (trec, tClauses) = mkExprClauses(newBool1, thenn, localSubst, pol, factsOf(pathVar) ++ conjuncts(cond))
          val (erec, eClauses) = mkExprClauses(newBool2, elze, localSubst, pol, factsOf(pathVar) ++ negated(cond))
          builder ++=  mergeCalls(pathVar, newBool1, localSubst,
                                  tClauses + (newBool1 -> Equals(newExpr, trec)),
                                  eClauses + (newBool2 -> Equals(newExpr, erec)))
          storeMeaning(newExpr, IfExpr(crec, trec, erec))

          newExpr
        }
      }

      case l: Lambda =>
        val template = LambdaTemplate(pathVar -> encodedCond(pathVar), l, localSubst)
        builder.registerLambda(template)
        template.ids._1

      case f: Forall =>
        val (assumptions, without: Forall) = liftAssumptions(f): @unchecked

        for (a <- assumptions) {
          rec(pathVar, a, Some(true))
        }

        val TopLevelAnds(conjuncts) = without.body: @unchecked

        val conjunctQs: Seq[(Expr, Expr)] = conjuncts.map { conj =>
          val vars = exprOps.variablesOf(conj)
          val conjArgs = without.params.filter(vd => vars(vd.toVariable) || hasInstance(vd.tpe) != Some(true))

          if (conjArgs.isEmpty) {
            (rec(pathVar, conj, pol), conj)
          } else {
            val forall = Forall(conjArgs, conj)
            pol match {
              case Some(p) =>
                val (res, template) = QuantificationTemplate(pathVar -> encodedCond(pathVar), p, forall, localSubst)
                registerQuantification(template)
                // an axiom holds where evaluation reaches it, and its instantiations are its
                // templates' (see [[QuantificationTemplate]])
                (res, if (p) Assume(forall, BooleanLiteral(true)) else res)
              case None =>
                val (res, negTemplate) = QuantificationTemplate(pathVar -> encodedCond(pathVar), false, forall, localSubst)

                val inst = Variable.fresh("neg-inst", BooleanType(), true)
                storeExpr(inst)
                iff(inst, res)

                val (_, posTemplate) = QuantificationTemplate(inst -> exprVars(inst), true, forall, localSubst, defer = true)
                registerQuantification(negTemplate)
                registerQuantification(posTemplate)
                (res, res)
            }
          }
        }

        // a source has the literals of the counterexamples of quantifiers that don't hold
        if (loggingRules) builder.abstracted += f -> assumptions.foldRight(andJoin(conjunctQs.map(_._2)))(Assume(_, _))
        andJoin(conjunctQs.map(_._1))

      case Equals(e1, e2) if unrollEquality(e1.getType) =>
        val (v, _) = equalitySymbol(e1.getType)
        val re1 = rec(pathVar, e1, pol)
        val re2 = rec(pathVar, e2, pol)
        val app = Application(v, Seq(re1, re2))
        // The equality of a sort is unfolded without a polarity, like the body of a function
        // (see [[EqualityTemplate]]). Where the polarity of the equality is known, the body of an
        // equality function that quantifies is encoded here instead, at that polarity, as what
        // the equality symbol is of these terms: the equality is not unfolded, and still has
        // the rules of its symbol (see [[instantiateEquality]]).
        (e1.getType, pol) match {
          case (adt: ADTType, Some(_)) if adt.getSort.hasEquality && inlinedEquality(adt.getSort.equality.get.id) =>
            storeEquality(pathVar, re1, re2, defined = true)
            val definition = adt.getSort.equality.get.applied(Seq(re1, re2)).inlined
            rec(pathVar, definition, pol) match {
              // an equality that holds has its axioms, and nothing else to say
              case BooleanLiteral(true) =>
              case encoded => storeGuarded(pathVar, Equals(app, encoded))
            }
          case _ =>
            storeEquality(pathVar, re1, re2)
        }
        app

      case adt: ADT if guard(adt).isDefined =>
        // The construction fails unless the value satisfies the sort's invariant, which may call the
        // sort's invariant on the constructed value, bound to a variable so as not to construct it again
        val res = ADT(adt.id, adt.tps, adt.args.map(a => rec(pathVar, a, None)))
        val v = Variable.fresh("adt", res.getType, true)
        storeExpr(v)
        storeDefinition(pathVar, v, res)
        if (!guard(adt).exists(factsOf(pathVar))) constructionInvariant(res).foreach { inv =>
          // the invariant only mentions the encoded fields, or calls the sort's invariant on the value
          val cond = exprOps.replace(Map(res -> v), inv)
          storeFailure(pathVar, rec(pathVar, cond, None))
        }
        v

      case e if guard(e).isDefined =>
        val Operator(as, r) = e: @unchecked
        val res = r(as.map(a => rec(pathVar, a, None)))
        if (!guard(e).exists(factsOf(pathVar))) definedness(res).foreach(storeFailure(pathVar, _))
        res

      case Operator(as, r) => r(as.map(a => rec(pathVar, a, None)))
    }

    val p = rec(pathVar, expr, polarity)
    (p, builder.result)
  }

  /** Whether the clauses of `expr` may falsify the path condition they are guarded by,
    * i.e. whether `expr` contains an assumption or an uninterpreted call, or calls a function that
    * (transitively) does, as unrolling the call falsifies the blocker it is registered under. */
  private def mayFalsifyPath(expr: Expr): Boolean = exprOps.exists {
    case fi: FunctionInvocation => callMayFalsifyPath(fi.id)
    case e => containsAssumption(e)
  }(expr)

  private def containsAssumption(e: Expr): Boolean = e match {
    case _: Assume | _: UninterpretedCall | _: Error => true
    case _ => false
  }

  private val callsMayFalsifyPath: MutableMap[Identifier, Boolean] = MutableMap.empty

  private def callMayFalsifyPath(id: Identifier): Boolean = callsMayFalsifyPath.getOrElseUpdate(id,
    reachableFunctions(id).exists(fid => exprOps.exists(containsAssumption)(getFunction(fid).fullBody)))

  private val reachable: MutableMap[Identifier, Set[Identifier]] = MutableMap.empty

  /** The functions that calls of `id` reach. The symbols of each solver are new, so their call graph, which
    * covers the whole program, would be computed again for each solver. */
  private[unrolling] def reachableFunctions(id: Identifier): Set[Identifier] =
    reachable.getOrElseUpdate(id, program.symbols.reachableFunctions(id))

  /** Whether checking that a value belongs to `tpe` may falsify the path condition. */
  private def mayFalsifyPath(tpe: Type): Boolean = typeOps.exists {
    case RefinementType(_, pred) => mayFalsifyPath(pred)
    case _ => false
  }(tpe)

  /** A type check, as [[mkTypeClauses]] unfolds it: the `result` that its clauses give it, a term
    * over the symbols that they define, and its `source`, which is the same check without the
    * clauses (see [[TemplateGenerator]]). The source has what the symbols stand for, the
    * conditionals that the blockers encode, the typings that are left to other templates, and
    * the assumptions that are clauses under a blocker; the fresh values that the check picks are
    * values that it names freely. */
  protected case class Check(result: Expr, source: Expr) {
    /** The check where `clause` holds, which the clauses assert on their own. */
    def assuming(clause: Expr): Check = Check(result, Assume(clause, source))
    /** The check on the path of `guard`, the blocker of `choice` (see `membershipGuard`). */
    def under(guard: Variable, choice: Variable): Check = Check(implies(guard, result), implies(choice, source))
    /** The check that this one and `that` both hold. */
    infix def and(that: Check): Check = Check.and(this, that)
  }

  protected object Check {
    val trivial: Check = Check(BooleanLiteral(true), BooleanLiteral(true))
    def and(checks: Check*): Check = Check(program.trees.and(checks.map(_.result)*), program.trees.and(checks.map(_.source)*))
  }

  /** Generates the clauses and other bookkeeping relevant to a type unfolding template.
    *
    * `inDomain` is set when the type check is the domain of a quantifier, i.e. when it appears
    * on the left of an implication and `expr` may range over values outside of `tpe`. The check
    * must then be fully constrained, as the solver could otherwise falsify it to weaken the formula.
    * The flag is carried over to the type templates of nested (inductive) types. */
  protected def mkTypeClauses(
    pathVar: Variable,
    tpe: Type,
    expr: Expr,
    substMap: Map[Variable, Encoded],
    inDomain: Boolean = false,
    ground: Boolean = false
  )(using generator: TypingGenerator): (Expr, TemplateClauses) = {
    val builder = new Builder(pathVar, substMap)
    import builder._

    // the typing guards a quantifier, which holds if the bound variable has no value
    if (generator == FreeGenerator && inDomain) typesManager.unfoldTypeParameters(tpe)

    case class RecursionState(
      recurseAdt: Boolean, // visit adt children/fields
      recurseMap: Boolean, // unroll map definition
      recurseSet: Boolean, // unroll set definition
      recurseBag: Boolean  // unroll bag definition
    )

    // Returns a blocker that holds iff both `pathVar` and `cond` hold. The extra blocker is only
    // introduced when `needed` (see `mayFalsifyPath`), as it slows down unrolling: the clauses
    // it guards are only constrained once the solver has established `cond`, which may require
    // unfolding further type templates.
    def guardedBy(pathVar: Variable, cond: Expr, needed: Boolean, name: String): Variable = cond match {
      case BooleanLiteral(true) => pathVar
      case _ if !needed => pathVar
      case _ =>
        val guard: Variable = Variable.fresh(name, BooleanType(), true)
        storeCond(pathVar, guard)
        iff(and(pathVar, cond), guard)
        guard
    }

    // The result of a guarded check is used under `pathVar`, so any call or application it contains
    // would be registered (and unrolled) under `pathVar` instead of `guard`. We therefore bind it to
    // a fresh variable under `guard`. Where `guard` doesn't hold, the base check is false, so
    // the conjunction it is part of doesn't depend on the (unconstrained) variable.
    def guardedResult(pathVar: Variable, guard: Variable, cond: Expr, res: Expr, name: String): Expr =
      if (guard == pathVar || res.isInstanceOf[BooleanLiteral]) res
      else {
        val newExpr: Variable = Variable.fresh(name, BooleanType(), true)
        storeExpr(newExpr)
        storeDefinition(guard, newExpr, res, IfExpr(cond, res, BooleanLiteral(false)))
        newExpr
      }

    // A blocker under `pathVar` that the solver sets freely, under which a membership check
    // instantiates its counterexample (see the function case below).
    def membershipGuard(pathVar: Variable): (Variable, Variable) = {
      val choice = Variable.fresh("choice", BooleanType(), true)
      storeExpr(choice)
      val w = Variable.fresh("w", BooleanType(), true)
      storeCond(pathVar, w)
      iff(and(pathVar, choice), w)
      (w, choice)
    }

    def rec(pathVar: Variable, tpe: Type, expr: Expr, state: RecursionState): Check = tpe match {
      case tpe if !(generator `unroll` tpe) => Check.trivial // nothing to do here!

      // The typing is stored without being unfolded here, so that `instantiateType` can defer it
      case tpe if generator == FreeGenerator && !inDomain && typesManager.isParameterTyping(tpe) =>
        storeType(pathVar, tpe, expr)

      // A function `f` lies in `Pi(x: A). B` iff `A(x0) ==> B(f(x0))` holds for all `x0`. We check
      // this at fresh values `x0` that are assumed to lie in `A` whenever the guard `w` holds:
      // if `f` lies outside of the type, the solver can pick a counterexample for `x0` and set
      // `w`, and otherwise the result can only be false if `B(f(x0))` is false for some `x0` in
      // `A`, so the result is exact in models. The guard `w` is free so that types with an empty
      // domain don't make the path infeasible.
      //
      // The domains of quantifiers in positive polarity are checked the same way: there, the result
      // may only be false if the value lies outside of the type, as it disables the instantiation.
      // So are the fresh grounds at which such quantifiers are instantiated when they have no other
      // ground (see `ensureGrounds`): assuming that the ground lies in its type would assume that the
      // type is inhabited, which a function type into an empty type isn't.
      case (_: FunctionType | _: PiType) if generator == MembershipGenerator || (inDomain && (generator == ContractGenerator || ground)) =>
        val (params, to) = tpe match {
          case PiType(params, to) => (params, to)
          case FunctionType(from, to) => (from.map(tpe => ValDef.fresh("x", tpe, true)), to)
          case _ => throw new InternalSolverError(s"Unexpected function type: ${tpe.asString}")
        }

        val (w, choice) = membershipGuard(pathVar)

        val (args, subst, domains) = params.foldLeft((Seq.empty[Variable], Map.empty[ValDef, Expr], Seq.empty[Expr])) {
          case ((args, subst, domains), vd) =>
            val paramType = typeOps.replaceFromSymbols(subst, vd.tpe)
            val arg = Variable.fresh(vd.id.name, paramType.getType, true)
            storeExpr(arg)
            // `w` can't hold if `arg` has no value, which makes the check hold
            typesManager.unfoldTypeParameters(paramType)
            val (p, paramClauses) = mkTypeClauses(w, paramType, arg, localSubst)(using FreeGenerator)
            builder ++= paramClauses
            storeGuarded(w, p)
            (args :+ arg, subst + (vd -> arg), domains :+ freeTyping(paramType, arg))
        }

        val res = rec(w, typeOps.replaceFromSymbols(subst, to), Application(expr, args), state)
        domains.foldRight(res)((domain, check) => check.assuming(domain)).under(w, choice)

      // Maps, sets and bags are checked the same way as functions: a map lies in `Map[A, B]` iff its
      // value at every key lies in `B`, and a set or bag lies in `Set[A]` or `Bag[A]` iff each of its
      // elements lies in `A`, so the result can only be false at a key or element that the solver
      // picks as a counterexample. Decomposing the value instead (see below) would let the solver
      // pick a decomposition whose parts lie outside of the type although the value doesn't, and
      // never completes for collections that may hold infinitely many elements. The keys of maps
      // must be unrefined, as the value of a map at a key outside of `A` must be its default.
      case MapType(from, to) if !(ContractUnrolling `unroll` from) &&
          (generator == MembershipGenerator || (inDomain && (generator == ContractGenerator || ground))) =>
        val (w, choice) = membershipGuard(pathVar)
        val key = Variable.fresh("key", from, true)
        storeExpr(key)
        rec(w, to, MapApply(expr, key), state).under(w, choice)

      case SetType(base) if generator == MembershipGenerator || (inDomain && generator == ContractGenerator) =>
        val (w, choice) = membershipGuard(pathVar)
        val elem = Variable.fresh("elem", base.getType, true)
        storeExpr(elem)
        assuming(w, ElementOfSet(elem, expr))(rec(w, base, elem, state)).under(w, choice)

      case BagType(base) if generator == MembershipGenerator || (inDomain && generator == ContractGenerator) =>
        val (w, choice) = membershipGuard(pathVar)
        val elem = Variable.fresh("elem", base.getType, true)
        storeExpr(elem)
        assuming(w, GreaterThan(MultiplicityInBag(elem, expr), IntegerLiteral(0)))(rec(w, base, elem, state)).under(w, choice)

      case (_: FunctionType | _: PiType) => storeType(pathVar, tpe, expr, inDomain, ground)

      case tp: TypeParameter if generator == FreeGenerator =>
        named(typesManager.storeTypeParameter(tp),
          if (!loggingRules) BooleanLiteral(true) else marker(TemplateGenerator.inhabited, tp, Seq.empty))

      case RefinementType(vd, pred) =>
        val newExpr: Variable = Variable.fresh("lt", vd.getType, true)
        storeExpr(newExpr)

        storeGuarded(pathVar, Equals(newExpr, expr))

        val recBase = rec(pathVar, vd.tpe, expr, state)

        // The predicate may only be meaningful (e.g. it may contain assumptions) when `expr`
        // belongs to the base type, so its clauses are guarded by the base type check.
        // Otherwise, a predicate failing outside of the base type would falsify `pathVar`
        // instead of simply making the type check false.
        val predVar = guardedBy(pathVar, recBase.result, mayFalsifyPath(pred), "rp")

        val (p, predClauses) = mkExprClauses(predVar,
          exprOps.replaceFromSymbols(Map(vd -> newExpr), pred), localSubst)
        builder ++= predClauses

        recBase and Check(guardedResult(pathVar, predVar, recBase.result, p, "rr"), exprOps.replaceFromSymbols(Map(vd -> expr), pred))

      case SigmaType(params, to) =>
        val (newExprs, recParams) = params.zipWithIndex.map { case (vd, i) =>
          val newExpr: Variable = Variable.fresh("lt", vd.getType, true)
          storeExpr(newExpr)

          storeGuarded(pathVar, Equals(newExpr, TupleSelect(expr, i + 1)))
          (newExpr, rec(pathVar, vd.tpe, newExpr, state))
        }.unzip

        // Similarly to refinements, the (dependent) last component is only checked
        // when the first components belong to their types.
        val toVar = guardedBy(pathVar, Check.and(recParams*).result, mayFalsifyPath(to), "sp")

        val recTo = rec(toVar,
          typeOps.replaceFromSymbols((params zip newExprs).toMap, to),
          TupleSelect(expr, params.size + 1), state)

        Check.and(recParams :+ recTo.copy(result = guardedResult(pathVar, toVar, Check.and(recParams*).result, recTo.result, "sr"))*)

      case adt: ADTType =>
        val sort = adt.getSort
        val invariant = sort.invariant
          .filter(_ => generator == FreeGenerator)
          .map(_.applied(Seq(expr)))
          .getOrElse(BooleanLiteral(true))

        Check(invariant, invariant) and (
          if (sort.definition.isInductive && !state.recurseAdt) {
            storeType(pathVar, tpe, expr, inDomain, ground)
          } else {
            val newExpr = Variable.fresh("e", BooleanType(), true)
            storeExpr(newExpr)

            val stored = for (tcons <- sort.constructors) yield {
              if (tcons.fields.exists(vd => generator `unroll` vd.tpe)) {
                val newBool: Variable = Variable.fresh("b", BooleanType(), true)
                storeCond(pathVar, newBool)

                // generate conditions for every ADT field to satisfy its type constraints,
                // but substitute field references as dependent on the current instance
                val fieldSubst = tcons.fields.map(vd => vd -> ADTSelector(expr, vd.id)).toMap
                val recProps = Check.and(tcons.fields.map { vd =>
                  val fieldType = typeOps.replaceFromSymbols(fieldSubst, vd.tpe)
                  rec(newBool, fieldType, ADTSelector(expr, vd.id), state.copy(recurseAdt = false))
                }*)

                iff(and(pathVar, isCons(expr, tcons.id)), newBool)
                storeGuarded(newBool, Equals(newExpr, recProps.result))
                Some(tcons.id -> recProps)
              } else {
                // Constructors without fields to check trivially satisfy the type. Otherwise `newExpr`
                // would be unconstrained for them, and the type check of a quantifier's domain could be
                // falsified to weaken the formula. The clause is only added for quantifier domains
                // (see `inDomain`), to keep the encoding unchanged elsewhere.
                if (inDomain) storeGuarded(pathVar, Implies(isCons(expr, tcons.id), newExpr))
                None
              }
            }

            // the fields of the constructor of the value lie in their types
            def branches(of: Check => Expr): Expr = stored.flatten.foldRight(BooleanLiteral(true): Expr) {
              case ((id, fields), rest) => IfExpr(isCons(expr, id), of(fields), rest)
            }
            storeMeaning(newExpr, branches(_.result))
            if (stored.forall(_.isEmpty)) Check.trivial else Check(newExpr, branches(_.source))
          }
        )

      case TupleType(tpes) =>
        Check.and((for ((tpe, idx) <- tpes.zipWithIndex) yield {
          rec(pathVar, tpe, TupleSelect(expr, idx + 1), state)
        })*)

      // A map, set or bag is empty, or is the update or union of a smaller one, picked freely,
      // where the source assumes that it is
      case MapType(from, to) =>
        if (!state.recurseMap) {
          storeType(pathVar, tpe, expr, inDomain, ground)
        } else {
          val newBool1 : Variable = Variable.fresh("mapIsEmpty", BooleanType(), true)
          val newBool2 : Variable = Variable.fresh("mapNonEmpty", BooleanType(), true)
          storeCond(pathVar, newBool1)
          storeCond(pathVar, newBool2)

          val condVar  : Variable = Variable.fresh("condMapEmpty", BooleanType(), true)
          val newExpr = Variable.fresh("mapRes", BooleanType(), true)
          val keyExpr: Variable = Variable.fresh("mapKey", from, true)
          val valueExpr: Variable = Variable.fresh("mapValue", to, true)
          val defaultExpr: Variable = Variable.fresh("mapDefault", to, true)
          val restExpr: Variable = Variable.fresh("mapRest", tpe, true)
          storeExpr(condVar)
          storeExpr(newExpr)
          storeExpr(keyExpr)
          storeExpr(valueExpr)
          storeExpr(defaultExpr)
          storeExpr(restExpr)
          decompositionKeys += keyExpr

          val isEmpty = Equals(expr, FiniteMap(Seq(), defaultExpr, from, to))
          storeGuarded(pathVar, Equals(condVar, isEmpty))
          iff(and(pathVar, condVar), newBool1)
          iff(and(pathVar, not(condVar)), newBool2)

          storeGuarded(newBool1, newExpr)
          val parts = assuming(newBool2, Equals(expr, MapUpdated(restExpr, keyExpr, valueExpr))) {
            rec(newBool2, tpe, restExpr, state.copy(recurseMap = false)) and
            rec(newBool2, from, keyExpr, state) and
            rec(newBool2, to, valueExpr, state)
          }
          storeDefinition(newBool2, newExpr, parts.result, IfExpr(condVar, BooleanLiteral(true), parts.result))

          rec(pathVar, to, defaultExpr, state) and Check(newExpr, IfExpr(isEmpty, BooleanLiteral(true), parts.source)) and
            storeReads(pathVar, tpe, to, expr, inDomain)
        }

      case SetType(base) =>
        if (!state.recurseSet) {
          storeType(pathVar, tpe, expr, inDomain, ground)
        } else {
          val newBool1 : Variable = Variable.fresh("setIsEmpty", BooleanType(), true)
          val newBool2 : Variable = Variable.fresh("setNonEmpty", BooleanType(), true)
          storeCond(pathVar, newBool1)
          storeCond(pathVar, newBool2)

          val condVar  : Variable = Variable.fresh("condSetEmpty", BooleanType(), true)
          val newExpr = Variable.fresh("setRes", BooleanType(), true)
          val elemExpr: Variable = Variable.fresh("setElem", base, true)
          val restExpr: Variable = Variable.fresh("setRest", tpe, true)
          storeExpr(condVar)
          storeExpr(newExpr)
          storeExpr(elemExpr)
          storeExpr(restExpr)
          decompositionKeys += elemExpr

          val isEmpty = Equals(expr, FiniteSet(Seq(), base))
          storeGuarded(pathVar, Equals(condVar, isEmpty))
          iff(and(pathVar, condVar), newBool1)
          iff(and(pathVar, not(condVar)), newBool2)

          storeGuarded(newBool1, newExpr)
          // the source states the element's typing first: the assumptions in it hold wherever the
          // set is not empty, whether or not the rest lies in the set's type
          val parts = assuming(newBool2, Equals(expr, SetUnion(FiniteSet(Seq(elemExpr), base), restExpr))) {
            val rest = rec(newBool2, tpe, restExpr, state.copy(recurseSet = false))
            val elem = rec(newBool2, base, elemExpr, state)
            Check(and(rest.result, elem.result), and(elem.source, rest.source))
          }
          storeDefinition(newBool2, newExpr, parts.result, IfExpr(condVar, BooleanLiteral(true), parts.result))

          Check(newExpr, IfExpr(isEmpty, BooleanLiteral(true), parts.source)) and storeReads(pathVar, tpe, base, expr, inDomain)
        }

      case BagType(base) =>
        if (!state.recurseBag) {
          storeType(pathVar, tpe, expr, inDomain, ground)
        } else {
          val newBool1 : Variable = Variable.fresh("bagIsEmpty", BooleanType(), true)
          val newBool2 : Variable = Variable.fresh("bagNonEmpty", BooleanType(), true)
          storeCond(pathVar, newBool1)
          storeCond(pathVar, newBool2)

          val condVar  : Variable = Variable.fresh("condBagEmpty", BooleanType(), true)
          val newExpr = Variable.fresh("bagRes", BooleanType(), true)
          val elemExpr: Variable = Variable.fresh("bagElem", base, true)
          val multExpr: Variable = Variable.fresh("bagMult", IntegerType(), true)
          val restExpr: Variable = Variable.fresh("bagRest", tpe, true)
          storeExpr(condVar)
          storeExpr(newExpr)
          storeExpr(elemExpr)
          storeExpr(multExpr)
          storeExpr(restExpr)
          decompositionKeys += elemExpr

          val isEmpty = Equals(expr, FiniteBag(Seq(), base))
          storeGuarded(pathVar, Equals(condVar, isEmpty))
          iff(and(pathVar, condVar), newBool1)
          iff(and(pathVar, not(condVar)), newBool2)

          storeGuarded(newBool1, newExpr)
          val parts = assuming(newBool2, Equals(expr, BagUnion(FiniteBag(Seq((elemExpr, multExpr)), base), restExpr))) {
            assuming(newBool2, GreaterThan(multExpr, IntegerLiteral(0))) {
              rec(newBool2, tpe, restExpr, state.copy(recurseBag = false)) and
              rec(newBool2, base, elemExpr, state) and
              rec(newBool2, IntegerType(), multExpr, state)
            }
          }
          storeDefinition(newBool2, newExpr, parts.result, IfExpr(condVar, BooleanLiteral(true), parts.result))

          Check(newExpr, IfExpr(isEmpty, BooleanLiteral(true), parts.source)) and storeReads(pathVar, tpe, base, expr, inDomain)
        }

      case _ => throw new InternalSolverError(s"Unexpected unrollable: ${tpe.asString}")
    }

    val check = rec(pathVar, tpe, expr, RecursionState(true, true, true, true))
    storeMeaning(typingSource(generator, tpe, expr, inDomain, ground), check.source)
    (check.result, builder.result)
  }

  /** The mode of a typing marker (see [[TemplateGenerator]]). */
  protected def typingMode(generator: TypingGenerator, inDomain: Boolean, ground: Boolean): String =
    (generator match {
      case FreeGenerator => "free"
      case ContractGenerator => "contract"
      case MembershipGenerator => "membership"
      case _: CaptureGenerator => "capture"
    }) + (if (inDomain) "-domain" else "") + (if (ground) "-ground" else "")

  /** That `arg` lies in `tpe`, as `generator` checks it (see [[TemplateGenerator]]): a capture names
    * the lambda that captures `arg`. */
  protected def typingSource(generator: TypingGenerator, tpe: Type, arg: Expr, inDomain: Boolean, ground: Boolean): Expr =
    generator match {
      case CaptureGenerator(_, _, container) if loggingRules =>
        marker(TemplateGenerator.typing, tpe.getType, Seq(StringLiteral(typingMode(generator, false, false)), arg, container))
      case _ => typingMarker(typingMode(generator, inDomain, ground), tpe, arg)
    }

  /** That `arg` lies in `tpe` as a free variable does (see [[TemplateGenerator]]). */
  def freeTyping(tpe: Type, arg: Expr): Expr = typingMarker(typingMode(FreeGenerator, false, false), tpe, arg)

  /** A marker that a source names, about the type `tpe` (see [[TemplateGenerator]]). The type is the
    * marker's type argument, which sources print as its sort. */
  protected def marker(id: Identifier, tpe: Type, args: Seq[Expr]): Expr =
    UninterpretedCall(id, Seq(tpe), args, FunctionType(args.map(_.getType), BooleanType()))

  /** That `arg` lies in `tpe`, checked the way `mode` says (see [[TemplateGenerator]]). Markers are
    * only named by sources, which are only kept when the rules are logged: otherwise, the marker
    * is `true`, and the type isn't printed. */
  protected def typingMarker(mode: String, tpe: Type, arg: Expr, id: Identifier = TemplateGenerator.typing): Expr =
    if (!loggingRules) BooleanLiteral(true) else marker(id, tpe, Seq(StringLiteral(mode), arg) ++ typeOps.variablesOf(tpe).toSeq.sortBy(_.id))

}
