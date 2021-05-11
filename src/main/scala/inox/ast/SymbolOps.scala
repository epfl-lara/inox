/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

import utils._
import solvers.{PurityOptions, SimplificationOptions}
import evaluators.EvaluationResults._
import transformers._

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

object SymbolOps {
  private[this] val identifiers = new scala.collection.mutable.ArrayBuffer[Identifier]
  def getId(index: Int): Identifier = synchronized {
    for (i <- identifiers.size to index) identifiers += FreshIdentifier("x", true)
    identifiers(index)
  }
}

/** Provides functions to manipulate [[Expressions.Expr]] in cases where
  * a symbol table is available (and required: see [[ExprOps]] for
  * simpler tree manipulations).
  *
  * @define encodingof Encoding of
  */
trait SymbolOps { self: TypeOps =>
  import trees._
  import trees.exprOps._
  import symbols._

  /** Override point for simplifier creation */
  protected def simplifierWithPC(popts: PurityOptions): SimplifierWithPC = new {
    val opts: PurityOptions = popts
  } with SimplifierWithPC with transformers.SimplifierWithPath

  protected trait SimplifierWithPC extends transformers.SimplifierWithPC {
    val trees: self.trees.type = self.trees
    val symbols: self.symbols.type = self.symbols
  }

  private var simplifierCache: MutableMap[PurityOptions, SimplifierWithPC] = MutableMap.empty
  def simplifier(implicit purityOpts: PurityOptions): SimplifierWithPC = synchronized {
    simplifierCache.getOrElse(purityOpts, {
      val res = simplifierWithPC(purityOpts)
      simplifierCache(purityOpts) = res
      res
    })
  }

  def simplifyExpr(expr: Expr)(implicit opts: PurityOptions): Expr = simplifyIn(expr, Path.empty)

  def simplifyIn(e: Expr, path: Path)(implicit opts: PurityOptions): Expr = {
    val s = simplifier
    val env = path.elements.foldLeft(s.initEnv) {
      case (env, Path.CloseBound(vd, e)) => env withBinding (vd -> e)
      case (env, Path.OpenBound(vd)) => env withBound vd
      case (env, Path.Condition(cond)) => env withCond cond
    }

    s.transform(e, env)
  }


  /** Override point for transformer with PC creation
    * 
    * Note that we don't actually need the `PathProvider[P]` here but it will
    * become useful in the Stainless overrides. */
  protected def transformerWithPC[P <: PathLike[P]](
    path: P,
    exprOp: (Expr, P, TransformerOp[Expr, P, Expr]) => Expr,
    typeOp: (Type, P, TransformerOp[Type, P, Type]) => Type
  )(implicit pp: PathProvider[P]): TransformerWithPC[P] = {
    new TransformerWithPC(path, exprOp, typeOp)
      with TransformerWithExprOp
      with TransformerWithTypeOp
  }

  protected class TransformerWithPC[P <: PathLike[P]](
    val initEnv: P,
    val exprOp: (Expr, P, TransformerOp[Expr, P, Expr]) => Expr,
    val typeOp: (Type, P, TransformerOp[Type, P, Type]) => Type
  ) extends transformers.TransformerWithPC {
    self0: TransformerWithExprOp with TransformerWithTypeOp =>

    override val s: self.trees.type = self.trees
    override val t: self.trees.type = self.trees
    override type Env = P
  }

  def transformWithOps[P <: PathLike[P]](e: Expr, path: P)(
    exprOp: (Expr, P, TransformerOp[Expr, P, Expr]) => Expr,
    typeOp: (Type, P, TransformerOp[Type, P, Type]) => Type
  )(implicit pp: PathProvider[P]): Expr = {
    transformerWithPC[P](path, exprOp, typeOp).transform(e, path)
  }

  def transformWithOps(e: Expr)(
    exprOp: (Expr, Path, TransformerOp[Expr, Path, Expr]) => Expr,
    typeOp: (Type, Path, TransformerOp[Type, Path, Type]) => Type
  ): Expr = transformWithOps(e, Path.empty)(exprOp, typeOp)

  def transformWithPC[P <: PathLike[P]](e: Expr, path: P, inTypes: Boolean)(
    exprOp: (Expr, P, TransformerOp[Expr, P, Expr]) => Expr
  )(implicit pp: PathProvider[P]): Expr = {
    val typeOp: (Type, P, TransformerOp[Type, P, Type]) => Type =
      if (inTypes) (tpe: Type, env: P, op: TransformerOp[Type, P, Type]) => op.sup(tpe, env)
      else (tpe: Type, env: P, op: TransformerOp[Type, P, Type]) => tpe
    transformerWithPC[P](path, exprOp, typeOp).transform(e, path)
  }

  def transformWithPC[P <: PathLike[P]](e: Expr, path: P)(
    exprOp: (Expr, P, TransformerOp[Expr, P, Expr]) => Expr
  )(implicit pp: PathProvider[P]): Expr = {
    transformWithPC(e, path, false)(exprOp)
  }

  def transformWithPC(e: Expr, inTypes: Boolean)(
    exprOp: (Expr, Path, TransformerOp[Expr, Path, Expr]) => Expr
  ): Expr = transformWithPC(e, Path.empty, inTypes)(exprOp)

  def transformWithPC(e: Expr)(
    exprOp: (Expr, Path, TransformerOp[Expr, Path, Expr]) => Expr
  ): Expr = transformWithPC(e, false)(exprOp)


  def collectWithPC[P <: PathLike[P], T](e: Expr, path: P, inTypes: Boolean)
                                        (pf: PartialFunction[(Expr, P), T])
                                        (implicit pp: PathProvider[P]): Seq[T] = {
    var results: Seq[T] = Nil
    var pfLift = pf.lift
    transformWithPC(e, path, inTypes) { (e, path, op) =>
      results ++= pfLift(e, path)
      op.sup(e, path)
    }
    results
  }

  def collectWithPC[P <: PathLike[P], T](e: Expr, path: P)
                                        (pf: PartialFunction[(Expr, P), T])
                                        (implicit pp: PathProvider[P]): Seq[T] = collectWithPC(e, path, false)(pf)

  def collectWithPC[T](e: Expr, inTypes: Boolean)(pf: PartialFunction[(Expr, Path), T]): Seq[T] =
    collectWithPC(e, Path.empty, inTypes)(pf)

  def collectWithPC[T](e: Expr)(pf: PartialFunction[(Expr, Path), T]): Seq[T] = collectWithPC(e, false)(pf)


  def existsWithPC[P <: PathLike[P]](e: Expr, path: P, inTypes: Boolean)
                                    (p: (Expr, P) => Boolean)
                                    (implicit pp: PathProvider[P]): Boolean = {
    var result = false
    transformWithPC(e, path, inTypes) { (e, path, op) =>
      if (result || p(e, path)) {
        result = true
        e
      } else {
        op.sup(e, path)
      }
    }
    result
  }

  def existsWithPC[P <: PathLike[P]](e: Expr, path: P)
                                    (p: (Expr, P) => Boolean)
                                    (implicit pp: PathProvider[P]): Boolean = existsWithPC(e, path, false)(p)

  def existsWithPC(e: Expr, inTypes: Boolean)(p: (Expr, Path) => Boolean): Boolean =
    existsWithPC(e, Path.empty, inTypes)(p)

  def existsWithPC(e: Expr)(p: (Expr, Path) => Boolean): Boolean = existsWithPC(e, false)(p)


  /** Replace each node by its constructor
    *
    * Remap the expression by calling the corresponding constructor
    * for each node of the expression. The constructor will perfom
    * some local simplifications, resulting in a simplified expression.
    */
  def simplifyByConstructors(expr: Expr): Expr = {
    def step(e: Expr): Option[Expr] = e match {
      case Not(t) => Some(not(t))
      case UMinus(t) => Some(uminus(t))
      case ADTSelector(e, sel) => Some(adtSelector(e, sel))
      case IsConstructor(e, id) => Some(isCons(e, id))
      case Equals(t1, t2) => Some(equality(t1, t2))
      case Implies(t1, t2) => Some(implies(t1, t2))
      case Plus(t1, t2) => Some(plus(t1, t2))
      case Minus(t1, t2) => Some(minus(t1, t2))
      case Times(t1, t2) => Some(times(t1, t2))
      case And(args) => Some(andJoin(args))
      case Or(args) => Some(orJoin(args))
      case Tuple(args) => Some(tupleWrap(args))
      case Application(e, es) => Some(application(e, es))
      case IfExpr(c, t, e) => Some(ifExpr(c, t, e))
      case _ => None
    }
    postMap(step)(expr)
  }

  /** Returns 'true' iff the evaluation of expression `expr` cannot lead to a crash. */
  def isPure(expr: Expr)(implicit opts: PurityOptions): Boolean = isPureIn(expr, Path.empty)

  def isAlwaysPure(expr: Expr) = isPure(expr)(PurityOptions.unchecked)

  /** Returns 'true' iff the evaluation of expression `expr` cannot lead to a crash under the provided path. */
  def isPureIn(e: Expr, path: Path)(implicit opts: PurityOptions): Boolean = {
    val s = simplifier
    val env = path.elements.foldLeft(s.initEnv) {
      case (env, Path.CloseBound(vd, e)) => env withBinding (vd -> e)
      case (env, Path.OpenBound(vd)) => env withBound vd
      case (env, Path.Condition(cond)) => env withCond cond
    }

    (env implies BooleanLiteral(false)) || s.isPure(e, env)
  }

  def isImpureExpr(expr: Expr): Boolean = expr match {
    case Assume(BooleanLiteral(true), _) => false
    case Choose(res, BooleanLiteral(true)) if hasInstance(res.tpe) == Some(true) => false
    case (_: Assume) | (_: Choose) | (_: Application) |
         (_: Division) | (_: Remainder) | (_: Modulo) | (_: ADTSelector) => true
    case adt: ADT => adt.getConstructor.sort.definition.hasInvariant
    case _ => false
  }

  /** Simplify all the pure and ground sub-expressions of the given expression,
    * by evaluating them using [[inox.evaluators.Evaluator]].
    * If `force` is omitted, the given expression will only be evaluated if it is
    * ground, pure, and does not contain choose or quantifiers.
    */
  def simplifyGround(expr: Expr, reportErrors: Boolean = false)(implicit sem: symbols.Semantics, ctx: Context): Expr = {
    val evalCtx = ctx.withOpts(evaluators.optEvalQuantifiers(false))
    val evaluator = sem.getEvaluator(evalCtx)

    case class SimplifyGroundError(expr: Expr, result: Result[Expr]) {
      def errMsg: String = result match {
        case RuntimeError(msg) =>
          s"runtime error: $msg"
        case EvaluatorError(msg) =>
          s"evaluator error: $msg"
        case _ => ""
      }
      override def toString: String = {
        s"Forced evaluation of expression @ ${expr.getPos} failed because of a $errMsg"
      }
    }

    def evalChildren(e: Expr)(implicit opts: PurityOptions): Expr = e match {
      case Operator(es, recons) => recons(es.map(rec))
    }

    // TODO: Should we run this within a fixpoint with simplifyByConstructor?
    def rec(e: Expr)(implicit opts: PurityOptions): Expr = e match {
      case e if isValue(e) =>
        e
      case e if isGround(e) && isPure(e) =>
        val evaluated = evaluator.eval(e)
        evaluated.result.map(exprOps.freshenLocals(_)).getOrElse {
          if (reportErrors) ctx.reporter.error(SimplifyGroundError(e, evaluated))
          evalChildren(e)
        }
      case l: Lambda =>
        evalChildren(l)(PurityOptions.unchecked)
      case e =>
        evalChildren(e)
    }

    rec(expr)(PurityOptions(ctx))
  }

  /** Normalizes identifiers in an expression to enable some notion of structural
    * equality between expressions on which usual equality doesn't make sense
    * (i.e. closures).
    *
    * This function relies on the static map `identifiers` to ensure identical
    * structures.
    *
    * @param args The "arguments" (free variables) of `expr`
    * @param expr The expression to be normalized
    * @param preserveApps Determines whether E-matching patterns should be preserved
    *                     during normalization (useful for normalizing foralls)
    * @param onlySimple Determines whether non-simple expressions (see
    *                   [[ExprOps.isSimple isSimple]]) should be normalized into a
    *                   dependency or recursed into (when they don't depend on `args`).
    *                   This distinction is used to provide general equality checks
    *                   between functions even when they have complex closures.
    * @param inFunction Determines whether normalization is called on a function. If
    *                   not, then normalization can normalize impure expressions when
    *                   the path-condition is empty.
    */
  def normalizeStructure(
    args: Seq[ValDef],
    expr: Expr,
    preserveApps: Boolean,
    onlySimple: Boolean,
    inFunction: Boolean
  )(implicit opts: PurityOptions): (Seq[ValDef], Expr, Seq[(Variable, Expr, Seq[Expr])]) = {

    val subst: MutableMap[Variable, (Expr, Seq[Expr])] = MutableMap.empty
    val varSubst: MutableMap[Variable, Variable] = MutableMap.empty
    val locals: MutableSet[Variable] = MutableSet.empty

    var counter: Int = 0
    def getVariable(e: Expr, tpe: Type, conditions: Seq[Expr] = Seq(), store: Boolean = true): Variable = {
      //val tpe = e.getType
      val newId = SymbolOps.getId(counter)
      counter += 1
      if (store) subst(Variable(newId, tpe, Seq())) = (e, conditions)
      Variable(newId, tpe, Seq())
    }

    def transformVar(v: Variable): Variable = subst.get(v) match {
      case Some((newV: Variable, _)) => newV
      case Some(_) => v
      case None => varSubst.get(v) match {
        case Some(newV) => newV
        case None =>
          val newV = getVariable(v, v.getType, store = false)
          locals += v
          varSubst += v -> newV
          newV
      }
    }

    object Matcher {
      def unapply(e: Expr): Option[Seq[Expr]] = e match {
        case Application(_, args) => Some(args)
        case ElementOfSet(elem, _) => Some(Seq(elem))
        case MultiplicityInBag(elem, _) => Some(Seq(elem))
        case MapApply(_, key) => Some(Seq(key))
        case FunctionInvocation(_, _, args) => Some(args)
        case _ => None
      }
    }

    def transformVal(vars: Set[Variable], vd: ValDef, inFunction: Boolean, path: Path): ValDef = {
      varSubst.getOrElse(vd.toVariable, {
        val newType = transformType(vars, vd.tpe, inFunction, path)
        val newV = getVariable(vd.toVariable, newType, store = false)
        locals += vd.toVariable
        varSubst += vd.toVariable -> newV
        newV
      }).toVal
    }

    def transformType(vars: Set[Variable], tpe: Type, inFunction: Boolean, path: Path): Type = {
      val tvars = vars map transformVar

      def rec(tpe: Type): Type = tpe match {
        case RefinementType(vd, pred) =>
          val newVd = transformVal(vars, vd, inFunction, path)
          val newPred = transformExpr(vars + vd.toVariable, pred, inFunction, path)
          RefinementType(newVd, newPred)
        case SigmaType(params, to) =>
          val toVars = typeOps.variablesOf(to)
          val newParams = params.map { vd =>
            if (toVars(vd.toVariable)) transformVal(vars, vd, inFunction, path)
            else transformVar(vd.toVariable).toVal
          }
          val newTo = transformType(vars ++ params.map(_.toVariable), to, inFunction, path)
          SigmaType(newParams, newTo)
        case PiType(params, to) =>
          val newTo = transformType(vars ++ params.map(_.toVariable), to, true, path)
          PiType(params map (vd => transformVar(vd.toVariable).toVal), newTo)
        case NAryType(tps, recons) =>
          recons(tps.map(rec))
      }

      rec(tpe)
    }

    def transformExpr(vars: Set[Variable], body: Expr, inFunction: Boolean, path: Path): Expr = {
      // this registers the argument images into subst
      val tvars = vars map transformVar

      def isLocal(e: Expr, path: Path, unconditional: Boolean): Boolean = {
        val vs = variablesOf(e)
        val tvs = vs flatMap { v => varSubst.get(v) }
        val pathVars = path.bound.map(_.toVariable).toSet

        (tvars & tvs).isEmpty && (if (unconditional) {
          // we will have `e` is always pure in this case
          (tvs & path.bound.map(_.toVariable).toSet).isEmpty
        } else {
          // we will have `e` pure in `path`
          val pathVars = path.bound.map(_.toVariable).toSet ++ path.conditions.flatMap(variablesOf)
          (tvs & pathVars).isEmpty
        })
      }

      def containsChoose(e: Expr): Boolean =
        exists { case c: Choose => true case _ => false } (e)

      def containsRecursive(e: Expr): Boolean =
        exists { case fi: FunctionInvocation => fi.tfd.fd.isRecursive case _ => false } (e)

      class Liftable(path: Path) {
        def unapply(e: Expr): Option[Seq[Expr]] = {
          // The set of minimal conditions that must be met for an expression to be liftable
          val minimal = 
            (isSimple(e) || !onlySimple)           && // check whether we want only simple expression
            !containsChoose(e)                     && // expressions containing chooses can't be lifted
            (!inFunction || !containsRecursive(e))    // recursive functions can't be lifted from lambdas

          // Whether the expression is guaranteed to be called, typically in foralls
          val isCalled = !inFunction && args.forall(vd => hasInstance(vd.tpe) contains true)

          if (!minimal) None
          else if (isLocal(e, path, true) && isAlwaysPure(e)) Some(Seq())
          else if (isLocal(e, path, false) && (isPureIn(e, path) || isCalled)) Some(path.conditions)
          else None
        }
      }

      // We use `recCounts` to check that we aren't in the outer-most call to `transformWithPC`.
      // This is necessary to avoid lifting a lambda's body into a new lambda with the exact same body
      // (so only sub-expressions of `body` can be lifted into lambdas).
      //
      // @nv: this is a super ugly hack. If someone has a better way of checking this (while still
      //      using `transformWithPC`), please change this horror!
      var recCounts: Int = 0
      transformWithOps(body, path)(
        (e, env, op) => {
          // the first call increases `recCounts` to 1 so `recCounts == 1` iff we're in the first call
          // We use an upper-bound of 2 to avoid integer overflow (although this will probably never happen).
          if (recCounts < 2) recCounts += 1

          val liftable = new Liftable(env)

          e match {
            case v: Variable =>
              if (vars(v) || locals(v)) transformVar(v)
              else getVariable(v, v.getType)

            case Matcher(args) if (
              args.exists { case v: Variable => vars(v) case _ => false } &&
              preserveApps
            ) =>
              val Operator(es, recons) = e
              recons(es.map(op(_, env)))

            case Let(vd, e @ liftable(conditions), b) =>
              subst(vd.toVariable) = (e, conditions)
              op(b, env)

            case expr @ liftable(conditions) =>
              getVariable(expr, expr.getType, conditions = conditions)

            case f: Forall =>
              val isInstantiated = f.params.forall(vd => hasInstance(vd.tpe) == Some(true))
              val newParams = f.params.map(vd => transformVal(vars, vd, inFunction, path))
              val newBody = transformExpr(vars ++ f.params.map(_.toVariable), f.body, !isInstantiated, env)
              Forall(newParams, newBody)

            case l: Lambda =>
              val newBody = transformExpr(vars ++ l.params.map(_.toVariable), l.body, true, env)
              Lambda(l.params map (vd => transformVar(vd.toVariable).toVal), newBody)

            // @nv: we make sure NOT to normalize choose ids as we may need to
            //      report models for unnormalized chooses!
            case c: Choose =>
              replaceFromSymbols(variablesOf(c).map(v => v -> {
                if (vars(v) || locals(v)) transformVar(v)
                else getVariable(v, v.getType)
              }).toMap, c)

            // Make sure we don't lift applications to applications when they have basic shapes
            case Application(liftable(_), args) if args.forall(liftable.unapply(_).isEmpty) =>
              op.sup(e, env)

            // This case enables lifting of impure expressions into lambdas outside of the expression
            // to normalize to improve normalized structure equality in the presence of impurity.
            // For example:
            //   (v: Int) => 1 + someImpureFunction(v)
            // and
            //   val f = (x: Int) => someImpureFunction(x)
            //   (v: Int) => 1 + f(v)
            // will have the same normalized structure thanks to this case.
            case Operator(es, recons) if (
              // We first make sure not to introduce new matchers in foralls
              (!preserveApps || !es.exists { case v: Variable => vars(v) case _ => false }) &&
              // Make sure we don't try to normalize outer-most expressions
              // See above about how/why `recCount` is used.
              recCounts > 1 &&
              // Don't lift pure conditions as recursive normalizations will be better
              isImpureExpr(e) &&
              es.exists(liftable.unapply(_).nonEmpty) &&
              es.exists(liftable.unapply(_).isEmpty)
            ) =>
              val conditions = es.collectFirst {
                case liftable(conditions) if conditions.nonEmpty => conditions
              }.getOrElse(Seq())

              val esWithParams = es.map(e => e -> (e match {
                case liftable(_) => None
                case e => Some(ValDef.fresh("v", e.getType))
              }))

              val params = esWithParams.collect { case (_, Some(vd)) => vd }
              val lambda = Lambda(params, recons(esWithParams.map {
                case (_, Some(vd)) => vd.toVariable
                case (e, _) => e
              }))

              Application(
                getVariable(lambda, lambda.getType, conditions = conditions),
                esWithParams.collect { case (e, Some(_)) => e }.map(op(_, env))
              )

            case _ =>
              val (ids, vs, es, tps, flags, recons) = deconstructor.deconstruct(e)
              val newVs = vs map transformVar
              op.sup(recons(ids, newVs, es, tps, flags), env)
          }
        },
        (tpe, env, op) => transformType(vars, tpe, inFunction, env)
      )
    }

    val newExpr = transformExpr(args.map(_.toVariable).toSet, expr, inFunction, Path.empty)
    val bindings = args map (vd => transformVar(vd.toVariable).toVal)

    // Reorder the dependencies to make sure inter-dependencies are satisfied
    val deps: Seq[(Variable, Expr, Seq[Expr])] = {
      def rec(v: Variable): Seq[Variable] = {
        val (expr, conds) = subst(v)
        val vars = variablesOf(expr) ++ conds.flatMap(variablesOf)
        (vars & subst.keySet - v).toSeq.flatMap(rec) :+ v
      }

      subst.keys.toSeq.flatMap(rec).distinct.map { v =>
        val (expr, conds) = subst(v)
        (v, expr, conds)
      }
    }

    (bindings, newExpr, deps)
  }

  /** Wrapper around
    * [[normalizeStructure(args:Seq[SymbolOps\.this\.trees\.ValDef],expr:SymbolOps\.this\.trees\.Expr,preserveApps:Boolean,onlySimple:Boolean,inFunction:Boolean)* normalizeStructure]]
    * that is tailored for structural equality of [[Expressions.Lambda Lambda]] and [[Expressions.Forall Forall]] instances.
    */
  def normalizeStructure(e: Expr, onlySimple: Boolean = false)
                        (implicit opts: PurityOptions): (Expr, Seq[(Variable, Expr, Seq[Expr])]) = freshenLocals(e) match {
    case lambda: Lambda =>
      val (args, body, subst) = normalizeStructure(lambda.params, lambda.body, false, onlySimple, true)
      (Lambda(args, body), subst)

    case forall: Forall =>
      val isInstantiated = forall.params.forall(vd => hasInstance(vd.tpe) == Some(true))
      val (args, body, subst) = normalizeStructure(forall.params, forall.body, true, onlySimple, !isInstantiated)
      (Forall(args, body), subst)

    case _ =>
      val (_, body, subst) = normalizeStructure(Seq(), e, false, onlySimple, false)
      (body, subst)
  }

  /** Ensures the closure `res` can only be equal to some other closure if they share the same
    * integer identifier `id`. This method makes sure this property is preserved after going through
    * [[normalizeStructure(e:SymbolOps\.this\.trees\.Expr,onlySimple:Boolean)*]]. */
  def uniquateClosure(id: Int, res: Lambda)(implicit opts: PurityOptions): Lambda = {
    def allArgs(l: Lambda): Seq[ValDef] = l.params ++ (l.body match {
      case l2: Lambda => allArgs(l2)
      case _ => Seq.empty
    })

    val resArgs = allArgs(res)
    val unique = if (resArgs.isEmpty) res else {
      /* @nv: This is a hack to ensure that the notion of equality we define on closures
       *      is respected by those returned by the model. */
      Lambda(res.params, Let(
        ValDef.fresh("id", tupleTypeWrap(List.fill(id)(resArgs.head.getType))),
        tupleWrap(List.fill(id)(resArgs.head.toVariable)),
        res.body
      ))
    }

    val (nl, subst) = normalizeStructure(unique)
    replaceFromSymbols(subst.map { case (v, e, _) => v -> e }.toMap, nl).asInstanceOf[Lambda]
  }

  /** Generates an instance of type `tpe` such that the following holds:
    * {{{constructExpr(i, tpe) == constructExpr(j, tpe)}}} iff {{{i == j}}}.
    */
  def constructExpr(i: Int, tpe: Type): Expr = tpe match {
    case _ if typeCardinality(tpe).exists(_ <= i) =>
      throw FatalError(s"Cardinality ${typeCardinality(tpe)} of type $tpe too high for index $i")
    case BooleanType() => BooleanLiteral(i == 0)
    case IntegerType() => IntegerLiteral(i)
    case BVType(signed, size) => BVLiteral(signed, i, size)
    case CharType() => CharLiteral(i.toChar)
    case RealType() => FractionLiteral(i, 1)
    case UnitType() => UnitLiteral()
    case tp: TypeParameter => GenericValue(tp, i)
    case TupleType(tps) =>
      val (0, args) = tps.foldLeft((i, Seq[Expr]())) {
        case ((i, args), tpe) => typeCardinality(tpe) match {
          case Some(card) =>
            val fieldCard = i min card
            val arg = constructExpr(fieldCard, tpe)
            (i - fieldCard, args :+ arg)

          case None =>
            val arg = constructExpr(i, tpe)
            (0, args :+ arg)
        }
      }
      Tuple(args)

    case adt: ADTType =>
      val sort = adt.getSort
      def rec(i: Int, conss: Seq[TypedADTConstructor]): (Int, TypedADTConstructor) = {
        val cons +: rest = conss
        constructorCardinality(cons) match {
          case None => i -> cons
          case Some(card) if card > i => i -> cons
          case Some(card) => rec(i - card, rest)
        }
      }

      val (ni, cons) = rec(i, sort.constructors.sortBy(constructorCardinality(_).getOrElse(Int.MaxValue)))
      ADT(cons.id, cons.tps, {
        if (cons.fields.isEmpty) Seq()
        else unwrapTuple(constructExpr(i, tupleTypeWrap(cons.fields.map(_.getType))), cons.fields.size)
      })

    case SetType(base) => typeCardinality(base) match {
      case None => FiniteSet(Seq(constructExpr(i, base)), base)
      case Some(card) if card > i => FiniteSet(Seq(constructExpr(i, base)), base)
      case Some(card) =>
        def rec(i: Int, c: Int): Seq[Expr] = {
          val elem = if (i % 2 == 0) None else Some(constructExpr(c, base))
          elem.toSeq ++ rec(i / 2, c + 1)
        }
        FiniteSet(rec(i, 0), base)
    }

    case MapType(from, to) => (typeCardinality(from), typeCardinality(to)) match {
      case (_, Some(1)) =>
        FiniteMap(Seq.empty, constructExpr(0, to), from, to)
      case (Some(x), _) if x <= 1 =>
        FiniteMap(Seq.empty, constructExpr(i, to), from, to)
      case (_, None) =>
        FiniteMap(Seq.empty, constructExpr(i, to), from, to)
      case (None, _) =>
        FiniteMap(Seq(constructExpr(i, from) -> constructExpr(1, to)), constructExpr(0, to), from, to)
      case (Some(i1), Some(i2)) =>
        val dfltIndex = i % i2
        val default = constructExpr(dfltIndex, to)
        def rec(i: Int, c: Int): Seq[(Expr, Expr)] = {
          val elem = if (i % i2 == 0) None else {
            val mod = (i % i2) - 1
            val index = if (mod == dfltIndex) i2 - 1 else mod
            Some(constructExpr(c, from) -> constructExpr(index, to))
          }
          elem.toSeq ++ rec(i / i2, c + 1)
        }
        FiniteMap(rec(i, 0), default, from, to)
    }

    case BagType(base) => if (i == 0) FiniteBag(Seq.empty, base) else {
      val key = constructExpr(0, base)
      FiniteBag(Seq(key -> IntegerLiteral(i)), base)
    }

    case FunctionType(Seq(), to) =>
      Lambda(Seq.empty, constructExpr(i, to))

    case FunctionType(from, to) =>
      val l = Lambda(from.map(tpe => ValDef.fresh("x", tpe, true)), constructExpr(0, to))
      uniquateClosure(i, l)(PurityOptions.unchecked)
  }

  /* Inline lambda lets that appear in forall bodies. For example,
   * {{{
   *   val f = (x: BigInt) => x + 1
   *   forall((x: BigInt) => f(x) == x + 1)
   * }}}
   * will be rewritten to
   * {{{
   *   val f = (x: BigInt) => x + 1
   *   forall((x: BigInt) => x + 1 == x + 1)
   * }}}
   */
  def inlineLambdas(e: Expr)(implicit opts: PurityOptions): Expr = {
    def rec(e: Expr, lambdas: Map[Variable, Lambda], inForall: Boolean): Expr = e match {
      case Let(vd, l: Lambda, b) =>
        val nl = l.copy(body = rec(l.body, lambdas, false))
        Let(vd, nl, rec(b, lambdas + (vd.toVariable -> nl), inForall))
      case Application(v: Variable, args) if (lambdas contains v) && inForall =>
        application(lambdas(v), args.map(rec(_, lambdas, inForall)))
      case Forall(args, body) =>
        Forall(args, rec(body, lambdas, true))
      case Operator(es, recons) =>
        recons(es.map(rec(_, lambdas, inForall)))
    }

    rec(e, Map.empty, false)
  }

  /** Pre-processing for solvers that handle universal quantification
    * in order to increase the precision of polarity analysis for
    * quantification instantiations.
    */
  def simplifyForalls(e: Expr)(implicit opts: PurityOptions): Expr = {

    def inlineFunctions(e: Expr): Expr = {
      import utils.Graphs._
      val initGraph = DiGraph[Identifier, SimpleEdge[Identifier]](functionCallsOf(e).map(_.id))

      val graph = fixpoint { graph: DiGraph[Identifier, SimpleEdge[Identifier]] =>
        var newGraph = graph
        for (id <- graph.N) {
          preTraversal {
            case fi: FunctionInvocation =>
              newGraph += SimpleEdge(id, fi.id)
            case Equals(IsTyped(e1, adt: ADTType), e2) if adt.getSort.hasEquality =>
              newGraph += SimpleEdge(id, adt.getSort.equality.get.id)
            case _ =>
          } (getFunction(id).fullBody)
        }
        newGraph
      } (initGraph)

      val toInline = graph.N.filter { id =>
        def rec(e: Expr): Boolean = e match {
          case _: Forall => true
          case Assume(pred, body) => rec(body)
          case Operator(es, _) => es.exists(rec)
        }

        !graph.transitiveSucc(id)(id) && rec(getFunction(id).fullBody)
      }

      def inline(e: Expr): Expr = postMap {
        case fi: FunctionInvocation if toInline(fi.id) =>
          Some(fi.inlined)
        case Equals(IsTyped(e1, adt: ADTType), e2)
        if adt.getSort.hasEquality && toInline(adt.getSort.equality.get.id) =>
          Some(adt.getSort.equality.get.applied(Seq(e1, e2)).inlined)
        case _ => None
      } (e)

      fixpoint(inline)(e)
    }

    def inlineForalls(e: Expr): Expr = postMap {
      case Forall(args, body) => Some(simpForall(args, body))
      case _ => None
    } (e)

    def inlinePosts(e: Expr): Expr = {
      def qArgs(quantified: Set[Variable], args: Seq[Expr]): Boolean = args.exists {
        case v: Variable => quantified(v)
        case _ => false
      }

      def inline(quantified: Set[Variable], e: Expr): Expr = andJoin(collectWithPC (e) {
        case (fi @ FunctionInvocation(_, _, args), path)
          if qArgs(quantified, args) &&
             !path.elements.exists(_.isInstanceOf[Path.OpenBound])
            =>
          val tfd = fi.tfd
          val nextQuantified = args.collect { case v: Variable if quantified(v) => v }.toSet
          tfd.withParamSubst(args, tfd.fullBody) match {
            case Let(res, _, Assume(pred, res2)) if res.toVariable == res2 && exists {
              case FunctionInvocation(_, _, args) => qArgs(quantified, args)
              case Application(_, args) => qArgs(quantified, args)
              case ElementOfSet(elem: Variable, set) => quantified(elem)
              case MultiplicityInBag(elem: Variable, set) => quantified(elem)
              case MapApply(elem: Variable, set) => quantified(elem)
              case _ => false
            } (pred) && !exists {
              case fi: FunctionInvocation => transitivelyCalls(fi.id, tfd.id)
              case _ => false
            } (pred) =>
              Seq[Expr](
                path implies replaceFromSymbols(Map(res.toVariable -> fi), and(pred, inline(nextQuantified, pred)))
              )
            case _ => Seq.empty[Expr]
          }
        case _ => Seq.empty[Expr]
      }.flatten)

      postMap {
        case f @ Forall(args, body) =>
          Some(assume(
            freshenLocals(forall(args, inline(args.map(_.toVariable).toSet, body))),
            f
          ))
        case _ => None
      } (e)
    }

    /* Weaker variant of conjunctive normal form */
    def normalizeClauses(e: Expr): Expr = e match {
      case Not(Not(e)) => normalizeClauses(e)
      case Not(Or(es)) => andJoin(es.map(e => normalizeClauses(Not(e))))
      case Not(Implies(e1, e2)) => and(normalizeClauses(e1), normalizeClauses(Not(e2)))
      case And(es) => andJoin(es map normalizeClauses)
      case _ => e
    }

    def simplifyMatchers(e: Expr): Expr = postMap {
      case f @ FiniteSet(elems, base) if elems.nonEmpty =>
        Some(elems.foldLeft(FiniteSet(Seq.empty, base).copiedFrom(f): Expr)(SetAdd(_,_).copiedFrom(f)))
      case f @ FiniteBag(pairs :+ (pair @ (key, _)), base) if pairs.nonEmpty =>
        Some(pairs.foldRight((FiniteBag(Seq(pair), base).copiedFrom(f): Expr, Seq(key))) {
          case (pair @ (key, _), (bag, elems)) => (ifExpr(
            orJoin(elems.map(e => Equals(e, key).copiedFrom(f))).copiedFrom(f),
            bag,
            BagUnion(bag, FiniteBag(Seq(pair), base).copiedFrom(f)).copiedFrom(f)
          ).copiedFrom(f), key +: elems)
        }._1)
      case f @ FiniteMap(pairs, dflt, from, to) if pairs.nonEmpty =>
        Some(pairs.foldLeft(FiniteMap(Seq.empty, dflt, from, to).copiedFrom(f): Expr) {
          (map, pair) => MapUpdated(map, pair._1, pair._2).copiedFrom(f)
        })
      case _ => None
    } (e)

    val simp: Expr => Expr =
      ((e: Expr) => normalizeClauses(e))    compose
      ((e: Expr) => simplifyMatchers(e))    compose
      ((e: Expr) => simplifyAssumptions(e)) compose
      ((e: Expr) => inlineLambdas(e))       compose
      ((e: Expr) => inlinePosts(e))         compose
      ((e: Expr) => inlineForalls(e))       compose
      ((e: Expr) => inlineFunctions(e))
    simp(e)
  }

  def simplifyLets(expr: Expr): Expr = preMap {
    case l1 @ Let(v1, Let(v2, e2, b2), b1) => Some(Let(v2, e2, Let(v1, b2, b1).copiedFrom(l1)).copiedFrom(l1))

    case Let(v, e, v2) if v.toVariable == v2 => Some(e)

    case Let(v, ts @ (
      (_: Variable)                |
      TupleSelect(_: Variable, _)  |
      ADTSelector(_: Variable, _)  |
      FiniteMap(Seq(), _, _, _)    |
      FiniteBag(Seq(), _)          |
      FiniteSet(Seq(), _)          |
      IsConstructor(_: Variable, _)
    ), b) => Some(replaceFromSymbols(Map(v -> ts), b))

    case _ => None
  } (expr)

  /** Fully expands all let expressions. */
  def expandLets(expr: Expr): Expr = {
    def rec(ex: Expr, s: Map[Variable,Expr]) : Expr = ex match {
      case v: Variable if s.isDefinedAt(v) => rec(s(v), s)
      case l @ Let(i,e,b) => rec(b, s + (i.toVariable -> rec(e, s)))
      case i @ IfExpr(t1,t2,t3) => IfExpr(rec(t1, s),rec(t2, s),rec(t3, s)).copiedFrom(i)
      case n @ Operator(args, recons) =>
        var change = false
        val rargs = args.map(a => {
          val ra = rec(a, s)
          if(ra != a) {
            change = true
            ra
          } else {
            a
          }
        })
        if(change)
          recons(rargs).copiedFrom(n)
        else
          n
      case unhandled => scala.sys.error("Unhandled case in expandLets: " + unhandled)
    }

    rec(expr, Map.empty)
  }

  /** Lifts lets to top level.
    *
    * Does not push any used variable out of scope.
    */
  def liftLets(e: Expr): Expr = {

    type C = Seq[(ValDef, Expr)]

    def combiner(e: Expr, defs: Seq[C]): C = (e, defs) match {
      case (Let(v, ex, b), Seq(inDef, inBody)) =>
        inDef ++ ((v, ex) +: inBody)
      case _ =>
        defs.flatten
    }

    def noLet(e: Expr, defs: C) = e match {
      case Let(_, _, b) => (b, defs)
      case _ => (e, defs)
    }

    val (bd, defs) = genericTransform[C](noTransformer, noLet, combiner)(Seq())(e)

    defs.foldRight(bd){ case ((vd, e), body) => Let(vd, e, body) }
  }

  protected def hasInstance(tpe: Type, seen: Set[Type]): Option[Boolean] = tpe match {
    case _: TypeParameter => None
    case MapType(_, to) => hasInstance(to, seen)
    case TupleType(tpes) => if (tpes.forall(tp => hasInstance(tp, seen) contains true)) Some(true) else None
    case SigmaType(params, to) =>
      if ((params.map(_.tpe) :+ to).forall(tp => hasInstance(tp, seen) contains true)) Some(true) else None
    case adt: ADTType =>
      val sort = adt.getSort
      if (seen(adt)) None
      else if (sort.hasInvariant) None
      else if (!sort.definition.isWellFormed) Some(false)
      else if (sort.constructors.sortBy(_.fields.size).exists(cons =>
                cons.fields.forall(vd => hasInstance(vd.tpe, seen + adt) contains true)))
        Some(true)
      else None
    case _: RefinementType => None
    case _ => Some(true)
  }

  final def hasInstance(tpe: Type): Option[Boolean] = hasInstance(tpe, Set())

  case class NoSimpleValue(tpe: Type) extends Exception(s"No simple value found for type $tpe")

  /** Returns simplest value of a given type */
  protected def simplestValue(tpe: Type, seen: Set[Type], allowSolver: Boolean, inLambda: Boolean)
                             (implicit sem: symbols.Semantics, ctx: Context): Expr = tpe match {
    case StringType()               => StringLiteral("")
    case BVType(signed, size)       => BVLiteral(signed, 0, size)
    case RealType()                 => FractionLiteral(0, 1)
    case IntegerType()              => IntegerLiteral(0)
    case CharType()                 => CharLiteral('a')
    case BooleanType()              => BooleanLiteral(false)
    case UnitType()                 => UnitLiteral()
    case SetType(baseType)          => FiniteSet(Seq(), baseType)
    case BagType(baseType)          => FiniteBag(Seq(), baseType)
    case MapType(fromType, toType)  => FiniteMap(Seq(), simplestValue(toType, seen, allowSolver, inLambda), fromType, toType)
    case TupleType(tpes)            => Tuple(tpes.map(simplestValue(_, seen, allowSolver, inLambda)))

    case adt @ ADTType(id, tps) =>
      val sort = adt.getSort
      if (!sort.definition.isWellFormed) throw NoSimpleValue(adt)

      if (seen(adt)) {
        if (inLambda) Choose(ValDef.fresh("res", adt), BooleanLiteral(true))
        else throw NoSimpleValue(adt)
      } else if (sort.hasInvariant) {
        if (!allowSolver) throw NoSimpleValue(adt)

        val p = Variable.fresh("p", FunctionType(Seq(adt), BooleanType()))
        val res = Variable.fresh("v", adt)

        import solvers._
        import SolverResponses._

        SimpleSolverAPI(sem.getSolver).solveSAT(Application(p, Seq(res))) match {
          case SatWithModel(model) => model.vars.get(res.toVal).getOrElse(throw NoSimpleValue(adt))
          case _ => throw NoSimpleValue(adt)
        }
      } else {
        for (cons <- sort.constructors.sortBy(_.fields.size)) {
          try {
            return ADT(
              cons.id,
              cons.tps,
              cons.fields.map(vd => simplestValue(vd.getType, seen + adt, allowSolver, inLambda))
            )
          } catch {
            case NoSimpleValue(_) => ()
          }
        }
        throw NoSimpleValue(adt)
      }

    case tp: TypeParameter =>
      GenericValue(tp, 0)

    case ft @ FunctionType(from, to) =>
      Lambda(from.map(tpe => ValDef.fresh("x", tpe, true)), simplestValue(to, seen, allowSolver, true))

    case _ => throw NoSimpleValue(tpe)
  }

  final def simplestValue(tpe: Type, allowSolver: Boolean = true)
                         (implicit sem: symbols.Semantics, ctx: Context): Expr = {
    simplestValue(tpe, Set.empty, allowSolver, false)
  }

  /** Hoists all IfExpr at top level.
    *
    * Guarantees that all IfExpr will be at the top level and as soon as you
    * encounter a non-IfExpr, then no more IfExpr can be found in the
    * sub-expressions
    *
    * Assumes no match expressions
    */
  def hoistIte(expr: Expr): Expr = {
    def transform(expr: Expr): Option[Expr] = expr match {
      case IfExpr(c, t, e) => None

      case nop @ Operator(ts, op) => {
        val iteIndex = ts.indexWhere{ case IfExpr(_, _, _) => true case _ => false }
        if(iteIndex == -1) None else {
          val (beforeIte, startIte) = ts.splitAt(iteIndex)
          val afterIte = startIte.tail
          val IfExpr(c, t, e) = startIte.head
          Some(IfExpr(c,
            op(beforeIte ++ Seq(t) ++ afterIte).copiedFrom(nop),
            op(beforeIte ++ Seq(e) ++ afterIte).copiedFrom(nop)
          ))
        }
      }
      case _ => None
    }

    postMap(transform, applyRec = true)(expr)
  }

  private[inox] def liftAssumptions(expr: Expr): (Seq[Expr], Expr) = {
    val vars = variablesOf(expr)
    var assumptions: Seq[Expr] = Seq.empty

    // Note that we avoid transforming types to make sure var/vals types match
    val newExpr = transformWithPC(expr, false)((e, env, op) => e match {
      case Assume(pred, body) if (
        ((env unboundOf pred) subsetOf vars) &&
        (env.conditions ++ env.bindings.map(_._2)).forall(isSimple)
      ) =>
        assumptions :+= freshenLocals(env implies pred)
        op(body, env withCond pred)
      case _ => op.sup(e, env)
    })

    (assumptions, newExpr)
  }

  private def simplifyAssumptions(expr: Expr): Expr = postMap {
    case Assume(pred, body) =>
      val (predAssumptions, newPred) = liftAssumptions(pred)
      val (bodyAssumptions, newBody) = liftAssumptions(body)
      Some(assume(andJoin(predAssumptions ++ (newPred +: bodyAssumptions)), newBody))
    case _ => None
  } (expr)

  private[inox] def simplifyFormula(e: Expr)(implicit ctx: Context, sem: symbols.Semantics): Expr = {
    implicit val simpOpts = SimplificationOptions(ctx)
    implicit val purityOpts = PurityOptions(ctx)

    if (simpOpts.simplify) {
      val simp: Expr => Expr =
        ((e: Expr) => simplifyGround(e))      compose
        ((e: Expr) => simplifyExpr(e))        compose
        ((e: Expr) => simplifyForalls(e))     compose
        ((e: Expr) => simplifyAssumptions(e))
      simp(e)
    } else {
      e
    }
  }

  // Use this only to debug isValueOfType
  private implicit class BooleanAdder(b: Boolean) {
    @inline def <(msg: => String) = {/*if(!b) println(msg); */b}
  }

  /** Returns true if expr is a value of type t */
  def isValueOfType(e: Expr, t: Type): Boolean = (e, t) match {
    case (StringLiteral(_), StringType()) => true
    case (BVLiteral(s1, _, s), BVType(s2, t)) => s1 == s2 && s == t
    case (IntegerLiteral(_), IntegerType()) => true
    case (CharLiteral(_), CharType()) => true
    case (FractionLiteral(_, _), RealType()) => true
    case (BooleanLiteral(_), BooleanType()) => true
    case (UnitLiteral(), UnitType()) => true
    case (GenericValue(t, _), tp) => t == tp
    case (Tuple(elems), TupleType(bases)) =>
      elems zip bases forall (eb => isValueOfType(eb._1, eb._2))
    case (FiniteSet(elems, tbase), SetType(base)) =>
      tbase == base &&
      (elems forall isValue)
    case (FiniteBag(elements, fbtpe), BagType(tpe)) =>
      fbtpe == tpe &&
      elements.forall{ case (key, value) => isValueOfType(key, tpe) && isValueOfType(value, IntegerType()) }
    case (FiniteMap(elems, default, kt, vt), MapType(from, to)) =>
      (kt == from) < s"$kt not equal to $from" && (vt == to) < s"${default.getType} not equal to $to" &&
      isValueOfType(default, to) < s"${default} not a value of type $to" &&
      (elems forall (kv => isValueOfType(kv._1, from) < s"${kv._1} not a value of type $from" && isValueOfType(kv._2, to) < s"${kv._2} not a value of type ${to}" ))
    case (adt @ ADT(id, tps, args), adt2: ADTType) =>
      isSubtypeOf(adt.getType, adt2) < s"$adt not a subtype of $adt2" &&
      ((args zip adt.getConstructor.fields.map(_.getType)) forall (argstyped => isValueOfType(argstyped._1, argstyped._2) < s"${argstyped._1} not a value of type ${argstyped._2}" ))
    case (Lambda(valdefs, body), FunctionType(ins, out)) =>
      variablesOf(e).isEmpty &&
      (valdefs zip ins forall (vdin => isSubtypeOf(vdin._2, vdin._1.getType) < s"${vdin._2} is not a subtype of ${vdin._1.getType}")) &&
      isSubtypeOf(body.getType, out) < s"${body.getType} is not a subtype of $out"
    case _ => false
  }

  /** Returns true if expr is a value. Stronger than isGround */
  def isValue(e: Expr) = isValueOfType(e, e.getType)

  /** Returns a nested string explaining why this expression is typed the way it is.*/
  def explainTyping(e: Expr)(implicit opts: PrinterOptions): String = {
    fold[String]{ (e, se) =>
      e match {
        case FunctionInvocation(id, tps, args) =>
          lookupFunction(id, tps) match {
            case Some(tfd) =>
              s"${e.asString} is of type ${e.getType.asString}" +
              se.map(child => "\n  " + "\n".r.replaceAllIn(child, "\n  ")).mkString +
              s" because ${tfd.fd.id.name} was instantiated with " +
              s"${tfd.fd.tparams.zip(tps).map(k => k._1.asString + ":=" + k._2.asString).mkString(",")} " +
              s"with type ${tfd.fd.params.map(_.getType.asString).mkString("(", ",", ")")} => " +
              s"${tfd.fd.getType.asString}"
            case None =>
              s"${e.asString} is of type ${e.getType.asString}" +
              se.map(child => "\n  " + "\n".r.replaceAllIn(child, "\n  ")).mkString +
              s" but couldn't find function $id"
          }
        case ADT(id, tps, args) =>
          lookupConstructor(id, tps) match {
            case Some(tcons) =>
              s"${e.asString} is of type ${e.getType.asString}" +
              se.map(child => "\n  " + "\n".r.replaceAllIn(child, "\n  ")).mkString +
              s" because ${tcons.id.name} was instantiated with " +
              s"${tcons.sort.definition.tparams.zip(tps).map(k => k._1.asString + ":=" + k._2.asString).mkString(",")} " +
              s"with fields ${tcons.fields.map(_.getType.asString).mkString("(", ",", ")")}"
            case None =>
              s"${e.asString} is of type ${e.getType.asString}" +
              se.map(child => "\n  " + "\n".r.replaceAllIn(child, "\n  ")).mkString +
              s" but couldn't find constructor $id"
          }
        case e =>
          s"${e.asString} is of type ${e.getType.asString}" +
          se.map(child => "\n  " + "\n".r.replaceAllIn(child, "\n  ")).mkString
      }
    }(e)
  }

  /* ===================================================
   *        Constructors that require Symbols
   * =================================================== */

  /** Simplifies the construct `TupleSelect(expr, index)`
    * @param originalSize The arity of the tuple. If less or equal to 1, the whole expression is returned.
    * @see [[Expressions.TupleSelect TupleSelect]]
    */
  def tupleSelect(t: Expr, index: Int, originalSize: Int): Expr = tupleSelect(t, index, originalSize > 1)

  /** If `isTuple`:
    * `tupleSelect(tupleWrap(Seq(Tuple(x,y))), 1) -> x`
    * `tupleSelect(tupleExpr,1) -> tupleExpr._1`
    * If not `isTuple` (usually used only in the case of a tuple of arity 1)
    * `tupleSelect(tupleWrap(Seq(Tuple(x,y))),1) -> Tuple(x,y)`.
    * @see [[Expressions.TupleSelect TupleSelect]]
    */
  def tupleSelect(t: Expr, index: Int, isTuple: Boolean): Expr = t match {
    case Tuple(es) if isTuple => es(index-1)
    case _ if t.getType.isInstanceOf[TupleType] && isTuple => TupleSelect(t, index)
    case other if !isTuple => other
    case _ =>
      sys.error(s"Calling tupleSelect on non-tuple $t")
  }

  /** $encodingof ``val id = e; vd``, and returns `bd` if the identifier is not bound in `bd` AND
    * the expression `e` is pure.
    * @see [[Expressions.Let Let]]
    * @see [[SymbolOps.isPure isPure]]
    */
  def let(vd: ValDef, e: Expr, bd: Expr) = {
    if ((variablesOf(bd) contains vd.toVariable) || !isAlwaysPure(e))
      Let(vd, e, bd).setPos(Position.between(vd.getPos, bd.getPos))
    else bd
  }

  /** $encodingof simplified `if (c) t else e` (if-expression).
    * @see [[Expressions.IfExpr IfExpr]]
    */
  def ifExpr(c: Expr, t: Expr, e: Expr): Expr = (t, e) match {
    case (_, `t`) if isAlwaysPure(c) => t
    case (IfExpr(c2, thenn, `e`), _) => ifExpr(and(c, c2), thenn, e)
    case (_, IfExpr(c2, `t`, e2)) => ifExpr(or(c, c2), t, e2)
    case (BooleanLiteral(true), BooleanLiteral(false)) => c
    case (BooleanLiteral(false), BooleanLiteral(true)) => not(c)
    case (BooleanLiteral(true), _) => or(c, e)
    case (_, BooleanLiteral(true)) => or(not(c), t)
    case (BooleanLiteral(false), _) => and(not(c), e)
    case (_, BooleanLiteral(false)) => and(c, t)
    case _ if c == BooleanLiteral(true) => t
    case _ if c == BooleanLiteral(false) => e
    case _ => IfExpr(c, t, e)
  }

  /** $encodingof simplified `fn(realArgs)` (function application).
   * Transforms
   * {{{ ((x: A, y: B) => g(x, y))(c, d) }}}
   * into
   * {{{
   *   val x0 = c
   *   val y0 = d
   *   g(x0, y0)
   * }}}
   * and further simplifies it.
   * @see [[Expressions.Lambda Lambda]]
   * @see [[Expressions.Application Application]]
   */
  def application(fn: Expr, realArgs: Seq[Expr]): Expr = fn match {
    case Lambda(formalArgs, body) =>
      assert(realArgs.size == formalArgs.size, "Invoking lambda with incorrect number of arguments")

      var defs: Seq[(ValDef, Expr)] = Seq()

      val subst = formalArgs.zip(realArgs).map {
        case (vd, to:Variable) =>
          vd -> to
        case (vd, e) =>
          val fresh = vd.freshen
          defs :+= (fresh -> e)
          vd -> fresh.toVariable
      }.toMap

      defs.foldRight(exprOps.replaceFromSymbols(subst, body)) {
        case ((vd, bd), body) => let(vd, bd, body)
      }

    case Assume(pred, l: Lambda) =>
      assume(pred, application(l, realArgs))

    case _ =>
      Application(fn, realArgs).copiedFrom(fn)
  }


  /** Simplifies the provided adt selector.
    * @see [[Expressions.ADTSelector ADTSelector]]
    */
  def adtSelector(adt: Expr, selector: Identifier): Expr = {
    adt match {
      case a @ ADT(id, tps, fields) =>
        val cons = a.getConstructor
        if (!cons.sort.hasInvariant && cons.fields.exists(_.id == selector) && fields.forall(isAlwaysPure)) {
          fields(cons.definition.selectorID2Index(selector))
        } else {
          ADTSelector(adt, selector).copiedFrom(adt)
        }
      case _ =>
        ADTSelector(adt, selector).copiedFrom(adt)
    }
  }

  /** $encodingof expr.isInstanceOf[tpe], simplifies to `true` or `false` in clear cases. */
  def isCons(expr: Expr, id: Identifier) = expr.getType match {
    case adt: ADTType if adt.getSort.constructors.size == 1 =>
      BooleanLiteral(true).copiedFrom(expr)
    case _ => IsConstructor(expr, id)
  }

  /** $encodingof simplified `forall(args, body)` (universal quantification).
   * @see [[Expressions.Forall Forall]]
   */
  def forall(args: Seq[ValDef], body: Expr): Expr = {
    if (body == BooleanLiteral(true)) BooleanLiteral(true)
    else if (args.isEmpty) body
    else {
      val vars = exprOps.variablesOf(body)
      val newArgs = args.filter(vd => vars(vd.toVariable) || hasInstance(vd.tpe) != Some(true))
      if (newArgs.size == args.size) Forall(args, body)
      else forall(newArgs, body)
    }
  }

  def simpForall(args: Seq[ValDef], body: Expr): Expr = {
    def liftForalls(es: Seq[Expr], recons: Seq[Expr] => Expr): Expr = {
      val (allArgs, allBodies) = es.map {
        case f: Forall =>
          val Forall(args, body) = exprOps.freshenLocals(f)
          (args, body)
        case e =>
          (Seq[ValDef](), e)
      }.unzip

      val flatArgs = allArgs.flatten
      if (flatArgs.isEmpty) {
        forall(args, recons(allBodies))
      } else {
        simpForall(args ++ flatArgs, recons(allBodies))
      }
    }

    body match {
      case Forall(args2, body) => simpForall(args ++ args2, body)
      case And(es) => liftForalls(es, andJoin)
      case Or(es) => liftForalls(es, orJoin)
      case Implies(l, r) => liftForalls(Seq(l, r), es => implies(es(0), es(1)))
      case _ => forall(args, body)
    }
  }
}
