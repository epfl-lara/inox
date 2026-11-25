/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package transformers

import utils._
import utils.CaseSplit.*

import scala.collection.mutable.{Map => MutableMap}

trait SimplifierWithPC extends Transformer { self =>
  val trees: ast.Trees
  val symbols: trees.Symbols
  val opts: solvers.PurityOptions

  given givenOpts: solvers.PurityOptions = opts

  // The only value that can be assigned to `s` and `t` is `trees`, but that has to be
  // done in a concrete class explicitly overriding `s` and `t`.
  // Otherwise, we can run into initialization issue.
  val s: trees.type
  val t: trees.type

  import trees.{given, _}
  import symbols.{given, _}
  import exprOps._
  import dsl._

  trait SolvingPath { selfP: Env =>
    def expand(expr: Expr): Expr = expr
    def implies(expr: Expr): Boolean

    // @nv: Scala's type system is unfortunately not powerful enough to express
    //      what we want here. The type should actually specify that the `that`
    //      parameter is the same type as this simplifier.
    // NOTE: we also rely on the fact that the SolvingPath instance doesn't refer
    //       to the outer simplifier here, otherwise the cast would lead to wrong
    //       simplifications!
    def in(that: SimplifierWithPC {
      val trees: self.trees.type
      val symbols: self.symbols.type
    }): that.Env = this.asInstanceOf[that.Env]
  }

  type Env <: PathLike[Env] & SolvingPath

  def initEnv: Env

  private val dynStack = new ThreadLocal[List[Int]] { override def initialValue = Nil }
  private val dynPurity = new ThreadLocal[List[Boolean]] { override def initialValue = Nil }

  private sealed abstract class PurityCheck
  private case object Pure extends PurityCheck
  private case object Impure extends PurityCheck
  private case object Checking extends PurityCheck

  private val pureCache: MutableMap[Identifier, PurityCheck] = MutableMap.empty

  protected final def isPureFunction(id: Identifier): Boolean = synchronized(pureCache.get(id) match {
    case Some(Pure) => true
    case Some(Impure) => false
    case Some(Checking) =>
      // Function is recursive and cycles were not pruned by the simplifier.
      // No need to update pureCache here as the update will take place in the next branch.
      opts.assumeChecked
    case None =>
      pureCache += id -> Checking
      val fndef = getFunction(id)
      val p = fndef.params.forall(vd => hasInstance(vd.tpe) == Some(true)) &&
        isPure(fndef.fullBody, initEnv.withBounds(fndef.params))
      pureCache += id -> (if (p) Pure else Impure)
      p
  })

  protected def isConstructor(e: Expr, id: Identifier, path: Env): Option[Boolean] = e match {
    case ADT(id2, _, _) => Some(id == id2)
    case _ => if (path `implies` IsConstructor(e, id)) {
      Some(true)
    } else if (path `implies` Not(IsConstructor(e, id))) {
      Some(false)
    } else {
      val adt @ ADTType(_, tps) = e.getType: @unchecked
      val sort = adt.getSort
      val cons = getConstructor(id, tps)
      val alts = (sort.constructors.toSet - cons).map(_.id)

      if (alts exists (id => path `implies` IsConstructor(e, id))) {
        Some(false)
      } else if (alts forall (id => path `implies` Not(IsConstructor(e, id)))) {
        Some(true)
      } else {
        None
      }
    }
  }

  // a purity check simplifies terms that are not the one whose simplification is recorded
  final def isPure(e: Expr, path: Env): Boolean = {
    val r = recorder
    if (r eq null) simplify(e, path)._2 else r.suspended(simplify(e, path)._2)
  }

  /** The recorder of the steps of the simplification, or `null` when it is not recorded (see
    * [[TransformationRecorder]]). */
  protected def recorder: TransformationRecorder { val trees: self.trees.type } = null

  /** Rewrites the subterm that the recorded simplification is at, if it is recorded. */
  protected inline def recorded(rule: String, inline to: Expr): Unit = {
    val r = recorder
    if (r ne null) r.rewrite(rule, to)
  }

  /** Runs `body`, which simplifies `e`, at `e` in the term of the recorded simplification. What
    * it makes of `e` without a step is one of `rule`, or of the pass around without one. */
  protected inline def recordedAt(e: Expr, rule: String = null)(inline body: Expr): Expr = {
    val r = recorder
    if (r eq null) body else r.at(e, rule)(body)
  }

  /** `res`, which the subterm that the recorded simplification is at becomes by the rule `rule`
    * of certificates, when the simplification is recorded (see [[TransformationRecorder]]). */
  private def step(rule: String, res: Expr): Expr = { recorded(rule, res); res }

  /** The term that the path binds `e` to, which `e` becomes where it is. */
  private def recordedExpand(e: Expr, path: Env): Expr = {
    val expanded = path `expand` e
    if (expanded ne e) recordedAt(e, "expand")(expanded) else e
  }

  /** Binds each of `bindings` around `inner`, the subterm that the recorded simplification is at,
    * from the outermost on, where `inner` then becomes `last`. */
  private def recordedBinds(bindings: Seq[(ValDef, Expr)], inner: Expr)(last: => Expr): Unit = {
    val r = recorder
    if (r ne null) {
      def rec(bs: Seq[(ValDef, Expr)]): Expr =
        if (bs.isEmpty) last
        else {
          r.rewrite("bind", Let(bs.head._1, bs.head._2, inner))
          r.at(inner)(rec(bs.tail))
        }
      rec(bindings)
    }
  }

  /** Simplifies `e` under `path`, and returns whether the result is pure.
    *
    * The cases are split into the `simplifyCore`, `simplifyData`, ... methods below, which are tried
    * in order (see [[utils.CaseSplit]]). Simplifiers can override `simplify` itself, or a single family.
    */
  protected def simplify(e: Expr, path: Env): (Expr, Boolean) = {
    val r = recorder
    if (r eq null) simplifyCases(e, path) else {
      // the recorded steps are from what the simplifier is given to what it returns
      var pure = false
      val res = r.at(e, "simplify") { val (re, pe) = simplifyCases(e, path); pure = pe; re }
      (res, pure)
    }
  }

  private def simplifyCases(e: Expr, path: Env): (Expr, Boolean) =
    simplifyCore(e, path) otherwise simplifyData(e, path) otherwise simplifyBindings(e, path) otherwise
      simplifyDefault(e, path)

  /** Simplifies the children of `e`. */
  protected def simplifyDefault(e: Expr, path: Env): (Expr, Boolean) = {
    dynStack.set(0 :: dynStack.get)
    val re = super.transform(e, path)
    val (rpure, rest) = dynPurity.get.splitAt(dynStack.get.head)
    val pe = rpure.foldLeft(opts.assumeChecked || !isImpureExpr(re))(_ && _)
    dynStack.set(dynStack.get.tail)
    dynPurity.set(rest)
    (re, pe)
  }

  /** Facts implied by the path, lambdas, boolean connectives and assumptions. */
  protected def simplifyCore(e: Expr, path: Env): (Expr, Boolean) = e match {
    // When the simplification is recorded, the steps on the connectives are of the `logic` rule
    // of certificates, under the conditions of the path, which are those of the term around.
    case e if path `implies` e =>
      (step("logic", BooleanLiteral(true).copiedFrom(e)), true)

    case e if path `implies` not(e) =>
      (step("logic", BooleanLiteral(false).copiedFrom(e)), true)

    case Lambda(params, body) =>
      val (rb, _) = simplify(body, path `withBounds` params)
      (Lambda(params, rb).copiedFrom(e), true)

    case Implies(l, r) => simplify(step("logic", Or(Not(l).copiedFrom(l), r).copiedFrom(e)), path)

    case a @ And(e +: es) =>
      val rest = andJoin(es).copiedFrom(a)
      recorded("logic", And(Seq(e, rest)))
      simplify(e, path) match {
        case (BooleanLiteral(true), true) => simplify(step("logic", rest), path)
        case (BooleanLiteral(false), true) =>
          (step("logic", BooleanLiteral(false).copiedFrom(a)), true)
        case (re, pe) =>
          val (res, pes) = simplify(rest, path `withCond` re)
          if (res == BooleanLiteral(false) && pe) {
            (step("logic", BooleanLiteral(false).copiedFrom(a)), true)
          } else {
            (step("logic", and(re, res)), pe && pes)
          }
      }

    case o @ Or(e +: es) =>
      val rest = orJoin(es).copiedFrom(o)
      recorded("logic", Or(Seq(e, rest)))
      simplify(e, path) match {
        case (BooleanLiteral(true), true) =>
          (step("logic", BooleanLiteral(true).copiedFrom(o)), true)
        case (BooleanLiteral(false), true) => simplify(step("logic", rest), path)
        case (re, pe) =>
          val (res, pes) = simplify(rest, path `withCond` Not(re).copiedFrom(re))
          if (res == BooleanLiteral(true) && pe) {
            (step("logic", BooleanLiteral(true).copiedFrom(o)), true)
          } else {
            (step("logic", or(re, res)), pe && pes)
          }
      }

    case ie @ IfExpr(c, t, e) => simplify(c, path) match {
      case (BooleanLiteral(true), true) => simplify(step("logic", t), path)
      case (BooleanLiteral(false), true) => simplify(step("logic", e), path)
      case (rc, pc) =>
        val (rt, pt) = simplify(t, path `withCond` rc)
        val (re, pe) = simplify(e, path `withCond` Not(rc).copiedFrom(rc))
        if (rt == re && pc) {
          (step("logic", rt), pt)
        } else {
          (step("logic", ifExpr(rc, rt, re)), pc && pt && pe)
        }
    }

    case Assume(pred, body) => simplify(pred, path) match {
      case (BooleanLiteral(true), true) => simplify(step("logic", body), path)
      case (BooleanLiteral(false), true) =>
        val (rb, _) = simplify(body, path)
        (Assume(BooleanLiteral(false).copiedFrom(pred), rb).copiedFrom(e), false)
      case (rp, _) =>
        val (rb, _) = simplify(body, path `withCond` rp)
        (Assume(rp, rb).copiedFrom(e), false)
    }

    case _ => unhandled
  }

  /** ADT and tuple constructors, testers and selectors. */
  protected def simplifyData(e: Expr, path: Env): (Expr, Boolean) = e match {
    case ic @ IsConstructor(e, id) =>
      val expanded = recordedExpand(e, path)
      val (re, pe) = simplify(expanded, path)
      isConstructor(re, id, path) match {
        case Some(b) if pe =>
          (step("logic", BooleanLiteral(b).copiedFrom(ic)), true)
        case Some(b) =>
          // the term is kept for its effects
          val vd = "e" :: re.getType
          val res = BooleanLiteral(b).copiedFrom(ic)
          recordedBinds(Seq(vd -> re), IsConstructor(re, id))(step("logic", res))
          (Let(vd, re, res).copiedFrom(ic), pe)
        case None => (IsConstructor(re, id).copiedFrom(ic), pe)
      }

    case s @ ADTSelector(e, sel) =>
      val expanded = recordedExpand(e, path)
      val (re, pe) = simplify(expanded, path)

      if (isConstructor(re, s.constructor.id, path) == Some(true)) {
        val cons = s.constructor
        val index = cons.definition.selectorID2Index(sel)
        re match {
          case ADT(_, _, es) if pe => (step("select", es(index)), true)

          // The other fields are kept for their effects, and so is the construction itself when it
          // checks an invariant, as it then fails on values that don't satisfy it
          case adt @ ADT(_, _, es) if !cons.sort.hasInvariant =>
            val value = es(index)
            val freshFields = cons.fields.map(_.freshen)
            val bindings = (freshFields zip es).filter(_._2 != value)
            recordedBinds(bindings, ADTSelector(re, sel))(step("select", value))
            simplify(bindings.foldRight(value) { case ((vd, e), b) => Let(vd, e, b).copiedFrom(s) }, path)

          case _ =>
            (ADTSelector(re, sel).copiedFrom(s), pe)
        }
      } else {
        (ADTSelector(re, sel).copiedFrom(s), opts.assumeChecked)
      }

    case adt @ ADT(id, tps, args) =>
      val (rargs, pargs) = args.map(simplify(_, path)).unzip
      val ls = (adt.getConstructor.fields zip rargs).collect {
        case (vd, ADTSelector(e, id)) if vd.id == id => e
      }

      val newAdt = ls match {
        case ls @ (e +: es) if (
          ls.size == rargs.size &&
          es.forall(_ == e) &&
          e.getType == adt.getType &&
          (isConstructor(e, id, path) contains true)) => step("eta", e)
        case _ => ADT(id, tps, rargs).copiedFrom(adt)
      }

      // Note that if `isConstructor(e, id, path)` holds for each ADTSelector argument
      // in rargs, then these selectors will be marked as pure by the simplifier so we
      // don't need to do any special recomputation of pargs
      (newAdt, pargs.foldLeft(opts.assumeChecked || !isImpureExpr(newAdt))(_ && _))

    case ts @ TupleSelect(e, i) =>
      val expanded = recordedExpand(e, path)
      simplify(expanded, path) match {
        case (Tuple(es), true) => (step("select", es(i - 1)), true)
        case (tuple @ Tuple(es), pe) =>
          // the other elements are kept for their effects
          val bindings = es.zipWithIndex.filter(_._2 != i - 1).map((e, _) => ("e" :: e.getType) -> e)
          recordedBinds(bindings, TupleSelect(tuple, i))(step("select", es(i - 1)))
          (bindings.foldRight(es(i - 1)) {
            case ((vd, e), b) => Let(vd, e, b).copiedFrom(ts)
          }, pe)
        case (re, pe) => (TupleSelect(re, i).copiedFrom(ts), pe)
      }

    case _ => unhandled
  }

  /** Lets, function calls, operators, tuples, quantifiers and applications. */
  protected def simplifyBindings(e: Expr, path: Env): (Expr, Boolean) = e match {
    // the `logic` rule of certificates knows what `let` binds
    case Let(vd, IfExpr(c1, t1, e1), IfExpr(c2, t2, e2)) if c1 == c2 =>
      simplify(step("logic", IfExpr(c1, Let(vd, t1, t2).copiedFrom(e), Let(vd, e1, e2).copiedFrom(e)).copiedFrom(e)), path)

    case Let(vd, v: Variable, b) => simplify(step("logic", replaceFromSymbols(Map(vd -> v), b)), path)

    case let @ Let(vd, e, b) =>
      val (re, pe) = simplify(e, path)
      val (rb, pb) = simplify(b, path `withBinding` (vd -> re))

      val v = vd.toVariable
      lazy val insts = count { case `v` => 1 case _ => 0 }(rb)
      lazy val inLambda = exists { case l: Lambda => variablesOf(l) contains v case _ => false }(rb)
      lazy val immediateCall = existsWithPC(rb) { case (`v`, path) => path.isEmpty case _ => false }
      lazy val containsLambda = exists { case l: Lambda => true case _ => false }(re)
      lazy val realPE = if (opts.assumeChecked) {
        val simp = simplifier(using solvers.PurityOptions.unchecked)
        simp.isPure(e, path `in` simp)
      } else {
        pe
      }
      lazy val isSimpleBdg = isSimpleBinding(re)

      if (
        (((!inLambda && pe) || (inLambda && realPE && !containsLambda)) && insts <= 1) ||
        (!inLambda && immediateCall && insts == 1) ||
        (((!inLambda && pe) || (inLambda && realPE)) && isSimpleBdg)
      ) {
        // We can assume here that all `important` simplifications have already taken place
        // as if the bound expression was an ADT or variable, then `path.expand` has already
        // made sure that all possible simplifications have taken place in `rb`.
        (step("logic", replaceFromSymbols(Map(vd -> re), rb)), pe && pb)
      } else {
        val newLet = Let(vd, re, rb).copiedFrom(let)
        re match {
          case l: Lambda =>
            val inlined = inlineLambdas(newLet, recorder)
            if (inlined != newLet) simplify(inlined, path)
            else (newLet, pe && pb)
          case _ => (newLet, pe && pb)
        }
      }

    case fi @ FunctionInvocation(id, tps, args) =>
      val (rargs, pargs) = args.map(simplify(_, path)).unzip
      (FunctionInvocation(id, tps, rargs).copiedFrom(fi), pargs.foldLeft(isPureFunction(id))(_ && _))

    // A call may only be dropped when its return type has values
    case uc @ UninterpretedCall(id, tps, args, tpe) =>
      val (rargs, pargs) = args.map(simplify(_, path)).unzip
      (UninterpretedCall(id, tps, rargs, tpe).copiedFrom(uc), pargs.foldLeft(hasInstance(uc.getTpe(stripRefinements = false)) == Some(true))(_ && _))

    // the constructors simplify the negation of a connective, and arithmetic on literals
    case n @ Not(e)   => recordedCons("logic", simplifyAndCons(Seq(e), path, es => not(es.head).copiedFrom(n)))
    case Equals(l, r) => recordedCons("arith", simplifyAndCons(Seq(l, r), path, es => equality(es(0), es(1)).copiedFrom(e)))
    case UMinus(t)    => recordedCons("arith", simplifyAndCons(Seq(t), path, es => uminus(es.head).copiedFrom(e)))
    case Plus(l, r)   => recordedCons("arith", simplifyAndCons(Seq(l, r), path, es => plus(es(0), es(1)).copiedFrom(e)))
    case Minus(l, r)  => recordedCons("arith", simplifyAndCons(Seq(l, r), path, es => minus(es(0), es(1)).copiedFrom(e)))
    case Times(l, r)  => recordedCons("arith", simplifyAndCons(Seq(l, r), path, es => times(es(0), es(1)).copiedFrom(e)))

    case Tuple(es)    =>
      // the elements are returned as they were given: their simplification is not recorded
      val r = recorder
      val (res, pes) = (if (r eq null) es.map(simplify(_, path)) else r.suspended(es.map(simplify(_, path)))).unzip
      val tuple = res.zipWithIndex.collect { case (TupleSelect(e, idx), i) if idx == i + 1 => e } match {
        case ls @ (x +: xs) if ls.size == es.size && xs.forall(_ == x) =>
          x.getType match {
            case TupleType(ts) if ts.size == es.size => x
            case _ => Tuple(es)
          }
        case _ => Tuple(es)
      }
      if (r ne null) r.rewrite("tuple", tuple)
      (tuple, pes.foldLeft(true)(_ && _))

    // `simpForall` records its steps
    case Forall(params, body) =>
      simplifyAndCons(Seq(body), path `withBounds` params, es => simpForall(params, es.head, recorder).copiedFrom(e))

    case app @ Application(e, es)  =>
      // an assumption on the caller becomes one on the application, which is then its body
      val (caller: Expr, recons: (Expr => Expr), lifted: Option[Expr]) = simplify(e, path) match {
        case (ra @ Assume(pred, e), _) =>
          val application = Application(e, es)
          recorded("lift", Assume(pred, application))
          (e, (expr: Expr) => assume(pred, expr).copiedFrom(ra), Some(application))
        case (e, _) => (e, (expr: Expr) => expr, None)
      }

      path.expand(caller) match {
        case (l: Lambda) =>
          // the caller is the lambda that the path binds it to, whose application binds its
          // parameters, which `application` then drops where it can
          def beta: Expr = {
            if (l ne caller) recordedAt(caller, "expand")(l)
            step("beta", symbols.applied(l, es))
          }
          lifted.fold(beta)(recordedAt(_)(beta))
          simplify(step("logic", recons(application(l, es))), path)
        case _ =>
          val (res, _) = es.map(simplify(_, path)).unzip
          (step("logic", recons(application(caller, res).copiedFrom(app))), opts.assumeChecked)
      }

    case _ => unhandled
  }

  private def simplifyAndCons(es: Seq[Expr], path: Env, cons: Seq[Expr] => Expr): (Expr, Boolean) = {
    val (res, pes) = es.map(simplify(_, path)).unzip
    val re = cons(res)
    val pe = pes.foldLeft(opts.assumeChecked || !isImpureExpr(re))(_ && _)
    (re, pe)
  }

  /** The result `res` of [[simplifyAndCons]], where what the constructor made of the term is a
    * step of the rule `rule` of certificates, when the simplification is recorded. The `arith`
    * rule is that of the integers, and of the equalities that it decides: the others are steps
    * of the rule `fold`. */
  private def recordedCons(rule: String, res: (Expr, Boolean)): (Expr, Boolean) = {
    val r = recorder
    if ((r ne null) && r.active) {
      val arith = r.node match {
        case Equals(a, b) => res._1 == BooleanLiteral(true) ||
          ((a, b) match { case (_: IntegerLiteral, _: IntegerLiteral) | (_: BooleanLiteral, _: BooleanLiteral) => true; case _ => false })
        case e => e.getType == IntegerType()
      }
      r.rewrite(if (rule != "arith" || arith) rule else "fold", res._1)
    }
    res
  }

  private def isProjection(e: Expr): Boolean = e match {
    case _: Variable => true
    case ADTSelector(adt, _) => isProjection(adt)
    case TupleSelect(tuple, _) => isProjection(tuple)
    case _ => false
  }

  private def isSimpleBinding(e: Expr): Boolean = e match {
    case FiniteSet(Seq(), _) | FiniteMap(Seq(), _, _, _) | FiniteBag(Seq(), _) => true
    case _: Literal[?] | ADT(_, _, Seq()) => true
    case IsConstructor(recv, _) => isProjection(recv)
    case _ => isProjection(e)
  }

  override final def transform(e: Expr, path: Env): Expr = {
    dynStack.set(if (dynStack.get.isEmpty) Nil else (dynStack.get.head + 1) :: dynStack.get.tail)
    val (re, pe) = simplify(e, path)
    dynPurity.set(if (dynStack.get.isEmpty) dynPurity.get else pe :: dynPurity.get)
    re
  }

  // We make sure to not simplify refinements as this could lead to
  // variable and definition miss-matches during simplification
  override def transform(tpe: Type, path: Env): Type = tpe
}
