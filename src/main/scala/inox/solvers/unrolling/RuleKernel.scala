/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

/** The rules of the unfolding: each [[Rule]] names a set of clauses, and [[Rule.clauses]] builds them.
  *
  * The clauses that the procedure asserts are meant to hold under the *intended interpretation* of
  * every solution, i.e. every assignment of the free variables under which the query evaluates to
  * `true` (see `RecursiveEvaluator`). It extends the solution to the symbols that the unfolding
  * introduces:
  *  - a blocker holds iff evaluation reaches the path it guards;
  *  - a call term is the value of the call;
  *  - the equality symbol of a type (see [[EqualityTemplates.equalitySymbol]]) is that type's
  *    equality, its custom equality (see [[ast.Definitions.ADTSort.equality]]) or the structural
  *    one built from those of its fields.
  *
  * The rules come in two kinds:
  *  - [[Rule.Define]], [[Rule.Enables]] and [[Rule.Hypothesis]] introduce fresh symbols: any
  *    interpretation can be extended to them, as long as each symbol is defined once;
  *  - the other rules are facts about the semantics, and each one states why its clauses hold
  *    under that interpretation.
  * The soundness of proofs relies on both. The managers only choose which rules to apply and when.
  *
  * The equality rules assume that custom equalities are equivalence relations, and
  * [[Rule.Congruence]] that functions respect them. Nothing checks either.
  *
  * Every clause that the procedure asserts comes from a rule. The clauses of the finite range check
  * (see [[QuantificationTemplates.getFiniteRangeClauses]]) are not asserted: like the satisfaction
  * assumptions, they only restrict the models of one check. [[Rule.Unfold]] and [[Rule.Instance]]
  * also register the items of the instantiation with their managers.
  *
  * [[RuleChecker]] checks, as the solver runs, that the clauses it asserts are those of the rules,
  * that the rules introduce each fresh symbol once, and that its refutations only make the
  * assumptions that refutations may make.
  */
trait RuleKernel { self: Templates =>
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  /** What an [[Rule.Instance]] instantiates. */
  enum InstanceOf {
    case Expression(exempt: App => Boolean)
    case OfAxiom
    case Counterexample
  }

  enum Rule {

    // Fresh symbols

    /** `literal == value`, under `guard` if there is one, where `literal` is a fresh symbol that
      * no other rule defines.
      *
      * Interpreting `literal` as `value` where `guard` holds satisfies the clause. What `literal`
      * stands for only matters for the assumptions that the checks make about it (see
      * [[OpenJunctions]]). The definitions are:
      *  - the typing of an application result, `domain1 && ... && domainN ==> codomain`, and of a
      *    function, the conjunction of the typings of its applications;
      *  - a typing whose type needs no unrolling, `true`, and one that is already instantiated under
      *    the same blocker, its result;
      *  - whether a free function is equal to none of the lambdas of its type;
      *  - the `rest` of an [[OpenJunction]], as the new operands and the `rest` of the next one;
      *  - the guard of the [[Congruence]] of two applications, and the condition under which two
      *    functions need a [[Witness]];
      *  - the conjunction of a set of blockers (see [[BlockerGraph.encodeBlockers]]);
      *  - whether the body of a function or lambda fails, as whether one of its failure literals or
      *    the calls and applications on its paths does, and whether an application fails, as the
      *    failure predicate of its type (see [[PartialFunctions]]). */
    case Define(guard: Option[Encoded], literal: Encoded, value: Encoded)

    /** `blocker ==> target`, where `target` is the blocker of an instantiation that is reached
      * from several places, such as the definition blocker of a call, the blocker of an equality,
      * or the type blocker of an application result. `blocker` may be a conjunction, such as an
      * application's blocker and the condition under which it is dispatched to a lambda.
      *
      * Interpreting `target` as the disjunction of the conditions that enable it satisfies the
      * clause, and the instantiation under `target` holds wherever one of them does. */
    case Enables(blocker: Encoded, target: Encoded)

    /** `literal && condition ==> fact`, where `literal` is a fresh symbol that only the model checks
      * assume, such as the equality of two functions whose distinguishing input isn't instantiated
      * yet (see [[WitnessTemplates.witnessEqualities]]).
      *
      * Interpreting `literal` as `false` satisfies the clause, and the refutation checks don't
      * assume it. */
    case Hypothesis(literal: Encoded, condition: Encoded, fact: Encoded)

    // Unfolding

    /** The instantiation of `template` on `args` under `blocker`, as the body of a call that fails
      * iff `failure` holds, or as a template that doesn't fail when `failure` is `None` (see
      * [[Template.instantiate]]).
      *
      * The template generator gives clauses that hold for the template's expression whenever its
      * blocker holds, and substituting the arguments preserves them. When the template is that of
      * a ground call's value, the evaluator computed that value, which is the call's value under
      * every solution. */
    case Unfold(template: Template, blocker: Encoded, args: Seq[Arg], failure: Option[Encoded])

    /** The clauses of `instantiation`, which is one of:
      *  - an [[InstanceOf.Expression]]: the query or the typing of a free variable, under their root
      *    blocker (see [[Root]]), the definitions of a witness, under the condition that it needs
      *    one (see [[Templates.instantiateWitness]]), or the closures of a lambda or quantification,
      *    under the blocker where it is created (see [[TemplateStructure]]). As for [[Unfold]], the
      *    generator gives clauses that hold for the expression whenever its blocker holds. The
      *    applications that `exempt` picks may fail.
      *  - an [[InstanceOf.OfAxiom]]: the body of a quantification that holds where its path does
      *    (see [[Holds]]), on terms that its matchers matched, under an enabler that implies that
      *    path. A quantification that holds has all its instances. The manager instantiates the
      *    matchers of the instance itself.
      *  - an [[InstanceOf.Counterexample]]: the body of a quantification that doesn't hold where its
      *    path does, on fresh symbols. They stand for a counterexample when the quantification
      *    doesn't hold, and for any value otherwise. */
    case Instance(instantiation: Instantiation, of: InstanceOf)

    /** `start`, where `start` is the root blocker of the query, or of the typing of a free variable.
      *
      * Evaluation reaches the root of the query, and the values of the free variables lie in their
      * types. */
    case Root(start: Encoded)

    /** `blocker ==> (typing == true)`, where `typing` is the result of the typing of a free value
      * that `blocker` reaches, which is deferred until the solver has a use for empty type
      * parameters (see [[TypeTemplates.deferredTypings]]). Its unfolding may define `typing` later.
      *
      * The values of the free variables lie in their types, and so do the values they hold. */
    case Typed(blocker: Encoded, typing: Encoded)

    /** `blocker ==> quantification`, where `quantification` stands for a
      * quantification that occurs where it must hold, under `blocker`, and that an instantiated one
      * subsumes.
      *
      * A solution makes the query hold, so it makes the quantification hold where evaluation
      * reaches it. */
    case Holds(blocker: Encoded, quantification: Encoded)

    /** `!literal`, or `under ==> !literal`, where `literal` is something that no solution reaches:
      *  - the blocker of a call whose ground arguments fail to evaluate, which evaluation fails
      *    before it reaches;
      *  - a failure of a template that isn't the body of a function or lambda, such as the query,
      *    or of a call or application on its paths. A solution evaluates the query without
      *    failing (see `partial-execution.md`). */
    case Unreachable(literal: Encoded, under: Option[Encoded] = None)

    /** `blocker ==> (decrease || unless)`, or `blocker ==> decrease` without `unless`, where
      * `decrease` states that a well-founded measure decreases:
      *  - the rank of a call is higher than that of a call its body reaches under `blocker` (see
      *    [[FunctionTemplates.rankClauses]]). Ranking each call that returns by the depth of its
      *    evaluation satisfies this, and only a call that doesn't return can't be ranked, in which
      *    case `unless` (`diverges`) holds. Without `unless`, the front-end has checked that every
      *    call returns (see `optAssumeChecked`).
      *  - a function that a lambda captures comes before the lambda (see
      *    [[TypeTemplates.CaptureTemplate]]). A lambda value contains the values it captures, so
      *    ordering function values by their size satisfies this. This only holds under intensional
      *    equality: otherwise, `() => f()` is equal to the function `f` it captures. */
    case Decreases(blocker: Encoded, decrease: Encoded, unless: Option[Encoded])

    // Functions and equality

    /** `premise1 && ... && premiseN ==> resultEq`, where the premises are the blockers of two calls,
      * applications or quantifications with the same callee or body, and the equalities of their
      * arguments or closures, and `resultEq` the equality of their results, each compared with the
      * equality of its type.
      *
      * A call or application is a function of its callee and arguments, and a quantification of its
      * body and closures. This assumes that functions respect custom equalities. */
    case Congruence(premises: Seq[Encoded], resultEq: Encoded)

    /** `start ==> distinguished`, where `start` holds iff two functions `f1` and `f2` are distinct
      * where they need a witness, and `distinguished` states that they differ on the witness, fresh
      * arguments `ws`: their applications differ, or, when `failures` gives whether each one fails,
      * one fails and the other doesn't or neither fails and they differ.
      *
      * Witnesses are only used when function equality is extensional or unobservable, and functions
      * can then be interpreted extensionally. Distinct functions then differ on some input, which
      * `ws` stand for. */
    case Witness(start: Encoded, differ: Encoded, failures: Option[(Encoded, Encoded)])

    /** `e1 == e2 ==> eq(e1, e2)`, under `guard` if there is one, where `eq` is the equality
      * symbol of `tpe`.
      *
      * Equalities are reflexive. */
    case Reflexivity(tpe: Type, e1: Encoded, e2: Encoded, guard: Option[Encoded])

    /** `blocker ==> (eq(e1, e2) == eq(e2, e1))`.
      *
      * Equalities are symmetric. */
    case Symmetry(tpe: Type, blocker: Encoded, e1: Encoded, e2: Encoded)

    /** `guard && eq(e1, e2) && eq(e2, e3) ==> eq(e1, e3)`.
      *
      * Equalities are transitive. */
    case Transitivity(tpe: Type, guard: Encoded, e1: Encoded, e2: Encoded, e3: Encoded)

    // First-class functions

    /** `!dispatch.rest ==> !blocker`, where `dispatch` is the dispatch disjunction of an application
      * reached under `blocker`, before any of its operands are found.
      *
      * The caller of an application that evaluation reaches is a function value: a lambda that
      * evaluation creates, or a free function. `dispatch.rest` stands for the disjunction of the
      * conditions under which the caller is each of these. */
    case Dispatched(blocker: Encoded, dispatch: OpenOr)

    /** `enabler ==> (appFailure == bodyFailure)`, where `enabler` holds when an application is reached
      * and dispatched to a lambda whose body fails iff `bodyFailure` holds.
      *
      * The application evaluates that body on its arguments, so it fails iff the body does. */
    case DispatchFailure(enabler: Encoded, appFailure: Encoded, bodyFailure: Encoded)

    /** `start ==> lambda == representative`, where `representative` is a fresh symbol shared by the
      * lambdas with the same type, normalized body and closures, and `lambda` is created under `start`.
      *
      * The value of a lambda is its normalized body and closures, so these lambdas are all the same
      * value, which `representative` stands for. */
    case SameLambda(start: Encoded, lambda: Encoded, representative: Encoded)

    /** The equality of the lambdas `lambda1` and `lambda2`, created where `blocker` holds, where
      * `closuresEqual` is the equality of their closures if their normalized bodies are the same:
      *  - under intensional equality, `blocker ==> (closuresEqual == (lambda1 == lambda2))`, and
      *    `blocker ==> lambda1 != lambda2` for different bodies;
      *  - otherwise, `blocker && closuresEqual ==> lambda1 == lambda2`.
      *
      * The value of a lambda is its normalized body and closures. Under intensional equality, two
      * lambdas are equal iff these are. Otherwise, lambdas with different bodies or closures may
      * still be equal (see [[WitnessTemplates]]). */
    case LambdaEquality(blocker: Encoded, lambda1: Encoded, lambda2: Encoded, closuresEqual: Option[Encoded],
                        intensional: Boolean)

    /** `blocker && isFree && start && lambda() == f() ==> lambda == f`, where `f` is a free function
      * with no parameters, `isFree` holds iff it is equal to none of the lambdas of its type, and
      * `lambda` is a pure lambda with no parameters, i.e. one that returns a value it captures,
      * created under `start`.
      *
      * Under intensional equality, interpreting `isFree` as "`f` is the lambda that returns its
      * result, `() => f()`, and none of the lambdas found so far" satisfies the clause, as lambdas
      * are equal when their normalized bodies and closures are. This leaves the `rest` of the
      * disjunction that defines `isFree` true when `f` is another lambda, such as
      * `() => if (false) error else y`, so the refutation checks must not assume that disjunction
      * complete (see [[LambdaTemplates.registerFunction]]). When functions have witnesses, their
      * equality is extensional or unobservable, `f` and `lambda` are equal whenever their results
      * are, and `isFree` is what it states. Without `isFree`, `f` may be equal to another lambda,
      * whose body differs. */
    case ArglessEquality(blocker: Encoded, isFree: Encoded, f: Encoded, tpe: FunctionType, start: Encoded, lambda: Encoded)

    /** The arguments that the clauses of this rule are built from, by name, as the certificates of
      * the solver's answers give them (see [[certificates.Certificates]]). An argument that the
      * rule doesn't have is left out, and one that only states a case has no terms. A type is
      * given by its equality symbol, with the applications that the clauses have, and a template
      * by the instance that is logged with the rule (see [[RuleChecker.generated]]). */
    def arguments: Seq[(String, Seq[Encoded])] = {
      def one(name: String, e: Encoded) = Seq(name -> Seq(e))
      def opt(name: String, e: Option[Encoded]) = e.toSeq.map(name -> Seq(_))
      def flag(name: String, set: Boolean) = if (set) Seq(name -> Seq.empty[Encoded]) else Seq()
      this match {
        case Define(guard, literal, value) => opt("guard", guard) ++ one("literal", literal) ++ one("value", value)
        case Enables(blocker, target) => one("blocker", blocker) ++ one("target", target)
        case Hypothesis(literal, condition, fact) => one("literal", literal) ++ one("condition", condition) ++ one("fact", fact)
        case Unfold(_, blocker, _, failure) => one("blocker", blocker) ++ opt("failure", failure)
        case Instance(_, of) => of match {
          case InstanceOf.Expression(_) => flag("expression", true)
          case InstanceOf.OfAxiom => flag("axiom", true)
          case InstanceOf.Counterexample => flag("counterexample", true)
        }
        case Root(start) => one("start", start)
        case Typed(blocker, typing) => one("blocker", blocker) ++ one("typing", typing)
        case Holds(blocker, quantification) => one("blocker", blocker) ++ one("quantification", quantification)
        case Unreachable(literal, under) => one("literal", literal) ++ opt("under", under)
        case Decreases(blocker, decrease, unless) => one("blocker", blocker) ++ one("decrease", decrease) ++ opt("unless", unless)
        case Congruence(premises, resultEq) => Seq("premises" -> premises) ++ one("result", resultEq)
        case Witness(start, differ, failures) =>
          one("start", start) ++ one("differ", differ) ++ failures.toSeq.map { case (err1, err2) => "failures" -> Seq(err1, err2) }
        case Reflexivity(tpe, e1, e2, guard) =>
          opt("guard", guard) ++ one("eq", equalitySymbol(tpe)._2) ++ Seq("terms" -> Seq(e1, e2)) ++ one("eq12", equality(tpe, e1, e2))
        case Symmetry(tpe, blocker, e1, e2) =>
          one("blocker", blocker) ++ one("eq", equalitySymbol(tpe)._2) ++ Seq("terms" -> Seq(e1, e2)) ++
            one("eq12", equality(tpe, e1, e2)) ++ one("eq21", equality(tpe, e2, e1))
        case Transitivity(tpe, guard, e1, e2, e3) =>
          one("guard", guard) ++ one("eq", equalitySymbol(tpe)._2) ++ Seq("terms" -> Seq(e1, e2, e3)) ++
            one("eq12", equality(tpe, e1, e2)) ++ one("eq23", equality(tpe, e2, e3)) ++ one("eq13", equality(tpe, e1, e3))
        case Dispatched(blocker, dispatch) => one("blocker", blocker) ++ one("rest", dispatch.rest)
        case DispatchFailure(enabler, appFailure, bodyFailure) =>
          one("enabler", enabler) ++ one("application", appFailure) ++ one("body", bodyFailure)
        case SameLambda(start, lambda, representative) =>
          one("start", start) ++ one("lambda", lambda) ++ one("representative", representative)
        case LambdaEquality(blocker, lambda1, lambda2, closuresEqual, intensional) =>
          one("blocker", blocker) ++ Seq("lambdas" -> Seq(lambda1, lambda2)) ++ opt("closures", closuresEqual) ++
            flag("intensional", intensional)
        case ArglessEquality(blocker, isFree, f, tpe, start, lambda) =>
          one("blocker", blocker) ++ one("free", isFree) ++ one("function", f) ++ one("start", start) ++ one("lambda", lambda) ++
            Seq("results" -> Seq(mkApp(lambda, tpe, Seq.empty), mkApp(f, tpe, Seq.empty)))
      }
    }

    /** The clauses of this rule. This is the only code that builds them. */
    def clauses: Clauses = applying(this)(build)

    private def build: Clauses = this match {
      case Define(guard, literal, value) =>
        val definition = mkEquals(literal, value)
        Seq(guard.fold(definition)(mkImplies(_, definition)))

      case Enables(blocker, target) =>
        Seq(mkImplies(blocker, target))

      case Hypothesis(literal, condition, fact) =>
        Seq(mkImplies(mkAnd(literal, condition), fact))

      case Unfold(template, blocker, args, failure) => failure match {
        case Some(failure) => template.instantiate(blocker, args, failure)
        case None => template.instantiate(blocker, args)
      }

      case Instance(instantiation, of) => of match {
        case InstanceOf.Expression(exempt) => instantiation.clauses(exempt = exempt)
        case InstanceOf.OfAxiom => instantiation.substClauses ++ instantiation.itemClauses(onMatcher = (_, _) => Seq.empty)
        case InstanceOf.Counterexample => instantiation.clauses()
      }

      case Root(start) =>
        Seq(start)

      case Typed(blocker, typing) =>
        Seq(mkImplies(blocker, mkEquals(typing, trueT)))

      case Holds(blocker, quantification) =>
        Seq(mkImplies(blocker, quantification))

      case Unreachable(literal, under) =>
        Seq(under.fold(mkNot(literal))(mkImplies(_, mkNot(literal))))

      case Decreases(blocker, decrease, unless) =>
        Seq(mkImplies(blocker, unless.fold(decrease)(mkOr(decrease, _))))

      case Congruence(premises, resultEq) =>
        Seq(mkImplies(mkAnd(premises*), resultEq))

      case Witness(start, differ, failures) =>
        val distinguished = failures match {
          case None => differ
          case Some((err1, err2)) => mkOr(mkNot(mkEquals(err1, err2)), mkAnd(mkNot(err1), mkNot(err2), differ))
        }
        Seq(mkImplies(start, distinguished))

      case Reflexivity(tpe, e1, e2, guard) =>
        val premise = guard.fold(mkEquals(e1, e2))(g => mkAnd(g, mkEquals(e1, e2)))
        Seq(mkImplies(premise, equality(tpe, e1, e2)))

      case Symmetry(tpe, blocker, e1, e2) =>
        Seq(mkImplies(blocker, mkEquals(equality(tpe, e1, e2), equality(tpe, e2, e1))))

      case Transitivity(tpe, guard, e1, e2, e3) =>
        Seq(mkImplies(mkAnd(guard, equality(tpe, e1, e2), equality(tpe, e2, e3)), equality(tpe, e1, e3)))

      case Dispatched(blocker, dispatch) =>
        Seq(mkImplies(mkNot(dispatch.rest), mkNot(blocker)))

      case DispatchFailure(enabler, appFailure, bodyFailure) =>
        Seq(mkImplies(enabler, mkEquals(appFailure, bodyFailure)))

      case SameLambda(start, lambda, representative) =>
        Seq(mkImplies(start, mkEquals(lambda, representative)))

      case LambdaEquality(blocker, lambda1, lambda2, closuresEqual, intensional) =>
        val equals = mkEquals(lambda1, lambda2)
        (closuresEqual, intensional) match {
          case (Some(eqs), true) => Seq(mkImplies(blocker, mkEquals(eqs, equals)))
          case (None, true) => Seq(mkImplies(blocker, mkNot(equals)))
          case (Some(eqs), false) => Seq(mkImplies(mkAnd(blocker, eqs), equals))
          case (None, false) => Seq.empty
        }

      case ArglessEquality(blocker, isFree, f, tpe, start, lambda) =>
        val (lambdaApp, fApp) = (mkApp(lambda, tpe, Seq.empty), mkApp(f, tpe, Seq.empty))
        Seq(mkImplies(mkAnd(blocker, isFree, start, mkEquals(lambdaApp, fApp)), mkEquals(lambda, f)))
    }
  }

  /** The application of the equality symbol of `tpe` to `e1` and `e2`. */
  private def equality(tpe: Type, e1: Encoded, e2: Encoded): Encoded =
    mkApp(equalitySymbol(tpe)._2, FunctionType(Seq(tpe, tpe), BooleanType()), Seq(e1, e2))

  /** The equality of `e1` and `e2` at `tpe`, which is only related to their structural equality
    * under `blocker` when `tpe` has an equality symbol. */
  private[unrolling] def guardedEquality(blocker: Encoded, tpe: Type, e1: Encoded, e2: Encoded): (Encoded, Clauses) =
    if (!unrollEquality(tpe)) (mkEquals(e1, e2), Seq.empty)
    else (equality(tpe, e1, e2), Rule.Reflexivity(tpe, e1, e2, Some(blocker)).clauses)
}
