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
  *  - [[Rule.Define]] and [[Rule.Enables]] introduce fresh symbols: any interpretation can be
  *    extended to them, as long as each symbol is defined once;
  *  - the other rules are facts about the semantics, and each one states why its clauses hold
  *    under that interpretation.
  * The soundness of proofs relies on both. The managers only choose which rules to apply and when.
  *
  * The equality rules assume that custom equalities are equivalence relations, and
  * [[Rule.Congruence]] that functions respect them. Nothing checks either.
  *
  * The kernel covers the calls, equalities, types and lambdas so far; the quantifiers and the
  * witnesses still build their clauses themselves. [[Rule.Unfold]] also registers the items of the
  * template with their managers, like any instantiation does.
  */
trait RuleKernel { self: Templates =>
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

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
      *  - the guard of the [[Congruence]] of two applications. */
    case Define(guard: Option[Encoded], literal: Encoded, value: Encoded)

    /** `blocker ==> target`, where `target` is the blocker of an instantiation that is reached
      * from several places, such as the definition blocker of a call, the blocker of an equality,
      * or the type blocker of an application result. `blocker` may be a conjunction, such as an
      * application's blocker and the condition under which it is dispatched to a lambda.
      *
      * Interpreting `target` as the disjunction of the conditions that enable it satisfies the
      * clause, and the instantiation under `target` holds wherever one of them does. */
    case Enables(blocker: Encoded, target: Encoded)

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

    /** `!blocker`, where `blocker` guards a call whose ground arguments fail to evaluate.
      *
      * Evaluation fails before it reaches the call, so no solution reaches it. */
    case Unreachable(blocker: Encoded)

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

    /** `premise1 && ... && premiseN ==> resultEq`, where the premises are the blockers of two calls or
      * applications of the same function and the equalities of their arguments, and `resultEq` the
      * equality of their results, each compared with the equality of its type.
      *
      * A call or application is a function of its callee and arguments. This assumes that functions
      * respect custom equalities. */
    case Congruence(premises: Seq[Encoded], resultEq: Encoded)

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
      * The value of a free function that is equal to no lambda is the lambda that returns its
      * result, and lambdas are equal when their normalized bodies and closures are. Without
      * `isFree`, `f` may be equal to another lambda, whose body differs. */
    case ArglessEquality(blocker: Encoded, isFree: Encoded, f: Encoded, tpe: FunctionType, start: Encoded, lambda: Encoded)

    /** The clauses of this rule. This is the only code that builds them. */
    def clauses: Clauses = this match {
      case Define(guard, literal, value) =>
        val definition = mkEquals(literal, value)
        Seq(guard.fold(definition)(mkImplies(_, definition)))

      case Enables(blocker, target) =>
        Seq(mkImplies(blocker, target))

      case Unfold(template, blocker, args, failure) => failure match {
        case Some(failure) => template.instantiate(blocker, args, failure)
        case None => template.instantiate(blocker, args)
      }

      case Unreachable(blocker) =>
        Seq(mkNot(blocker))

      case Decreases(blocker, decrease, unless) =>
        Seq(mkImplies(blocker, unless.fold(decrease)(mkOr(decrease, _))))

      case Congruence(premises, resultEq) =>
        Seq(mkImplies(mkAnd(premises*), resultEq))

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
