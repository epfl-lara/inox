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
  * Each case states why its clauses hold under that interpretation, which is what the soundness of
  * proofs relies on. The managers only choose which rules to apply and when.
  *
  * The equality rules assume that custom equalities are equivalence relations, and [[Rule.Purity]]
  * that functions respect them. Nothing checks either.
  *
  * The kernel covers the calls, equalities, types and lambdas so far; the quantifiers and the
  * witnesses still build their clauses themselves. [[Rule.Unfold]] also registers the items of the template with their managers,
  * like any instantiation does.
  */
trait RuleKernel { self: Templates =>
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  enum Rule {

    /** `blocker ==> target`, where `target` is the blocker of an instantiation that is reached
      * from several places, such as the definition blocker of a call, the blocker of an equality,
      * or the type blocker of an application result. `blocker` may be a conjunction, such as an
      * application's blocker and the condition under which it is dispatched to a lambda.
      *
      * Under the intended interpretation, `target` holds iff one of the conditions that enable it
      * does, and `blocker` is one of them. */
    case Enables(blocker: Encoded, target: Encoded)

    /** `!blocker`, where `blocker` guards a call whose ground arguments fail to evaluate.
      *
      * Evaluation fails before it reaches the call, so no solution reaches it. */
    case Unreachable(blocker: Encoded)

    /** The instantiation of `template` on `args` under `blocker`, as the body of a call that fails
      * iff `failure` holds, or as a template that doesn't fail when `failure` is `None` (see
      * [[Template.instantiate]]).
      *
      * The template generator gives clauses that hold for the template's expression whenever its
      * blocker holds, and substituting the arguments preserves them. */
    case Unfold(template: Template, blocker: Encoded, args: Seq[Arg], failure: Option[Encoded])

    /** The call `tfd(args)`, under `blocker`, whose ground arguments evaluate to the result `value`.
      * The call fails iff `failure` holds.
      *
      * The evaluator computes the value of the call, which is its value under every solution. */
    case UnfoldValue(tfd: TypedFunDef, value: Expr, blocker: Encoded, args: Seq[Arg], failure: Encoded)

    /** `blocker ==> (decrease || diverges)`, or `blocker ==> decrease` without `diverges`, where
      * `decrease` states that a call ranks higher than a call that its body reaches under `blocker`
      * (see [[FunctionTemplates.rankClauses]]).
      *
      * Ranking each call that returns by the depth of its evaluation satisfies `decrease`. Only a
      * call that doesn't return can't be ranked, and `diverges` then holds. Without `diverges`,
      * the front-end has checked that every call returns (see `optAssumeChecked`). */
    case Decreases(blocker: Encoded, decrease: Encoded, diverges: Option[Encoded])

    /** `blocker1 && blocker2 && args1 == args2 ==> tfd(args1) == tfd(args2)`, comparing the
      * arguments and the results with the equalities of their types.
      *
      * The result of a call is a function of its arguments. These clauses only shortcut the
      * unfolding of both calls, so the equalities in them are not unfolded. */
    case Purity(tfd: TypedFunDef, args1: Seq[Encoded], blocker1: Encoded, args2: Seq[Encoded], blocker2: Encoded)

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

    /** `blocker ==> (result == (domain1 && ... && domainN ==> codomain))`, where `result` is a fresh
      * literal for the typing of an application result, `domainI` the memberships of its arguments
      * in the parameter types, and `codomain` the typing of the result in the return type.
      *
      * A function of type `Pi(x: A). B` maps the arguments in `A` to results in `B`, and nothing is
      * said of the others, so `result` stands for this implication. */
    case ApplicationTyping(blocker: Encoded, result: Encoded, domain: Seq[Encoded], codomain: Encoded)

    /** `blocker ==> (result == typings.withOperands(operands))`, where `result` is the typing result
      * of a function, and `operands` the typings of its applications found so far.
      *
      * A function lies in its type iff the results of all its applications do (see
      * [[ApplicationTyping]]). `typings.rest` stands for the applications still to come. */
    case FunctionTyping(blocker: Encoded, result: Encoded, typings: OpenAnd, operands: Seq[Encoded])

    /** `blocker ==> (isFree == !equalities.withOperands(operands))`, where `isFree` is a fresh literal,
      * and `operands` are the equalities of a free function to the lambdas of its type found so far,
      * under their start blockers.
      *
      * `isFree` stands for the function being equal to none of the lambdas of its type, and
      * `equalities.rest` for its equalities to the lambdas still to come. */
    case NonFree(blocker: Encoded, isFree: Encoded, equalities: OpenOr, operands: Seq[Encoded])

    /** `last.rest == next.withOperands(operands)`, under `guard` if there is one, where `next` is
      * [[OpenJunction.next]] of `last`.
      *
      * `last.rest` stands for the operands still to come, which are now `operands` and those that
      * the fresh `next.rest` stands for. */
    case Link[J <: OpenJunction[J]](last: J, next: J, operands: Seq[Encoded], guard: Option[Encoded])

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

    /** `bc == (blocker1 && blocker2 && caller1 == caller2)` and `bc && argEqs ==> resultEq`, where
      * `bc` is a fresh literal, and `argEqs` and `resultEq` compare the arguments and the results
      * of two applications with the equalities of their types.
      *
      * An application is a function of its caller and arguments. Like [[Purity]], this assumes that
      * functions respect custom equalities. */
    case Congruence(bc: Encoded, blocker1: Encoded, blocker2: Encoded, caller1: Encoded, caller2: Encoded,
                    argEqs: Seq[Encoded], resultEq: Encoded)

    /** `blocker && isFree && start && lambda() == f() ==> lambda == f`, where `f` is a free function
      * with no parameters, and `lambda` a pure lambda with no parameters, i.e. one that returns a
      * value it captures, created under `start`.
      *
      * The value of a free function that is equal to no lambda (`isFree`, see [[NonFree]]) is the
      * lambda that returns its result, and lambdas are equal when their normalized bodies and
      * closures are. Without `isFree`, `f` may be equal to another lambda, whose body differs. */
    case ArglessEquality(blocker: Encoded, isFree: Encoded, f: Encoded, tpe: FunctionType, start: Encoded, lambda: Encoded)

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

    /** `result == cached`, where both are the results of the same typing of the same value under
      * the same blocker (see [[TypeTemplates.instantiateTyping]]).
      *
      * They stand for the same proposition. */
    case SameTyping(result: Encoded, cached: Encoded)

    /** `blocker ==> result`, where `result` is the result of a typing in a type that needs no
      * unrolling.
      *
      * Such a type constrains its values no more than their sort does, so every value lies in it. */
    case TrivialTyping(blocker: Encoded, result: Encoded)

    /** `blocker ==> less`, where `less` orders a function that a lambda captures before the lambda
      * (see [[TypeTemplates.CaptureTemplate]]).
      *
      * A lambda value contains the values it captures, so ordering function values by their size
      * satisfies `less`. This only holds under intensional equality: otherwise, `() => f()` is
      * equal to the function `f` it captures. */
    case CapturedBefore(blocker: Encoded, less: Encoded)

    /** The clauses of this rule. This is the only code that builds them. */
    def clauses: Clauses = this match {
      case Enables(blocker, target) =>
        Seq(mkImplies(blocker, target))

      case Unreachable(blocker) =>
        Seq(mkNot(blocker))

      case Unfold(template, blocker, args, failure) => failure match {
        case Some(failure) => template.instantiate(blocker, args, failure)
        case None => template.instantiate(blocker, args)
      }

      case UnfoldValue(tfd, value, blocker, args, failure) =>
        val start = Variable.fresh("cs", BooleanType())
        val (p, cls) = mkExprClauses(start, value, Map(start -> blocker))
        val tmplClauses = cls + (start -> Equals(tfd.applied, p))

        val (contents, _) = Template.contents(
          start -> blocker,
          tfd.params.map(_.toVariable) zip args.map(_.encoded),
          tmplClauses,
          optCall = Some(Defined(tfd)),
          partial = true
        )

        contents.instantiation(blocker, Map.empty[Encoded, Arg]).clauses(failure = Some(failure))

      case Decreases(blocker, decrease, diverges) =>
        Seq(mkImplies(blocker, diverges.fold(decrease)(mkOr(decrease, _))))

      case Purity(tfd, args1, blocker1, args2, blocker2) =>
        val (equalities, equalityClauses) = (tfd.params.map(_.getType) zip (args1 zip args2)).map {
          case (tpe, (e1, e2)) => guardedEquality(blocker1, tpe, e1, e2)
        }.unzip

        val (entail, entailClauses) =
          guardedEquality(blocker1, tfd.getType, mkCall(tfd, args1), mkCall(tfd, args2))

        equalityClauses.flatten ++ entailClauses :+
          mkImplies(mkAnd(blocker1 +: blocker2 +: equalities*), entail)

      case Reflexivity(tpe, e1, e2, guard) =>
        val premise = guard.fold(mkEquals(e1, e2))(g => mkAnd(g, mkEquals(e1, e2)))
        Seq(mkImplies(premise, equality(tpe, e1, e2)))

      case Symmetry(tpe, blocker, e1, e2) =>
        Seq(mkImplies(blocker, mkEquals(equality(tpe, e1, e2), equality(tpe, e2, e1))))

      case Transitivity(tpe, guard, e1, e2, e3) =>
        Seq(mkImplies(mkAnd(guard, equality(tpe, e1, e2), equality(tpe, e2, e3)), equality(tpe, e1, e3)))

      case ApplicationTyping(blocker, result, domain, codomain) =>
        Seq(mkImplies(blocker, mkEquals(result, mkImplies(mkAnd(domain*), codomain))))

      case FunctionTyping(blocker, result, typings, operands) =>
        Seq(mkImplies(blocker, mkEquals(result, typings.withOperands(operands))))

      case NonFree(blocker, isFree, equalities, operands) =>
        Seq(mkImplies(blocker, mkEquals(isFree, mkNot(equalities.withOperands(operands)))))

      case Link(last, next, operands, guard) =>
        val link = last.link(next, operands)
        Seq(guard.fold(link)(mkImplies(_, link)))

      case Dispatched(blocker, dispatch) =>
        Seq(mkImplies(mkNot(dispatch.rest), mkNot(blocker)))

      case DispatchFailure(enabler, appFailure, bodyFailure) =>
        Seq(mkImplies(enabler, mkEquals(appFailure, bodyFailure)))

      case Congruence(bc, blocker1, blocker2, caller1, caller2, argEqs, resultEq) =>
        Seq(
          mkEquals(bc, mkAnd(blocker1, blocker2, mkEquals(caller1, caller2))),
          mkImplies(mkAnd(bc +: argEqs*), resultEq))

      case ArglessEquality(blocker, isFree, f, tpe, start, lambda) =>
        val (lambdaApp, fApp) = (mkApp(lambda, tpe, Seq.empty), mkApp(f, tpe, Seq.empty))
        Seq(mkImplies(mkAnd(blocker, isFree, start, mkEquals(lambdaApp, fApp)), mkEquals(lambda, f)))

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

      case SameTyping(result, cached) =>
        Seq(mkEquals(result, cached))

      case TrivialTyping(blocker, result) =>
        Seq(mkImplies(blocker, mkEquals(result, trueT)))

      case CapturedBefore(blocker, less) =>
        Seq(mkImplies(blocker, less))
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
