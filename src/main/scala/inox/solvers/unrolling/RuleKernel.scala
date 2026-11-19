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
  * The kernel covers the calls and the equalities so far; the other templates still build their
  * clauses themselves. [[Rule.Unfold]] also registers the items of the template with their managers,
  * like any instantiation does.
  */
trait RuleKernel { self: Templates =>
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  enum Rule {

    /** `blocker ==> target`, where `target` is the blocker of an instantiation that is reached
      * from several places, such as the definition blocker of a call, or the blocker of an
      * equality.
      *
      * Under the intended interpretation, `target` holds iff evaluation reaches one of the places
      * that it stands for, and `blocker` guards one of them. */
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
