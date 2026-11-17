# Partial execution: functions that fail or diverge

This note describes how the unrolling procedure treats evaluation that doesn't return a value,
either because it gets stuck on an error or because it never terminates. It complements the
guarantees in [`README.md`](README.md), whose semantics is the one of
`evaluators/RecursiveEvaluator`.

## 1. Semantics

A query is satisfiable when some assignment of its free variables makes it evaluate to `true`.
Evaluation can also end without a value, in two ways:

- **Stuck.** Evaluation reaches a `RuntimeError`: an `Error(tpe, msg)`, an `Assume` whose condition
  doesn't hold, an integer or real division, remainder or modulo by zero, or an ADT whose invariant
  fails when the value is built.
- **Divergent.** A chain of calls never returns. The evaluator reports this as running out of
  steps.

No Inox expression can observe the difference between the two: a query that reaches either one
doesn't evaluate to `true`. The procedure therefore treats both as the same undefined result, written
⊥ below.

Lambdas are values whatever their bodies do: `x => error[T]` and `x => loop(x)` are values, and only
applying them may give ⊥. Function types are read partially accordingly:

> `f` lies in `Pi(x: A). B` when, for every `a` in `A`, if `f(a)` evaluates to a value `b`,
> then `b` lies in `B[a]`.

Under this reading every function type is inhabited, as `x => error[B]` lies in `A => B` even when
`B` is empty. The total reading, where `f(a)` must also return, can't be checked by evaluation,
since it would need the evaluator to prove that `f` terminates. `SymbolOps.hasInstance` departs from
the partial reading on one point (see §5).

## 2. How the encoding handles ⊥

The encoding only ever needs to know where evaluation is defined. A clause that mentions the result
of an expression is guarded by the blocker of the path that evaluates it, so it only constrains
assignments under which evaluation reaches that expression. On such a path, every result that the
query uses was returned, and the clauses hold for these results.

| Construct | Encoding | Why it's right under the partial reading |
|---|---|---|
| `Error`, failed `Assume`, undefined operation | A failure literal, which formulas assert to be false, so the path that reaches it is infeasible (`TemplateGenerator.Builder.storeFailure`, §4) | Evaluation along that path doesn't return |
| Call `f(a)` | Unfolded as `f(a) = body[a]`, guarded by the call's blocker | The equation holds whenever `f(a)` returns |
| Call `g(b)` reached while evaluating the body of `f(a)` | `rank_f(a) > rank_g(b) \|\| diverges` on the path that reaches it, where the search for models assumes `!diverges` (`FunctionTemplates.rankClauses`, §3) | A call that returns has a finite evaluation, whose depth is a rank |
| Application of a free function, `f(a) ∈ B` | Assumed at each application (`LambdaTemplates.registerApplication`) | The application is reached, so `f(a)` returned |
| Return type of a call | Assumed of the result, for arguments in the parameter types | Only constrains a result that was returned |
| Membership of a function value in `Pi(x: A). B` | Checked at a witness `x0` under a free guard `w`: `w ==> B(f(x0))` (`TemplateGenerator.mkTypeClauses`) | Where `f(x0)` is ⊥, the guard's path is infeasible, so `x0` can't refute membership |

The last row is where the partial reading shows. A function that fails at some point still lies in
the type, as long as it returns values of the type wherever it returns. A function that diverges at
some point lies in the type as well, but showing it needs the call to diverge, which the procedure
never establishes (§3):

```scala
// h: (BigInt => {v: BigInt | v > 0}) => {b: Boolean | b}
!h((x: BigInt) => error[BigInt])                           // UNSAT: the lambda is in h's domain
!h((x: BigInt) => if (x > 0) x else 0)                     // not UNSAT: 0 is outside the codomain
!h((x: BigInt) => if (x > 0) x else loop(x))               // Unknown
```

`PartialExecutionSuite` checks these cases.

## 3. Calls that reach themselves

A call that reaches itself on the same arguments never returns: evaluation is deterministic, so it
would reach the same call again. The unrolling doesn't see this on its own. Once every call on such a
cycle is unfolded, no call is left pending, and the equations of the cycle hold for any value:

- `def loop(x: BigInt): BigInt = loop(x)` gives `loop(x) = loop(x)`. `Template.extractCalls` drops
  the body's call, since it equals the template's own call.
- `def f(x: BigInt): BigInt = g(x)` and `def g(x: BigInt): BigInt = f(x)` give `f(x) = g(x)` and
  `g(x) = f(x)`. The call `f(x)` that unfolding `g(x)` reaches is already unfolded.

The solver could then return a model that relies on, say, `loop(0) = -1` or `f(2) = 0`, which only
`--check-models` rejects.

`FunctionTemplate.apply` therefore ranks calls. Each function `f` gets an uninterpreted integer
function `rank_f` of its arguments. Every call `g(b)` that evaluating the body of `f(a)` reaches
adds `rank_f(a) > rank_g(b) || diverges` on the path that reaches it, where `diverges` is a single
literal shared by all calls. A call that returns has a finite evaluation, so ranking it by the depth
of its evaluation satisfies these clauses. Along a cycle on the same arguments, the ranks would have
to decrease back to themselves, so the paths that close the cycle need `diverges`.

The search for models assumes `!diverges`, like the blockers of the calls that aren't unfolded yet,
so no model takes the paths that close a cycle. Proofs don't assume it, so no proof relies on a call
never returning either. The evaluator can't tell that a call diverges, as it runs out of steps, and
the solver doesn't decide more than the evaluator: a query whose answer depends on a call diverging
gets `Unknown`.

```scala
def loopPos(x: BigInt): BigInt = if (x > 0) loopPos(x) else x

loopPos(k) == 0   // SAT, with k = 0
loopPos(k) == 5   // Unknown: only k > 0 could give 5, where loopPos diverges
loop(k) == 0      // Unknown
f(k) == 0         // Unknown
```

Only the body's own paths are ranked: the calls in lambdas and quantifiers that the body contains
belong to their own templates, and the calls in type checks aren't evaluated by the evaluator. One
exception: the refinements of an uninterpreted call's result type are assumed on the body's paths,
though the evaluator never evaluates them, so a call in such a refinement is also ranked.

## 4. Where functions fail

Under extensional equality, functions are partial: two functions differ on an input on which one of
them fails and the other doesn't, and agree on an input on which both fail. `x => error[Unit]` and
`x => ()` are distinct, while `() => 1 / y` and `() => 2 / y` are equal when `y == 0`. Telling these
apart needs a literal for "`f(a)` fails", which the encoding builds as follows:

- Each point where evaluation may fail (an `Error`, an `Assume`, a partial operation) gets a literal
  that holds exactly when its path is taken and its condition doesn't hold (`Builder.storeFailure`).
- Whether a call `f(a)` fails is a literal of the call, and whether an application `g(a)` fails is
  a first-order uninterpreted predicate of `g` and its arguments, whose congruence makes
  applications to equal arguments fail alike (`Templates.callFailure` and `appFailure`). When a call
  or an application is unfolded, the template of the body it reaches defines its failure: the body
  fails iff one of its failure literals holds, or a call or an application on one of its paths fails
  (`Template.instantiate`).
- Free functions are partial as well: whether one of their applications fails is only constrained
  where a formula reaches it, and the model of a free function fails on the inputs on which its
  applications fail in the model.
- The templates of formulas (the query, typing constraints, quantifier bodies, equalities) assert
  that their failure literals are false, and that the calls and applications on their paths don't
  fail. The paths that fail are then infeasible, as they were before failures had literals.
- The distinguishing input `w` of two functions `f` and `g` (see `function-witnesses.md`) is the one
  place where an application may fail: if `f != g`, either exactly one of `f(w)` and `g(w)` fails, or
  neither fails and `f(w) != g(w)`.

The evaluator compares functions the same way (`RecursiveEvaluator.valuesEqual`).

## 5. Limits

**Loops on changing arguments stay blocked.** A loop such as `def f(x: BigInt): BigInt = f(x + 1)`
reaches a new call at each unfolding, so some call is always pending. `ModelCheck` blocks the
pending calls, so no model relies on a value that `f` never returns. The solver doesn't terminate on
such a query instead. Proofs that need the call to diverge are out of reach, though:
`x => if (x > 0) x else f(x)` lies in `BigInt => {v: BigInt | v > 0}`, but showing it means showing
that `f(x)` never returns a value, which needs induction. Unrolling doesn't do induction.

**Partial operations are total under `--assume-checked`.** The evaluator fails on a division,
remainder or modulo of integers or reals by zero, and on a selector of another constructor. The
solvers make the paths on which these fail infeasible, unless a front-end has checked them with
`--assume-checked`. They are then total SMT terms, and a model may rely on a value of `x / 0` that
evaluation never produces.

**Divergence is never decided.** Neither the solver nor the evaluator establishes that a call
diverges (§3), even when it reaches itself on the same arguments. Under extensional equality, whether
a function that diverges on an input equals another one is therefore undecided too:
`(x: BigInt) => loop(x)` is neither shown equal to nor distinct from `(x: BigInt) => 0`, and such
queries get `Unknown`.

**Quantified assumptions cost more.** The failure literal of an `Assume` is equal to the negation
of its condition, so quantifiers in the condition are encoded with both polarities, and the negative
one introduces a fresh witness for each of them. Under total functions (`--assume-checked`, or any
other function equality), assumptions can't fail and their quantifiers are only encoded positively.
With many quantified assumptions, such as in TIP's `Tutorial`, the witnesses can keep feeding new
instantiations, so such queries are best run under `--assume-checked`.

**Equal lambdas aren't applied.** Two lambdas that a model makes equal are only compared on their
distinguishing input once they are distinct, so a model can equate lambdas that differ on some input
(e.g. `p == ((x: BigInt) => x + y == (x: BigInt) => x - y)` with `p` true). Model checks reject such
models, and the solver answers `Unknown`.

**Function types into empty types are empty for `hasInstance`.** Under the partial reading,
`x => error[B]` lies in `A => B` even when `B` is empty. `SymbolOps.hasInstance` holds such a type
empty when `A` is inhabited, so a quantifier over it is vacuous, and `forall (f: BigInt => T) => false`
holds for an empty type parameter `T`.

**Front-ends that rely on totality.** A front-end that checks that every function terminates and
never fails, as Stainless does, could let Inox assume the total reading everywhere, which would make
more proofs go through. Inox has no option for it.
