# The unrolling procedure

This package implements the decision procedure formalized in Nicolas Voirol's
thesis, *Verified Functional Programming* (EPFL, thesis no. 9479, 2019).
Throughout this file, "the thesis" means that document. Chapter 1 covers
recursive functions and datatypes, Chapter 2 first-class functions, Chapter 3
dependent types, Chapter 4 quantifiers, and §6.1 the solver loop.

The procedure reduces a query over the Inox language (recursive functions,
lambdas, datatypes, dependent types and quantifiers) to a sequence of
quantifier-free SMT queries. Each query is checked by an underlying theory
solver (`../z3`, `../smtlib`, `../princess`). Its proofs are sound and it is
complete for counterexamples, under the assumptions listed below.

## The formalization

### Blockers and unfolding (thesis Chapter 1)

Every expression is translated into a set of clauses over boolean *blockers*.
A blocker `b` guards the clauses that encode the body of one branch. Each
function call `f(args)` reached under blocker `b` is recorded, and its body is
not encoded yet. Unfolding the call means instantiating `f`'s template with
`args`, guarded by `b`.

At step *i*, the current clause set `Φi` over-approximates the query, because
every call that has not been unfolded is uninterpreted. Adding `block(Fi)`
(the negation of each blocker guarding a call that has not been unfolded) gives
an under-approximation, because it only keeps paths whose calls are all
encoded. The loop in `UnrollingSolver.scala` (`checkAssumptions`) alternates
between the two:

- `ModelCheck` checks `Φi` together with `satisfactionAssumptions` (the blocking
  literals). A model is a candidate counterexample and goes to `Validate`,
  through `FiniteRangeCheck` when quantifier instantiations are pending.
- `Validate` extracts the model. With `optCheckModels`, it also evaluates the
  query in the model, and answers `Unknown` if that fails.
- `ProofCheck` checks `Φi` together with `refutationAssumptions`, which block
  no unfolding (they only hold the typing literals of free functions and
  collections). UNSAT here proves the query unsatisfiable.
- `Unroll` unfolds everything pending at the oldest generation (calls, types,
  equalities, applications and quantifier instantiations), so each of them is
  eventually unfolded. This is the fairness condition that completeness relies
  on.

| Concept | Code |
|---|---|
| Expression to clause translation | `TemplateGenerator.mkExprClauses` |
| Function templates and call unfolding | `FunctionTemplates.scala` |
| Clause and blocker infrastructure | `Templates.scala` |
| Custom equality on datatypes (`ADTSort.equality`), unfolded like calls | `EqualityTemplates.scala` |
| Uninterpreted calls, as applications of free functions (constants when nullary) | `TemplateGenerator.uninterpretedFunction` |
| The check/unroll loop and model extraction | `UnrollingSolver.scala` |

### First-class functions (thesis Chapter 2)

Lambdas are closures. `normalizeStructure` (in `ast/SymbolOps.scala`) turns a
lambda into a structure plus a list of closed dependencies. Two lambdas with
the same structure are equal iff their dependencies are equal, and lambdas
with different structures are distinct. The evaluator normalizes lambdas the
same way (`evaluators/RecursiveEvaluator.scala`), so both agree on which
lambdas are equal.

Each application `f(x)` is dispatched to every known lambda template of the
right type and to every free function. The dispatch is guarded by
"`f` equals this lambda" (`LambdaTemplates.instantiateApp`), so the encoding
stays first-order. The thesis's incremental uninterpreted sort for lambdas
(§2.6.1) appears as the `order`/`lessThan` clauses in
`TypeTemplates.CaptureTemplate`. These clauses ensure that a closure cannot
capture itself. Lambda tracking (§2.6.2) is `LambdaTemplates.registerLambda`.

This structural equality is the default (`--function-equality=intensional`).
Under `none` and `extensional`, distinct functions also get an input on which
they differ, so that counterexamples don't rely on comparing functions. This
extension is described in [`function-witnesses.md`](function-witnesses.md).

### Dependent types (thesis Chapter 3)

Types are encoded by the reducibility predicate `⟦τ⟧`, unfolded lazily like a
function call (`TemplateGenerator.mkTypeClauses`, `TypeTemplates.scala`):

- A refinement `{x: τ | p}` holds when `x ∈ ⟦τ⟧` and `p(x)` holds.
- A dependent pair `Σx: τ1. τ2` holds when its first component is in `⟦τ1⟧` and
  its second is in `⟦τ2⟧`, with `x` bound to the first component.
- A dependent function `Πx: τ1. τ2` holds when every application to an argument
  in `⟦τ1⟧` returns a value in `⟦τ2⟧`.
- Datatypes unfold constructor by constructor. Inductive types are unfolded
  lazily and are blocked in `ModelCheck` like calls, which is the thesis's
  `block(Ri)`.

A type is either constrained on a free value (`FreeGenerator`), assumed of a
computed value such as the result of a call (`ContractGenerator`), decided
exactly, as for the domains of Π types (`MembershipGenerator`), or used to
order the functions that a closure captures (`CaptureGenerator`). Free
functions are typed at their applications, and free maps, sets and bags at
the keys and elements that the query reads.

### Quantifiers (thesis Chapter 4)

`∀x: τ. p` is a `Boolean` expression; Inox has no separate `Prop` sort.

- **Positive polarity** (assumed true). The quantifier is instantiated on the
  ground terms that match its matchers (applications and the reads of maps,
  sets and bags), so each instance is `τ(t) ⇒ p[x/t]`.
- **Negative polarity** (assumed false). The quantifier gets a fresh skolem
  constant `c` and the clause `τ(c) ∧ ¬p[x/c]`.
- **Unknown polarity**, for example under an equality. Both templates are
  registered.

Both templates are in `QuantificationTemplates.scala`. A quantifier that is
assumed true only gives a counterexample when the model satisfies it
everywhere. `getFiniteRangeClauses` (the `FiniteRangeCheck` state) and
`checkForall` together decide that, for the essentially uninterpreted fragment
of the thesis (`model_i`). A model outside that fragment is reported as
`Unknown`, unless evaluating the query in the model shows that it holds, which
is only attempted for quantifiers that match neither calls nor lambdas.

## Guarantees

The semantics is the one implemented by `evaluators/RecursiveEvaluator`.

- **Proofs are sound.** If the procedure answers UNSAT, no assignment of the
  free variables makes the query evaluate to `true`.
- **Counterexamples are sound.** A model returned with SAT is meant to make
  the query evaluate to `true`. This is only checked with the evaluator when
  `optCheckModels` is set (it is off by default), in which case a model that
  fails the check gives `Unknown`.
- **Counterexamples are complete.** If a satisfying assignment exists and its
  evaluation terminates, the procedure eventually finds a model, provided
  `optUnrollBound` is unbounded (the default) and the query stays in the
  fragment the thesis covers. Quantifiers must be in the essentially
  uninterpreted fragment, models of first-class functions must be
  extractable, and type parameters must be inhabited.

The procedure is a semi-decision procedure for satisfiability, so it may run
forever on unsatisfiable queries, and the soundness of proofs is relative to
terminating function definitions. Inox checks neither termination nor
positivity of datatypes; Stainless does both before it calls Inox.

## Departures from the thesis

Inox differs from the formalization in a few places, which matter when
reading the proofs against the code:

- **By design**: closures are normalized more aggressively, models of
  functions are `if`-chains instead of named recursive functions, calls are
  merged across branches, and Inox has features outside the formalization
  (ADT invariants, custom equality, uninterpreted calls, `assume`, the SMT
  theories).
- **Stricter than the thesis states**: refinement predicates are guarded by
  their base type, Π codomains and return types are only assumed for
  arguments in the domain, and type parameters may be empty.
- **`optAssumeChecked`** lets a front-end that checks arguments itself, such
  as Stainless, skip the domain checks.
