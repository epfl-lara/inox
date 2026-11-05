# Distinguishing inputs for first-class functions

This note states what the distinguishing inputs ("witnesses") in `LambdaTemplates.scala`,
`Templates.instantiateWitness` and the check loop of `UnrollingSolver.scala` guarantee, and sketches
why. It builds on the formalization in Nicolas Voirol's thesis, *Verified Functional Programming*
(EPFL, no. 9479, 2019), called "the thesis" below. Theorem and lemma numbers refer to its Chapter 2
unless stated otherwise.

## 1. The problem

Function equality is structural (thesis §2.1.1). Two lambdas are equal iff their normalized
structures coincide and their closures are equal (Lemma 7). This makes equality decidable, which the
completeness of model finding relies on, but it is not extensional: two distinct function values can
agree on every input.

Model extraction must map distinct model terms to distinct values. The thesis states this right after
its extraction rules (§2.2): for function terms `t1`, `t2` with extractions `v1`, `v2`,
`M ⊨ t1 ≃ t2` iff `v1 = v2`. The thesis gets it by extracting unknown functions as `λx. f_t(x)`, where
`f_t` is a fresh synthetic definition. Inox instead rebuilds a free function as an `if`-chain over the
applications in the model. It keeps distinct terms distinct with `uniquateClosure`, or with `choose`
for cyclic values.

Either way, a counterexample can claim `f != g` while no input tells `f` and `g` apart. Under Scala
semantics such a counterexample is spurious. The thesis lists this under Future Work (Chapter 7),
where it suggests "generating clauses from which distinguishing inputs can be extracted". This is
that construction.

### Why it matters: counterexamples without function equality

The unrolling procedure of the thesis needs the target language to compare functions structurally.
Its completeness argument (Theorem 2) extracts models whose distinct functions may agree on every
input, and such a counterexample only means something in a language that can observe the
structure of functions. That is the most stringent requirement the technique places on a language.
Many languages don't meet it. Their function equality is reference equality, extensional
equality, undecidable, or doesn't exist at all.

With witnesses, the counterexamples no longer depend on function equality. By Theorem C and its
corollaries (§5), every pair of distinct functions in a model found with witnesses comes with an
input on which the two functions give different results. Each distinction the model makes between
functions is therefore observable through applications alone. The counterexample stays valid under
any function equality that separates functions with different results, structural, by reference or
extensional, and in a language with no function equality at all. Theorem D (§6) makes this
complete: whenever such a counterexample exists, the procedure finds one.

So the unrolling technique applies to arbitrary languages, whatever the operational semantics of
their function equality, or without one. The procedure can still compare functions structurally
inside the solver, to dispatch applications and to keep closures apart. The witnesses ensure that
the counterexamples it reports never rely on that comparison, or on evaluating equality between
functions at all.

The extracted model must not compare functions either. A free function `f: (Int => Int) => Int`
applied to `g` and `h` is extracted as an if-chain over its applications, and a chain that tests
`x == g` asks the language to compare functions. When `f(g)` and `f(h)` differ, `g ≄ h` holds and
the pair has a distinguishing input `w` with `g(w) ≠ h(w)`. The branch for `g` therefore tests
`x(w) == g(w)`, which separates `g` from `h` with one application and a comparison of results.
A branch tests its argument on the distinguishing input of each other argument at that position,
and results of function type are tested on their own distinguishing inputs, so curried arguments
are separated by a sequence of applications. Such a model of `f` is still a valid model of `f(g)`
and `f(h)`: it maps `g` and `h` to their extracted results, since each passes its own tests and
fails the tests of the others.

This extraction falls back to comparing functions when no distinguishing input applies:

- two arguments are lambdas of the program under `intensional` equality, which are told apart by
  structure (under `none`, their witness is instantiated when extraction needs it, §9);
- the argument is a datatype or tuple containing functions;
- the arguments get no instantiated distinguishing input, as when Theorem F drops the witnesses,
  which only happens under `intensional` equality.

`choose` extraction (cyclic values) also still selects its branches by comparing values.

## 2. The construction

**Notation.** At step `i` of the procedure:

- `Φi` is the clause set of the thesis.
- `Bi` is the set of satisfaction assumptions (`templates.satisfactionAssumptions`). This is the
  thesis's `block(Fi) ∪ block(Ai, Λi, Di)`, together with the blockers for types and quantifiers.
- `U` is the set of user assumptions.

Inox registers a function term as *free* when nothing defines it. Each free term `f` has a guard
`g_f`, its blocker conjoined with "`f` is no known lambda". The free terms are:

- function-typed free variables,
- function-typed parts of free values (from type unfolding with `FreeGenerator`),
- function-typed results of applications of free functions, and
- function-typed witness arguments.

The blocker under which an application result is registered only bounds when its typing holds, so
a model could leave it false. A result therefore also gets an *activity literal*, implied by the
application's blocker (`resultGuards`), and its guard includes that literal.

Each lambda template `λ` has a start blocker `s_λ`.

**Pairs.** A pair `p = (f, h)` of terms of the same type is one of:

- `f` free and `h` another free term, with condition `c_p = g_f ∧ g_h`;
- `f` free and `h` a lambda template `λ`, with `c_p = g_f ∧ s_λ`;
- under `none` and `extensional` function equality only (§9), two lambda templates `λ1`, `λ2` that
  differ in structure, or share a structure but have closures that differ syntactically, with
  `c_p = s_λ1 ∧ s_λ2`. Under `none`, these pairs are only instantiated on demand.

Unless function equality is `extensional`, the pairs that involve a free function are *on demand*
as well: they get no `eq_p` clause and stay out of `E_i` until a model shows both of their members.
A free function shows up when extraction reaches it, and a lambda when its start blocker holds in the
model. Validation then *promotes* these pairs (`promoteWitnesses`): they get their `eq_p` clause, join
`E_i`, and the model check runs again. From then on they follow the rules below.

Pairs are registered when their second member is (`LambdaTemplates.registerFunction`,
`instantiateLambda`, `equalityClauses`).

**Lambdas.** Under `intensional` function equality, Inox compares lambdas structurally: lambdas
with the same structure are equal iff their closures are, and the others are distinct. Under
`none` and `extensional`, only the direction that holds extensionally is kept. For lambdas with
the same structure and closure equalities `κ`, `c_p ∧ κ ⇒ λ1 ≃ λ2`, and the pair gets a
distinguishing input otherwise (§9).

**Equality literals.** Every pair gets a fresh literal `e_p` and the clause

    (eq_p)   e_p ∧ c_p ⇒ f ≃ h

**Instantiation.** Instantiating `p` (`Templates.instantiateWitness`) adds the following:

- fresh witness arguments `w̄` of the parameter types,
- a blocker `s_p` with `s_p ⇔ (W ∧ c_p ∧ f ≄ h)`, where `W` is one global literal (`witnessEnabler`),
- the embedding of `f(w̄) != h(w̄)` under `s_p`, and
- the free typing of `w̄` under `s_p`.

When `w̄` has function type, it is registered as free, so it gets pairs of its own.

`Ψi` denotes all the `eq_p` clauses together with everything instantiations have produced by step
`i`, including the later unfolding of what they introduced.

**Depth.** A pair has depth `d(p) = max(d(f), d(h)) + 1`, where terms of the query have depth 0.
Everything created while instantiating `p`, or later unfolded from it, inherits `d(p)`:

- the witness arguments,
- their type unfoldings (`typeDepths`),
- the results of applications on them (`appDepths`), and
- lambdas and lambda bodies instantiated for them.

**Level.** `L` is 0 until the first model is found, then grows by one with each unrolling. `E_i` is
the set of `e_p` for pairs not instantiated yet. It is assumed only while `L > 0` and witnesses are
in use (`useWitnesses`).

**Rules.** The model check runs on `Φi ∪ Ψi` under `U ∪ Bi ∪ {W} ∪ Ei` (`W` once something is
instantiated). If it is UNSAT and `Ei` is not empty:

- **R1.** Let `N` be the set of literals `e_p` in the unsat core, or all of `Ei` when the solver gives
  no core. If some pairs of `N` have depth at most `L`, instantiate them and check again.
- **R2.** Otherwise, check again without `Ei`. If that check is SAT, the equalities are to blame even
  though the core doesn't show it. Solvers don't reliably report every assumption they use: Z3 often
  leaves the equality literals out. In that case, instantiate every pending pair of depth at most `L`,
  or go to the proof check if there is none. If the check without `Ei` is UNSAT, continue with its
  result.

All further decisions are therefore based on a check that didn't assume `Ei`.

- **R0.** SAT, `L = 0`, and some pair is pending. Set `L := 1` and check again.
- **Otherwise**, the loop proceeds as without witnesses. SAT goes to validation, or to the finite
  range check for quantifiers. UNSAT goes to the proof check, except that a model check with nothing
  left to unroll answers UNSAT only when `W` wasn't assumed.

The **proof check** first runs under `U ∪ R ∪ {W}`, where `R` is the set of refutation assumptions
(`refute`). If that is UNSAT, it runs again under `U ∪ R`. UNSAT there is a proof. SAT there means no
model with distinguishing inputs can ever exist, as the next section shows, so the witnesses are
dropped (`useWitnesses := false`) and `W` and `E` are never assumed again.

The **finite range check** (thesis Chapter 4) also assumes `W` and `Ei`, and applies R1 and R2 to its
own UNSAT answers. It never drops witnesses. **Validation** drops them when a model found with them
can't be extracted or validated.

**Extraction order.** Extraction rebuilds a free function as an `if`-chain over its applications in
the model. Its default branch, for inputs outside these points, is taken from the first application.
Applications to witness arguments are placed last (`isWitnessArgument`), so they give the default
only when the function has no other application, and the default is the same as without witnesses. Otherwise a witness point
could set the default to a value that breaks a quantified property of the function.

Unsat cores are only hints here. Every decision that matters is backed by a check, so no result
below depends on cores being correct or minimal.

## 3. Assumptions

- **(A1)** The guarantees of the procedure without witnesses, as in thesis Chapters 1 to 4. This
  includes their hypotheses: terminating definitions, and the essentially uninterpreted fragment
  for quantifiers. It also includes Inox's documented departures from the thesis.
- **(A2)** The underlying solver is sound and complete for the quantifier-free clause sets it
  receives. Nothing is assumed about its unsat cores.
- **(A3)** Extraction is consistent on active applications. If `M` satisfies the blockers, an
  extracted function applied to the extracted arguments of an application whose blocker holds
  evaluates to the extracted result. This is the property behind thesis Theorem 1 and item 5 of
  Theorem 2, which Inox's `if`-chains provide.

## 4. Witnesses are conservative

**Lemma W1 (inert witnesses).** Every model `M` of `Φi ∪ X` extends to a model `M'` of
`Φi ∪ Ψi ∪ X` with `M'(W) = false` and `M'(e_p) = false` for every `p`. Here `X` is any set of
clauses that mentions neither `W`, the `e_p`, nor symbols introduced by `Ψi`.

*Proof sketch.* `M'` gives `W` and every `e_p` the value false, and keeps `M` elsewhere. The clauses
of `Ψi` come in three kinds:

1. `eq_p` holds because its antecedent contains `e_p`.
2. `s_p ⇔ (W ∧ …)` forces `s_p` to false.
3. Everything else was produced by embedding or unfolding under `s_p`, or under blockers defined from
   it. These clauses have the shape of thesis Lemma 1, `b ⇒ c`, where each new blocker is defined as
   its parent conjoined with a condition. Setting all of these blockers to false satisfies them, as
   in Lemma 1.

The remaining definitional clauses are about fresh symbols that `M` doesn't constrain: the witness
arguments, application results, lambda closures and capture order. They are satisfiable for fresh
symbols, by the same argument that the thesis's unfolding steps use for calls, applications and new
`δτ` constructors (Theorem 2 and the proof of Theorem 3). ∎

**Theorem A (proofs are sound).** If the procedure answers UNSAT, the query has no counterexample.

*Proof sketch.* An UNSAT answer has one of two origins:

- **The proof check.** The answer comes from the run without `W`, so `Φi ∪ Ψi ∪ U ∪ R` is
  unsatisfiable.
- **A model check with nothing left to unroll.** Here `Φi ∪ Ψi ∪ U ∪ Bi` is unsatisfiable. Neither
  `W` nor any `e_p` was assumed: R1 and R2 make every decision after an UNSAT check under `Ei` on a
  check without it, and the loop only answers UNSAT from a model check when `W` wasn't assumed.

In both cases, the contrapositive of Lemma W1 shows that `Φi` is unsatisfiable together with the
same assumptions. Thesis Theorem 3, together with its Chapter 3 and 4 counterparts, concludes. ∎

**Lemma W3 (dropping is justified).** If `Φi ∪ Ψi ∪ U ∪ R ∪ {W}` is unsatisfiable, then no later
model check that assumes `W` is satisfiable.

*Proof sketch.* Clause sets only grow (`Φj ⊇ Φi`, `Ψj ⊇ Ψi`). A later model check assumes more,
namely `Bj` and `Ej` in addition to `R`. So it is unsatisfiable as well. The refutation assumptions
`R` are part of the satisfaction assumptions, as in the procedure without witnesses. ∎

**Theorem B (models stay sound).** A model returned with SAT gives a counterexample, exactly as in
thesis Theorem 1.

*Proof sketch.* The returned `M` satisfies `Φi ∪ Bi`, and Theorem 1 applies. The applications that
witnesses introduce, like `f(w̄)`, are embedded applications like any other. Their blockers are in
`Bi`, and extraction treats them as additional points of the `if`-chain. Each point agrees with the
dispatch interpretation in `M`, by congruence of the encoded application. So (A3) still holds.
Since witness points come last in the extraction order, the default branch is chosen among the
other points as before, so the finite range check of thesis Chapter 4 justifies quantified properties
of the extracted function as before. With
`optCheckModels`, every model is re-checked by the evaluator anyway. ∎

## 5. Distinguishing inputs

**Theorem C.** Let `M` be the model of a SAT answer obtained with witnesses in use. Every model check
after the first one is in that case, by R0. Let `p = (f, h)` be a registered pair with `M ⊨ c_p`.
Then either `M ⊨ f ≃ h`, or `p` has been instantiated, `M ⊨ s_p`, and `M ⊨ f(w̄) ≄ h(w̄)`. In the
second case the blockers of both applications hold, since they lie in `Bi`.

*Proof sketch.* If `p` is pending, `e_p` was assumed, and `eq_p` gives `f ≃ h`. If `p` is
instantiated and `M ⊨ f ≄ h`, then `M ⊨ W ∧ c_p ∧ f ≄ h`, so `M ⊨ s_p`, and the embedding of
`f(w̄) != h(w̄)` under `s_p` holds. ∎

**Corollary C1 (extracted functions differ on an input).** Assume moreover that extraction is
well founded on `M`: no cyclic function value is reached, so no `choose` is produced. Let `t1`, `t2`
be active terms of the same type, at least one of them free. If `M(t1) ≠ M(t2)`, then their
extractions differ, and the difference is observable through applications to extracted values.
For function types this means there are values `ā` such that `ext(t1)(ā)` and `ext(t2)(ā)`
evaluate to different values.

*Proof sketch.* By well-founded induction on the extraction recursion.

- **First-order sorts.** SMT model values are in normal form, so extraction is injective (thesis
  §2.2).
- **Datatypes.** Distinct values differ in their constructor, or in some field, and the induction
  applies to that field. Function-typed fields of free values are free terms.
- **Functions.** Theorem C gives `w̄` with `M(f(w̄)) ≠ M(h(w̄))`. Take `ā = ext(M(w̄))`. By (A3),
  `ext(f)(ā)` evaluates to `ext(M(f(w̄)))`, and likewise for `h`. The two results differ by the
  induction hypothesis. This works because function-typed results of free applications are
  registered as free terms, and the results of lambdas are embedded expressions. ∎

**Corollary C2 (comparisons agree with extensional equality).** Consider the evaluation of the
query on the reported counterexample. Each comparison between two function values, at least one
of which is the extraction of a free term, has the same outcome under structural and extensional
equality. Equal values are structurally equal, hence extensionally equal. Values that are not
equal differ on an input by C1.

A comparison between two lambdas of the program is the one exception under `intensional`
equality, as no witness is involved: the program fixes their structural distinctness. Under
`none`, the query can't contain it, and under `extensional`, such lambdas form a pair (§9).

## 6. Completeness

A witness constraint `f ≄ h ⇒ f(w̄) ≄ h(w̄)` is an extensionality assumption, which structural
equality doesn't satisfy in general. So completeness takes two forms: one for the counterexamples
that satisfy it, and a fallback for the ones that don't.

**Lemma W2 (finite rounds).** Between two unrollings, the procedure instantiates finitely many pairs.

*Proof sketch.* At level `L`, only pairs of depth at most `L` are instantiated. Instantiation creates
no terms of depth 0, and all unfolding of what it creates is deferred to the next unrolling (types
via `typeDepths`, lambda bodies via `appDepths`). By induction on `k`, there are finitely many pairs
of depth `k`:

- Pairs of depth 1 are pairs of depth-0 terms, and there are finitely many of those until the next
  unrolling.
- Pairs of depth `k + 1` involve terms of depth at most `k`. These terms come from finitely many
  instantiations of depth at most `k`.

R0 fires once per check, and each drop happens at most once. ∎

So an infinite run performs infinitely many unrollings, `L` grows without bound, and fairness of the
unrolling (thesis Definition 4) holds as without witnesses.

**Definition.** Fix a run, and let `Φ∞` and `Ψ∞` be the unions of its clause sets. A counterexample
`γ` is *finitely distinguishable* when some model `M*` of `Φ∞ ∪ Ψ∞ ∪ U ∪ {W}` satisfies two
conditions:

1. **Agreement.** `M*` agrees with `γ` as in the proof of thesis Theorem 2: a blocker holds iff the
   evaluation of `γ` reaches its label.
2. **Finiteness.** The following set `T` is finite. It holds the calls and application/lambda pairs
   whose blocker holds in `M*`, and the pairs `p` with `M* ⊨ c_p ∧ f ≄ h`.

Intuitively, `γ` can be extended with distinguishing inputs for every pair of distinct functions it
involves, and only finitely many such inputs are needed. This fails when `γ` needs two distinct but
extensionally equal functions, as in `f == (x => g(x))`. It also fails when every distinguishing input
creates further distinct functions without end.

**Theorem D (completeness for finitely distinguishable counterexamples).** Assume (A2) and unbounded
unrolling. If the query has a finitely distinguishable counterexample, the procedure answers SAT
with a model found while witnesses are in use. Theorems B and C then apply to that model.

*Proof sketch.*

1. **The check without equalities is eventually SAT.** `M*` satisfies `Φi ∪ Ψi ∪ U ∪ {W}`. It also
   satisfies every blocker assumption of `Bi`, except the ones guarding pending items of `T`. By W2
   and fairness, there is a step after which every call and application of `T` is unfolded, and
   `L` is at least the depth of every pair of `T`. From then on, `M*` satisfies every check that
   doesn't assume `Ei`.
2. **No drop.** By step 1, the proof check under `W` is SAT, so `refute` never drops the witnesses.
   Before that step, it doesn't drop them either: `M*` satisfies `Φi ∪ Ψi ∪ U ∪ R ∪ {W}` at every
   step, since `R` holds in `M*` as in thesis Theorem 2. Validation doesn't drop them, since the model
   is extractable and valid by Theorem B. The implementation limits under §7 are the exception.
3. **Termination.** Suppose the run is infinite, and consider the steps after the one given by step
   1. An UNSAT model check under `Ei` instantiates pairs in its core (R1), finitely often per level
   by W2. Once R1 has none left to instantiate, R2 runs the check without `Ei`, which is SAT by step
   1, and instantiates every pending pair of depth at most `L`. This includes every pending pair of
   `T`. After finitely many steps, every pair of `T` is instantiated. `M*` then falsifies no
   assumption of the model check under `Ei`, so that check is SAT.

   For quantified queries, the finite range check assumes `W` and `Ei`, and applies R1 and R2 the
   same way. The completeness argument of thesis Chapter 4 then applies to it. ∎

R1 may instantiate pairs outside `T`. This is harmless, because W2 bounds the number of
instantiations per level.

On-demand pairs (§2) leave the argument unchanged for the pairs a model shows: such a model goes to
validation, which promotes them, so every pair of `T` that models keep showing ends up in `E_i`.
Pairs that no model shows never need a distinguishing input, since extraction never compares their
members. Each validation promotes finitely many pairs (W2 bounds the terms of each round), and a
promoted pair is never on demand again.

**Theorem E (refutable queries still terminate).** If `Φk ∪ U` is unsatisfiable under the
refutation assumptions for some `k`, which is the thesis's condition for proofs, the procedure
answers UNSAT after finitely many steps.

*Proof sketch.* Each unrolling is reached after finitely many steps (W2), and unrolling stays fair
despite the witnesses' extra calls, because each generation is finite. After the unrolling that
covers `Φk`, every model check is UNSAT. Each UNSAT check reaches the proof check after finitely many
steps: R1 and R2 instantiate finitely often (W2) and then move to the proof check rather than
unrolling directly, and drops happen at most once. The proof check is then UNSAT, because
`Φi ∪ Ψi ∪ U ∪ R ⊇ Φk ∪ U ∪ R`. ∎

**Theorem F (fallback for counterexamples that aren't finitely distinguishable).** Suppose the
query has a counterexample, and the extensionality assumption is refutable for it: for some `k`,
`Φk ∪ Ψk ∪ U ∪ R ∪ {W}` is unsatisfiable. Then the procedure drops the witnesses after finitely many
steps. From then on, it is the procedure without witnesses, which finds the counterexample by
thesis Theorem 2.

*Proof sketch.* The run reaches step `k` (W2). Every UNSAT model check reaches the proof check after
finitely many steps, as in the proof of Theorem E, and model checks under `W` are UNSAT by W3. The
proof check under `W` is then UNSAT. The query is satisfiable, so the proof check without `W` is
SAT by Theorem A, and `refute` drops the witnesses. After the drop, `W` and `E` are never assumed.
Lemma W1 makes `Ψ` inert, and thesis Theorem 2 applies. The model is extracted with
`uniquateClosure` as before. ∎

For example, `f == (x => g(x))` forces `f` and `g` apart with no distinguishing input. Once the
lambda is applied to the witness, `f(w) == g(w)` is derived, the witness assumption is refuted, and
the witnesses are dropped.

The remaining gap is a counterexample whose extensionality assumption is unsatisfiable without
being refutable by unfolding, for instance when refuting it needs induction. There the procedure
keeps unrolling and gives no answer, in the same way the procedure without witnesses gives no answer
on an unsatisfiable query it can't refute. Closing this gap means trading against Theorem C. One
way is to interleave model checks without witnesses and return their models, for instance after a
fixed number of unrollings without a witness model. That loses Theorem C for queries whose
distinguishing model lies deeper than the bound.

## 7. Limitations

- Theorem D needs unbounded unrolling. With `optUnrollBound`, the answer can be Unknown.
- Corollary C1 needs well-founded extraction. Cyclic values are extracted with `choose`, and nothing
  is claimed for them.
- Nullary functions are no exception. Their distinguishing input is the empty argument list, so
  instantiating a pair of nullary functions adds `f ≄ h ⇒ f() ≄ h()`, that is
  `f() ≃ h() ⇒ f ≃ h`. A counterexample that needs two distinct nullary functions with equal
  results is therefore not finitely distinguishable, like the eta-expansion above. Theorem F covers
  it, and the model is then extracted without witnesses.
- Decoding backends can fail to extract models with function-typed witnesses (cvc5 at the time of
  writing). Validation then drops the witnesses, so Theorem C doesn't hold for those models.
- Activity literals are only added for function-typed application results. A function stored in a
  datatype that a free function returns is registered under its typing blocker. That blocker bounds
  but doesn't force the typing, so Theorem C relies on that blocker being true for such functions.
- Cost: no witness is instantiated before the first model (R0). Queries that never have a model, such
  as most verification conditions, only pay for the `eq_p` clauses, whose literals they never assume.
- Cost of models: every function term the unrolling creates is paired with all earlier terms of its
  type. On Stainless's `Berardi1`, where application results of function type keep appearing, the
  pending pairs grew from 238 to 5,400 over 14 unrollings, all at depth 1, and every model check
  assumed their equalities. The query went from 1 s to 40 s on Z3 and 6 min on cvc5, ending Unknown
  as before. Promoting pairs only once a model shows them (§2) brings it back to 1 to 4 s. Under
  `extensional`, pairs can't wait for a model, since `f ≄ h` must imply a distinguishing input in
  refutations as well, so this cost remains there.

## 8. Tests

`src/it/scala/inox/solvers/unrolling/FunctionWitnessSuite.scala` runs every test under `intensional`
equality unless stated otherwise, on native Z3,
`unrollz3`, SMT-LIB Z3 and cvc5, with and without model finding, and with `optCheckModels`.
Theorem B is therefore checked on every model.

| Property | Tests |
|---|---|
| C, C1 on free/free and free/lambda pairs | distinct first-order functions; distinct function and lambda; distinct function and closure; distinct functions agreeing on an input; distinct nullary functions; distinct nullary function and lambda |
| C1 through argument and result types | distinct functions of several arguments; distinct curried functions; distinct higher-order functions |
| C1 through datatypes and type parameters | distinct functions in datatypes; distinct functions on a type parameter; distinct functions over a recursive type with function fields |
| D with many pairs, a finite domain, unfolding and quantifiers | many pairwise distinct functions; all Boolean functions; distinguishing input that needs unfolding; distinct functions next to a recursive function |
| A when the extensionality assumption fails | structurally distinct, extensionally equal lambdas; distinct functions equal on every input; more distinct Boolean functions than extensional ones; unsatisfiable query about distinguishing inputs |
| F, the fallback for intensional counterexamples | eta-expanded closure remains distinct; nullary functions with equal results; intensional counterexample that needs unfolding; intensional counterexample over a recursive type with function fields |
| A, E on refutable queries | equal functions agree; unsatisfiable query with distinct functions |
| Extraction without comparing functions (§1) | functions applied to distinct functions; functions applied to a function and a lambda; functions applied to distinct curried functions (skipped on unrollz3, whose models give `f` the same result on both arguments); distinct higher-order functions |
| Rejecting comparisons under `none` (§9) | function comparisons are rejected without function equality; function comparisons at type parameters are rejected without function equality; function comparisons in callees are found at their type arguments (an intermediate callee, polymorphic recursion); comparisons with constructors without functions are accepted |
| Models under `none` and `extensional` (§9) | functions applied to functions without function equality (lambda pairs on demand); free functions passed to a function without function equality (free pairs promoted from on demand, §2); models with extensional function equality |
| Refutations under `none` and `extensional` (§9) | intensional counterexamples don't exist without function equality; extensionally equal functions are equal; extensionally distinct lambdas are distinct; structurally distinct lambdas remain distinct |
| Evaluation (§9) | quantified function comparisons are evaluated extensionally; `EvaluatorSuite`'s "Function equality" (by results, undecidable comparisons, tuples, intensional) |
| Incremental state, option off | incremental solving; disabled witnesses |

## 9. Function equality semantics

`optFunctionEquality` (`--function-equality`) selects the semantics of equality between functions.
§2 to §6 describe `intensional`.

| Setting | Comparisons in queries | Witnesses | Lambdas | Evaluator |
|---|---|---|---|---|
| `none` (default) | rejected | unconditional, on demand | no structural inequality, witnesses on demand | by results |
| `intensional` | structural | under `W`, on demand, dropped by Theorem F | structural | structural |
| `extensional` | extensional | unconditional | no structural inequality, lazy witnesses | by results |

**`none`.** `assertCnstr` rejects a query that compares values whose type contains functions,
directly or in a function it transitively calls. Callees are checked at the type arguments of their
calls, so `jixx[A, B]`, which compares values of type `A`, is rejected when called with
`A = U => Boolean` (Stainless's `Berardi1`). The type parameters of the query itself are assumed to
admit equality, and past eight instantiations of the same function (polymorphic recursion), its
generic body is checked instead. #34 replaces this check with equality types.

Without comparisons, a query can't observe function equality: functions only occur in applications,
and a model stays a model when functions that agree on every input are identified. So the solver
may interpret function equality as extensional equality, and witnesses hold unconditionally, in
refutations as well as in models. Theorem F never applies, since an intensional counterexample needs
a comparison. A query that needs two functions to be distinct while they agree on every input, like
`f(g) ≠ f(eta(g))`, is UNSAT, which is the correct answer in a language without function equality.

Lambdas aren't compared structurally: their equality can't be observed, so it is left open. Giving
every pair of lambdas a distinguishing input when it is created makes some queries much harder
(TIP's `Lang` hangs Z3). So lambda/lambda pairs are registered without an equality literal
(`LambdaTemplates.onDemandWitnesses`), and are only instantiated when extraction needs to tell two
lambda arguments of a free function apart. The solver then instantiates them and checks again.

**`extensional`.** Comparisons are allowed and mean extensional equality. Witnesses hold
unconditionally, so `f ≄ h ⇒ f(w̄) ≄ h(w̄)` is an extensionality axiom. Refutations rely on it:
`(f ≠ g) ∧ ∀x. f(x) = g(x)` and `g ≠ eta(g)` are UNSAT. Pairs of lambdas that differ in structure or
closures get the same lazy witnesses as free functions (§3): the lambdas are assumed equal when
looking for a model, and the witness is instantiated once that equality is in an unsat core, up to
the depth that the unrolling has reached. `id ≠ alsoId` is UNSAT this way.

Instantiating lambda witnesses eagerly, with each new lambda, doesn't terminate. A witness can
create lambdas on the spot (eg. in the typing constraints of application results, as in Stainless's
encoded programs), and each new lambda is compared to all earlier lambdas of its type. In
`LawTypeArgsElim`, a single forall-checking solver reached witness depth 3056, with about 3000
lambdas and 6000 witnesses, without unrolling once. Bounding that depth by the unrolling made each
round finite, but the lambdas still grew from round to round (124, 623 then 1122 over rounds 4 to 6).
With lazy witnesses, the same check passes, in 6 s to 2.5 min depending on the run.

**Evaluator.** Under `none` and `extensional`, `RecursiveEvaluator` compares function values by their
results. Structurally equal values are equal. Otherwise, the values are applied to the closed
subexpressions of the parameter types that they contain, and to the simplest values of those types.
For extracted models these include the distinguishing inputs. The values are distinct if some
input tells them apart, and the comparison is an evaluation error otherwise. Ground simplification
and model validation follow, so a model is never accepted on a structural comparison that the
semantics doesn't make. Under `none`, `SolvingEvaluator` checks quantifiers under `none` as well,
unless the model values compare functions where no input tells them apart, in which case it uses
`extensional`. Always using `extensional` ran out of memory on Stainless's `LawTypeArgsElim` in
lucky mode, through the (then eager) lambda witnesses of `extensional` (see below).

