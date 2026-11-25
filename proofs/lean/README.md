# The certificate checker in Lean

`inox-check` checks the certificates that Inox prints for its unsat answers
(see [their format](../../src/main/scala/inox/solvers/certificates/README.md)),
as the [Scala checker](../certificates/README.md) does, and has
[Logos](https://github.com/cvc5/logos) check their proofs. Logos is the checker
of cvc5's CPC proofs that is written in Lean and proved sound there, so that
what `inox-check` accepts comes with a theorem.

```sh
inox --solvers=smt-cvc5 file.smt3 > answers.txt   # the file has a (get-proof)
cd proofs/lean && lake build
.lake/build/bin/inox-check answers.txt
```

It accepts a certificate when:

- its rules account for its script ([`Inox/Checker.lean`](Inox/Checker.lean)):
  each rule is an instance of its kind and builds the asserts that it names,
  every assert is named by a rule or is an assumption, each fresh symbol is
  introduced once, and the proof only assumes asserts of the script. Clauses
  are compared as text, up to how cvc5 prints testers (`(is C e)` for
  `((_ is C) e)`), and the clauses of an instance of a template once their
  conjunctions and disjunctions are built as the solver builds them, with
  the values of its parameters (`simplified`): the Scala checker compares
  them up to a normal form of their connectives;
- Logos finds its proof `correct` ([`Inox/Accept.lean`](Inox/Accept.lean)).

With `--rules`, it checks the rules only. With `--terms`, it also checks the
rules on the terms that Logos reads, and prints which facts it covers (see
below); `--remaining` also prints the facts that remain.
`check.sh DIR [JOBS] [FLAGS]` runs it on the files of `DIR`, which is what CI
does on the corpus of the Scala checker, with `--terms` (the `certificates`
job).

## What is proved

[`Inox/Correct.lean`](Inox/Correct.lean) states what an accepted certificate
gives, from the soundness theorem of Logos:

```lean
theorem unsat_of_accept (sound : LogosSound)
    (certificate : Sexp) (checked : Checked) (assums : List Term) (cmds : CCmdList)
    (hAccept : accept certificate = .ok checked)
    (hParse : parseProof checked.proof = .ok (assums, cmds)) :
    eo_satisfiability (logos_assumption_term assums) false
```

The conjunction of the assumptions of the proof, as Logos reads them, has no
model in the semantics of SMT-LIB that Logos formalizes.

[`Inox/NoModel.lean`](Inox/NoModel.lean) states it of the assumptions
themselves: no well-formed model makes all of them true.

```lean
theorem no_model_of_accept (sound : LogosSound)
    (certificate : Sexp) (checked : Checked) (assums : List Term) (cmds : CCmdList)
    (hAccept : accept certificate = .ok checked)
    (hParse : parseProof checked.proof = .ok (assums, cmds)) :
    ∀ M, ¬ Satisfies M assums
```

`Satisfies M ts` is that `M` is a well-formed model in which each formula of
`ts` evaluates to true. No model satisfies a list that contains the assumptions
either (`no_model_of_unsat_of_subset`), such as the asserts of the script.

[`Inox/Fresh.lean`](Inox/Fresh.lean) is a first step towards the rules: the
constraints that introduce a fresh symbol keep a set of constraints satisfiable.
Its key lemma is coincidence (`eval_setConst`): the value of a term does not
depend on the interpretation of a constant it does not mention, provided that
the name of the constant does not start like one of the constants Logos reserves
for partial operators (`@div_by_zero`, `@mod_by_zero`, `@qdiv_by_zero`,
`@oob_seq_nth`, `@wrong_apply_sel_n_m`). The names Logos gives the constants of
a proof, `@u.i` and `@c.i`, never do. From a well-formed model of constraints
that do not mention the symbol, it builds one that also satisfies the
constraints of `Define` (`define_sat`, `define_guarded_sat`), of the root and
hypothesis literals (`root_sat`, `hypothesis_sat`) and of `Enables`
(`enables_sat`).

[`Inox/Extend.lean`](Inox/Extend.lean) lifts these lemmas to the terms Logos
reads from a proof and to `Satisfies`: a model of a list of assumptions extends
to a model of the list with the clauses of a fresh-symbol rule appended
(`define_extends`, `define_guarded_extends`, `root_extends`,
`hypothesis_extends`, `enables_extends`), and so to one of the list with the
clauses of a sequence of such steps (`extend_sat`, `no_model_of_extend`). What
a step requires is static and decidable: its constant is not mentioned by the
assumptions before it nor by the other terms of its clauses, and its clauses
have type `Bool`. That clauses of type `Bool` evaluate to Booleans and that a
definition evaluates to a canonical value of its sort is type preservation, a
theorem of Logos's proofs; it is a hypothesis here, `LogosTyping`, which
`Inox/Closed.lean` discharges (`logos_typing`).

The steps may also be facts, which hold in the models that a predicate `Good`
selects (`Step.fact`, `Holds`), when reinterpreting a fresh symbol keeps those
models (`KeepsConst`): then no model that `Good` selects satisfies the base
assumptions, if none satisfies them with the clauses of the steps
(`extend_sat_good`, `no_model_of_extend_good`). `extend_sat` is the case
`Good := True` without facts.

[`Inox/RuleSteps.lean`](Inox/RuleSteps.lean) ties this to the certificate. It
writes the proof's declarations followed by one `assume` per clause (those of
the query's assumptions, of each rule in order, then of the completeness
assumptions), parses that text with Logos, and makes a step of each rule: a
`Define`, `Hypothesis` or `Root` introduces its literal, the `Enables` rules of
a target together introduce it, and the other rules and the completeness
assumptions are facts. An `Enables` clause `(=> b m)` whose blocker `b` has a
`Define` `(= b rhs)` of which `m` is a conjunct (an operand of `rhs`'s `and`)
is not a blocker of `m`'s step but a derived clause: it holds in every model of
that definition (`holds_derived`), and it comes after the steps. This breaks the
cycles where a conjunction of targets enables one of them (`bs := (and m0 m2)`
with `(=> bs m0)`): `m0` is introduced by its other blockers, then `bs`, then the
clause. `TermSteps.check` ([`Inox/Terms.lean`](Inox/Terms.lean), which
`inox-check --terms` runs) decides that each fresh-symbol step can follow those
before it, that the definition of each derived clause is among them, and that
every assumption of the proof is a clause. It takes time linear in the size of
the clauses, up to hashing: freshness is decided against the set of the names of
the constants that the clauses before mention (`NamesCover`), and the
definitions and the clauses are looked up in hash sets, whose lemmas make the
lookups equalities:

```lean
theorem no_good_model_of_accept (sound : LogosSound) (hty : LogosTyping)
    (Good : SmtModel → Prop) {certificate : Sexp} {checked : Checked} {r : TermSteps}
    (hAccept : accept certificate = .ok checked) (hr : termSteps checked = .ok r)
    (hcheck : r.check = true)
    (hkeep : ∀ st ∈ r.fresh, KeepsConst Good st.const)
    (hfacts : FactsHold Good (extend r.base r.fresh) r.facts) :
    ∀ M, Good M → ¬ Satisfies M r.base
```

What remains is `hfacts`, that each rule that is a fact holds in the models
that the solutions of the query give, and `hkeep`, that those models don't
depend on the fresh symbols: these are about the semantics of Inox.

[`Inox/Unfold.lean`](Inox/Unfold.lean) discharges `hkeep`, and `hfacts` for
the unfoldings of functions without branches, with `Good` the models of the
program's defining equations. The checker keeps the source of each template
that is a function, `(function (f x1 … xn) body)` or the body of the function's
definition that `(definition (f x1 … xn) ..)` instantiates (also without the
names of its subterms, when it lowers without them), and `equations` reads each
`(= (f x1 … xn) body)` with Logos, after the clauses' declarations and those of
the templates' script, without the assumptions of the body, which Logos
doesn't read in a term: `(assume c b)` is `b`. The equation then holds on the
calls that have values, whose evaluation went through the assumptions they met.
A model is `Good` when it satisfies each equation for all
the canonical values of the sorts of its parameters:

```lean
def Good (eqs : List Equation) (M : SmtModel) : Prop :=
  ∀ e ∈ eqs, ∀ vs, List.Forall₂ (Typed M) e.params vs →
    __smtx_model_eval (setConsts M (bindValues e.params vs)) (__eo_to_smt e.term) =
      SmtValue.Boolean true
```

`Good` doesn't include `model_wf`, since `Satisfies` does, and `Keeps`
reinterprets a constant by any value. A fact `(=> g s)` is an unfolding
(`unfoldB`) when `g` is a Boolean and `s` is, as a Logos term, a defining
equation without binders with terms `u1 … un` for its parameters, where each
`ui` has the parameter's sort and is not a selector or a tester; the terms are
found by matching, and only the equality of the terms is relied on. It holds in
every `Good` model (`holds_unfold`), since substitution commutes with evaluation
(`eval_subst`). A fresh symbol keeps the `Good` models when no equation
mentions it and it is no parameter (`keepsB`, by coincidence), which
`TermSteps.keeps` decides for all of them:

```lean
theorem no_good_model_of_unfold (sound : LogosSound) (hty : LogosTyping)
    {certificate : Sexp} {checked : Checked} {r : TermSteps}
    (hAccept : accept certificate = .ok checked) (hr : termSteps checked = .ok r)
    (hcheck : r.check = true) (hkeeps : r.keeps = true)
    (hfacts : FactsHoldExcept (Good r.equations) (unfoldB r.equations)
      (extend r.base r.fresh) r.facts) :
    ∀ M, Good r.equations M → ¬ Satisfies M r.base
```

`FactsHoldExcept` is `FactsHold` for the facts that are not unfoldings, and
`no_good_model_of_unfoldings` needs nothing of the facts when they all are. So
no well-formed model of the program's defining equations satisfies the query.
That such a model exists, and that it agrees with Inox's evaluation of the
functions, which follows from their termination, is a separate layer that is
not proved here.

The unfoldings covered are those of a function whose body has no `ite` and no
call to a function whose value the template names: the clause is then
`(=> start (= (f x1 … xn) body))`. The other clauses of a template mention its
own symbols (the condition `c`, the blockers of the branches `b`, the result
`e`, the values of nested calls and constructors), which hold only once those
symbols are chosen.

### The instances of templates

[`Inox/Meanings.lean`](Inox/Meanings.lean) finds the meaning of each local
symbol of a template, a term over its parameters, from the shapes of its
clauses and its source, as the source check of the Scala checker
([`Sources.scala`](../src/main/scala/inox/certificates/Sources.scala)) does:
the source's `where` gives the meanings of the symbols whose clauses are
guarded several times (the result of an `ite`, an `and` or an `or`, a merged
call, the typing of a value); a blocker means the conditions of its path, such
as `(and n c)` for `(= (and n c) b)`, or `(or b1 b2 ..)` for a merge; failing
these, a symbol that one clause `(=> n (= v t))` defines means `t`. The checker
states, for each `Unfold` and `Instance` rule, the definition `(= v D)` of each
of its symbols that has a meaning, with the rule's arguments for the
parameters, except the symbols that a `Define`, `Hypothesis` or `Root`
introduces, the targets of `Enables` rules, and the duplicates. Logos reads
them with the other clauses; nothing relies on how they were found.

Each definition is one more fresh-symbol step (`addDefinitions`), ordered with
the others so that each follows the steps that its term mentions; the
definitions that can't (those in a cycle with an `Enables` step, where the
start of an instance is enabled by a blocker whose definition mentions a symbol
of that instance) are left out, and their clauses stay facts. The check decides
that the steps are fresh, as for the others: together, they extend a `Good`
model to all the symbols of the instances, by the values of their meanings.

A clause of an instance then holds when, with the definitions of the instance's
symbols that are steps substituted (`substSmt`), it holds in every `Good` model
(`instClauseB`, deciding `verify`): an implication `(=> p q)` holds when `q`
holds under the literals that `p` being true makes known, for each disjunct of
`p`, or when `p` reduces to false under them; a term holds when it reduces to
`true` under the known literals (`red`: a known subterm is its value, an `ite`
whose condition reduces to a literal is its branch, Boolean operators of
literals are reduced, and `(= x y)` is true when `x` and `y` reduce to the same
term); and an instance of a defining equation holds. So a result defined under
the guards of both branches, `(=> b1 (= e t1))` and `(=> b2 (= e t2))`, becomes
`(=> (and n c) (= (ite c t1 t2) t1))`, which holds since the guard makes `c`
known; and the value of a nested call, `(=> b (= lt (f' args)))`, is that call.
[`Inox/Instances.lean`](Inox/Instances.lean) proves it: `eval_red`,
`verify_sound`, and, since a definition that holds gives its constant the value
of its term (`defBinding_sound`), interpreting the constants as those values
leaves the model unchanged (`setConsts_self`), so the substituted clause has
the value of the clause (`eval_subst`). `r.covered` is `unfoldB` or a clause of
an instance that the check accepts:

```lean
theorem holds_instanceFact (hty : LogosTyping) {r : TermSteps} {t : Term}
    (ht : t ∈ r.instanceFacts) {assums : List Term} (hsub : extend r.base r.fresh ⊆ assums) :
    Holds (Good r.equations) assums t

theorem no_good_model_of_instances (sound : LogosSound) (hty : LogosTyping)
    {certificate : Sexp} {checked : Checked} {r : TermSteps}
    (hAccept : accept certificate = .ok checked) (hr : termSteps checked = .ok r)
    (hcheck : r.check = true) (hkeeps : r.keeps = true)
    (hfacts : FactsHoldExcept (Good r.equations) r.covered (extend r.base r.fresh) r.facts) :
    ∀ M, Good r.equations M → ¬ Satisfies M r.base
```

`inox-check --terms` prints, for each certificate, how many facts are
unfoldings, how many are clauses of instances that the check accepts, and how
many remain, by category: `decreases` (the clauses of the `diverges!` symbols),
`contract` (the clauses of an `Unfold` rule that are not about its symbols'
meanings: preconditions, postconditions, ADT invariants, refinements),
`assertion` (`Instance` rules), `typing` (the `tp!` predicates),
`definition without source` (a template whose source is not a function),
`binder`, `completeness`, and the other rules by kind; and how many definitions
of local symbols are steps. `--remaining` prints the remaining facts and the
definitions left out. On the 31 regression certificates that Logos reads, 1,124
of the 1,871 facts are covered (24 unfoldings, 1,100 clauses of instances), and
776 of the 805 definitions are steps.

The soundness of Logos is a hypothesis of the theorems, `LogosSound`, which is
the statement of Logos's own theorem. They then only need the definitions of
Logos, and Mathlib for its reals: the [`verification`](verification) project
builds them in minutes, and the `Lean proofs` workflow does when this directory
changes.

```sh
cd proofs/lean/verification && lake exe cache get && lake build
```

[`Inox/Closed.lean`](Inox/Closed.lean) discharges the hypothesis with the
theorem of Logos. It needs the proofs of Logos, which take hours to build, once
for each version of Logos (the workflow builds it when run by hand with
`closed`):

```sh
cd proofs/lean/verification && lake build InoxClosed
```

## What is not proved yet

- **The rules that are facts.** `no_good_model_of_accept` covers the rules that
  introduce fresh symbols, and `no_good_model_of_instances` the unfoldings and
  the clauses of instances that hold by the meanings of their symbols. The
  theorem to come is the one of an UNSAT answer in
  [`semantics.md`](../semantics.md): the query has no solution. It needs the
  semantics of Inox in Lean, that its solutions give `Good` models, and for
  each other kind of rule, that its clauses hold in them (`hfacts`): the
  decreases clauses; the preconditions, postconditions, ADT invariants and
  refinements of the templates (`contract`), which are assumptions about the
  program; the assertions of `Instance` rules; the typing predicates; the
  templates whose source is not a function; the clauses with binders; and the
  other rules (`Dispatched`, `Congruence`, `SameLambda`, …).
- **Longer cycles of `Enables` rules.** A cycle where a target reaches a
  definition that enables it only through other definitions or targets
  (`bs := (and d s)`, `(=> m s)`, `(=> bs2 m)`, `bs2 := (and d2 x)`,
  `d2 := (or bs y)`) has no order in which each step is fresh. Its targets
  would need to be introduced together, as the least model of the `Enables`
  clauses of the cycle given the definitions, which are monotone in them.
- **The sources of the templates.** The checker lowers the source of every
  template to the syntax of the session, as the Scala checker does
  ([`Lowering.lean`](Inox/Lowering.lean), a port of
  [`Lowering.scala`](../src/main/scala/inox/certificates/Lowering.scala)), and
  refuses a certificate with a source that doesn't lower. Only the Scala
  checker checks that the clauses of a template are those of its source
  ([`Sources.scala`](../src/main/scala/inox/certificates/Sources.scala)); this
  checker only checks the clauses that it covers against the lowered source
  (`unfoldB`, and the clauses of instances, given the meanings of their
  symbols).
- **The link between the proof and the script.** The checker checks that each
  assumption of the proof is the text of an assert of the script, up to how
  cvc5 prints testers (`(is C e)` for `((_ is C) e)`), once the terms that the
  proof defines are in place. The theorem is about the assumptions as Logos
  reads them.

As for Logos itself: its parser is not verified, it doesn't read the constant
arrays of Inox's maps and bags, which are in cvc5's expert signature (the
checker then checks the rules, and Ethos the proof), and it reports a proof
outside of what its theorem covers as `incomplete`, which `inox-check` refuses.
