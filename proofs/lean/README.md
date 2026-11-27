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
the query's assumptions, of each rule in order, of the completeness
assumptions, of the definitions of local symbols, then of the source
expressions of the assertions), parses that text with Logos, and makes a step
of each rule: a `Define`, `Hypothesis` or `Root` introduces its literal, the
`Enables` rules of a target together introduce it, and the other rules are
facts. The base clauses `r.base`, those that the models considered satisfy, are
the query's assumptions, the source expressions and the completeness
assumptions (see below). An `Enables` clause `(=> b m)` whose blocker `b` has a
`Define` `(= b rhs)` of which `m` is a conjunct (an operand of `rhs`'s `and`)
is not a blocker of `m`'s step but a derived clause: it holds in every model of
that definition (`holds_derived`), and it comes after the steps. This breaks
the cycles where a conjunction of targets enables one of them
(`bs := (and m0 m2)` with `(=> bs m0)`): `m0` is introduced by its other
blockers, then `bs`, then the clause. `TermSteps.check`
([`Inox/Terms.lean`](Inox/Terms.lean), which `inox-check --terms` runs) decides
that each fresh-symbol step can follow those before it, that the definition of
each derived clause is among them, and that every assumption of the proof is a
clause. It takes time linear in the size of the clauses, up to hashing:
freshness is decided against the set of the names of the constants that the
clauses before mention (`NamesCover`), and the definitions and the clauses are
looked up in hash sets, whose lemmas make the lookups equalities:

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

The clauses of an `Enables` step, `(=> b c)` for each blocker `b`, don't say
that the activation literal `c` holds only if one of its blockers does. The
model that the steps build does have it, since it makes `c` the disjunction of
the blockers and the later steps don't reinterpret them (`Step.Only`,
`extend_sat_only`). `no_good_model_of_accept_only` is the same theorem with the
facts only asked of such models, so that a fact about a call can go from its
activation literal to the blockers of the paths that reach the call:

```lean
    (hfacts : FactsHold (fun M => Good M ∧ ∀ st ∈ r.fresh, st.Only M)
      (extend r.base r.fresh) r.facts) :
```

The theorem without `Total` uses it (`no_solution_of_reached`, below).

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
term); and an instance of a defining equation holds. The known literals include
those that a true disjunction with an operand that reduces to false makes
known, those of its other operand (`unitLits`, `kSound_unitLits`): on the
branch of `(or b t)` where `b` is false, a query that states the disjunction
makes `t` known. So a result defined under the guards of both branches,
`(=> b1 (= e t1))` and `(=> b2 (= e t2))`, becomes
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

### The statement: the query, its expressions, the completeness assumptions

The base `r.base`, which the theorems say no `Good` model satisfies, is:

- the query's `check-sat` assumptions;
- the source expressions of the assertions: for each `Instance` rule with the
  argument `expression` whose template's source is `(expression t)`, the term
  `t` with the rule's arguments for the template's parameters
  (`Checked.expressions`; testers printed as cvc5 does). These are the formulas
  that the query asserts, which the certificate refutes, as
  `Lowering.Tables.statement` states them (see below);
- the completeness assumptions that the certificate declares under
  `(assumptions (complete …))`, which are assumptions on the models considered,
  not facts to prove.

The source expressions are in SMT-LIB 3, with markers and assumptions, which
Logos doesn't read. The base has each one lowered to the syntax of the session
(`Inox/Lowering.lean`), with the meaning that its `where` gives to each marker
(a typing `((as typing!0 S) "free" x)`, for one) in place of the marker, the
conjuncts that still have markers left out, of the expression and of the
conditions of its assumptions, and each `(assume c b)` replaced by `b`; an
expression with a marker left elsewhere is left out of the base. So the base's
clause is implied by the source expression, given the meanings of its markers:
the theorems' hypotheses are weaker than the query's assertions with their
assumptions, and the theorems stronger than about the assertions themselves.
That the meanings of the markers are those that the source gives them, and that
a typing's meaning is what the template's clauses state of the marker, is only
checked by the Scala checker (`Sources.scala`); neither checker checks that the
meaning of a typing is that of the type.

Of the latter two, those that mention a constant that a rule introduces (a
fresh symbol, whose value the steps choose) can't be assumptions of a model of
the query: such a completeness assumption stays a fact, and such a source
expression is left out of the base. The clauses of an assertion's instance are
then checked as those of a function's, given the base: the literals that the
base clauses and the constants of the root steps make known
(`TermSteps.baseLits`, by `lits`) are known to `verify` in each clause
(`instClauseB`, `kSound_baseLits`), so the meanings of the instance's symbols,
substituted, reduce under the source expression.

So the final theorem (`no_good_model_of_instances`) reads: for each model `M`
that is well formed and satisfies the defining equations `r.equations`
(`Good`), `M` does not satisfy at once the query's assumptions, the source
expressions of its assertions and the completeness assumptions, given that the
facts that remain hold in the `Good` models (`hfacts`). `r.equations` are the
defining equations of the program's functions and the reflexivity axioms below.

### The rules that hold in every model

A fact that `verify` accepts as it is, given the literals of the base clauses,
holds (`TermSteps.verified`, `holds_verified`). Besides reduction, `verify`
accepts:

- **Congruence** (`congEq`, `congB_sound`): `(= x y)` where `x` and `y` are the
  same term, or their equality is a known literal (of a sort other than regular
  languages, whose equality is not that of their values), or they are
  applications of the same function, or of functions that are equal by
  congruence and are not selectors or testers, to arguments equal by
  congruence. This holds in every well-formed model, since evaluation is a
  function of the values of the subterms. The `Congruence` facts of the
  certificates that remain are equalities of the instances of quantifiers
  (`(= inst!1 inst!0)`), whose argument equalities are not clauses; no
  `Symmetry` or `Transitivity` facts occur.
- **Modus ponens on the defining equations** (`mpInst`, `mpInst_sound`): `q`
  when a defining equation, with the last arguments of `q` for its parameters,
  is `(=> A q)` and `A` reduces to true under the known literals.
- **Reflexivity**: the `Reflexivity` facts are `(=> (and g (= a b)) (eq a b))`
  for an `eq` that applies the program's equality on a type
  (`(dynLambda!2 |eqBag[BigInt]!0| a b)`). It is not valid in every model: `eq`
  is made of symbols of the query. From the certificate's `Reflexivity` rules,
  the checker states, once for each such `eq`, the axiom
  `(=> (= x y) (eq x y))` over two new constants as a defining equation
  (`reflexivities`), when `eq` is made of constants of the query whose names
  Logos does not reserve (`constApp`; a built-in relation such as `<` would
  leave no `Good` model) and it mentions no fresh symbol. So the `Good` models
  are those where `eq` is reflexive, and the facts are its instances by modus
  ponens. That this holds of the program's equality is a fact about Inox, as
  the defining equations are.
- **Decreases**: a decreases clause is `(=> b (or (> r r') diverges))`, where
  `r` and `r'` are the ranks of a call and of a call of its body, and nothing
  else constrains `diverges`. So it is a fresh symbol that may be true: the
  checker adds a root step for each constant that ends the disjunction of a
  fact and that neither the base clauses, the equations, the other steps nor
  the definitions mention (`unconstrained`), which the check of the steps
  decides as for any other. The constants of the root steps are then known
  literals (`TermSteps.roots`, `roots_subset_extend`), under which the clause
  reduces to true. The clauses say nothing of the termination of the calls,
  which the theorems about the semantics take as a hypothesis (`Total`) or do
  without, for the calls that evaluation goes through
  (`no_solution_of_reached`).
- **The typing of a set**: a variable or a parameter of a type of sets has
  clauses for the typing of its elements,
  `(=> nonEmpty (= s (set.union (set.insert e empty) rest)))` with the typing
  of `rest` in turn, where `e` and `rest` are symbols of the template that
  nothing else constrains: any element of a set that is not empty and the
  others. The source gives the typing as
  `(ite (= s empty) true (assume (= s (union {e} rest)) typing(rest)))`, which
  `Meanings.setTyping` recognises: it reads `e` as `(set.choose s)`, the
  element that Logos chooses of `s`, `rest` as
  `(set.minus s (set.singleton e))`, and the typing as `true`. These are
  definitions of fresh symbols like the others, and the clause is then the
  split of a set that its guard makes known not to be empty, which `verify`
  accepts (`setSplit`, `setSplit_sound`, by `choose_mem` and `split_eq` of
  [`Inox/Sets.lean`](Inox/Sets.lean)). The typing of the rest is a parameter of
  the instance that unfolds it, so the definitions of the symbols that are
  `true` are in place in the clauses of every instance. This is for the sets
  whose elements have no typing of their own.
- **The symbols that other instances mention**: a symbol of an instance may be
  in an argument of another, as the typing of the rest of a set is, or the
  value of a constructor with an invariant, `adt`, which the query defines and
  the calls take. So the definitions of the symbols that are `true`, and of
  those that name a value over no defined symbol, are in place in the clauses
  of every instance (`TermSteps.shared`), and the definitions are put in place
  twice (`subst2`, `eval_subst2`), since a definition of an instance may
  mention such a symbol. `Paths` reads the definitions of the blockers with
  them in place too (`sharedBindings`).

`inox-check --terms` prints, for each certificate, how many facts are
unfoldings, how many are clauses of instances that the check accepts, how many
hold as they are (by rule kind), and how many remain, by category: `decreases`
(the clauses of the `diverges!` symbols that are constrained), `contract` (the
clauses of an `Unfold` rule that are not about its symbols' meanings:
preconditions, postconditions, ADT invariants, refinements), `assertion`
(`Instance` rules), `typing` (the `tp!` predicates),
`definition without source` (a template whose source is not a function),
`binder`, `completeness`, and the other rules by kind; how many definitions of
local symbols are steps; the base: how many of its clauses are the query's, how
many of the source expressions and completeness assumptions are base clauses;
and how many reflexivity axioms. `--remaining` also prints the remaining facts
and the definitions left out. On the 31 regression certificates that Logos
reads, 1,825 facts remain once the 46 completeness assumptions are in the base,
and 1,360 are covered (24 unfoldings, 1,311 clauses of instances, of which the
180 decreases clauses, 25 directly: 12 `Reflexivity`, 13 `Congruence`); 30 of
the 32 source expressions are base clauses, and 771 of the 805 definitions are
steps (5 fewer than without the source expressions and completeness assumptions
in the base, which mention their symbols).

The soundness of Logos is a hypothesis of the theorems, `LogosSound`, which is
the statement of Logos's own theorem. They then only need the definitions of
Logos, its proof that a well-formed model exists, and Mathlib for its reals and
their cardinality: the [`verification`](verification) project builds them in
minutes, and the `Lean proofs` workflow does when this directory changes.

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

## The bridge to the semantics (partly proved)

The theorem of an UNSAT answer is about Inox's semantics: no values of the free
variables make the query evaluate to `(Ok true)`. The semantics is
[`semantics.md`](../semantics.md), and its Lean form,
[`proofs/semantics/Inox/Semantics.lean`](../semantics/Inox/Semantics.lean), is
generated from it, as its Scala form is (`inox.semantics.Codegen`): the
inductive types `Value`, `Expr`, `Ty`, `Program` and `Env` of its `inox-sem`
blocks, and total definitions `eval O P fuel env e` and
`call O P fuel f tps tenv vs`, by well-founded recursion on `fuel.toNat`. They
are relative to an oracle `O` for the functions that quantify over values, and
`O.Sound` states that it gives them as the semantics defines them. The checker
and Logos, on the other side, work on SMT-LIB terms and on `SmtValue`s. This
section says what connects them. The proved part is the first-order fragment of
integers, Booleans, reals, bit-vectors, datatypes without type parameters and
sets, against the generated evaluator (see [What is proved of it so
far](#what-is-proved-of-it-so-far)).

### The fragment

The first-order core: `Variable`, `Let`, the literals of integers, Booleans and
unit, `IfExpr`, `And`, `Or`, `Implies`, `Not`, `Equals` on values that are not
closures, `FunctionInvocation` without type arguments, `ADT` without type
arguments, `IsConstructor`, `ADTSelector`, `Assume` and `Error`, in a program
whose functions have no type parameters and whose sorts may have invariants.
Lambdas, applications, quantifiers, sets, bags, maps, strings, reals,
bit-vectors and floating point come after it. Each needs the same three pieces:
a translation, a case of the agreement theorem, and the clauses of its
templates.

### The translation

A translation `tr Γ` from the semantics to Logos, for this fragment:

- types: `IntegerType` to `Int`, `BooleanType` to `Bool`, `UnitType` and
  `ADTType s []` to the datatype of the script's encoding, by name;
- values: `IntV i` to `Numeral i`, `BoolV b` to `Boolean b`, `UnitV` and
  `ADTV c vs` to the constructor `DtCons` of `c` applied to the translations of
  `vs`;
- expressions: a variable to the constant of its symbol (`UConst x T`, with `T`
  from `Γ`), `IfExpr` to `ite`, `And` and `Or` to nested `and` and `or`,
  `Implies`, `Not` and `Equals` to `=>`, `not` and `=`, an invocation of `f` to
  the application spine of `f`'s symbol, `ADT` to the constructor's, and
  `IsConstructor` and `ADTSelector` to the tester and the selector. `Let`
  becomes a fresh symbol bound in `Γ` with its definition, as the templates
  name it. `Assume` and `Error` have no term: they show up as clauses (see
  below).

`Γ` is needed because the semantics' expressions don't carry the types of their
variables: `FunDef` has `params (List Id)` and no types. The types come from
the certificate (below). The names come from the same place: the certificate's
symbols map back to Inox identifiers (`Proofs.scala`), and the translation is
that map read backwards.

### The intended model

Given a program `P` and a solution `σ` of the query, the intended model
`M(P, σ)` is the `SmtModel` that:

- gives each free variable of the query `tr σ(x)`;
- interprets the symbol of each function `f`, on the translations of values
  `vs` of its parameter types, by `tr v` when `call O P n f [] [] vs = Ok v`
  for some fuel `n` (unique by the fuel lemma), and by an arbitrary value of
  the return type otherwise;
- interprets a function symbol of arity `k > 1` applied to fewer arguments as a
  `Fun` value whose code names the function and the arguments so far, so that
  `__smtx_model_eval_apply` reaches the call when the last one comes;
- interprets sorts, constructors, selectors and testers as Logos does.

[`Inox/Model.lean`](Inox/Model.lean) builds this model over an arbitrary
interpretation `interp` of the functions, and proves it well formed whatever
`interp` is. The bridge instantiates `interp` with `call`. It takes one fact as
a parameter: an injection of names, types and argument lists into the nonzero
codes of `Fun` values (`Codes`). One exists (`Codes.nonempty`,
[`Inox/Codes.lean`](Inox/Codes.lean)): `ModelId` is `ℝ`, the sorts are
countable, and a value is written injectively as a list of reals and naturals
(`ser_inj`), so there are no more partial applications than reals.

### The agreement theorem

For `e` in the fragment, well-typed in `Γ`, and `env` matching `Γ`: if
`eval O P n env e = Ok v`, then Logos evaluates `tr Γ e` in `M(P, σ)`, with the
constants of `Γ` set to `tr env`, to `tr v`.

It is proved by induction on `n` and then on `e`. The cases follow `eval`'s
equations: the connectives because `Ok` means the operands needed were `Ok`,
which is what Logos's total `and`/`or` need on the values; invocations because
`call` is `Ok` with the same fuel, so the model's interpretation is that value.

Only `Ok` results say anything. `Stuck` and `OutOfFuel` give no value, and the
translated term may then have any value in the model. This is where the rest of
the certificate comes in.

### Where `Stuck` and `OutOfFuel` show up

- **The defining equations.** `Good` asks that each function's equation
  `(= (f x1 … xn) body)` hold for all arguments. In `M(P, σ)` it holds where
  `call O P n f [] [] vs` is `Ok` for some `n`. Elsewhere the interpretation is
  arbitrary, and so the equation may fail. For a program whose functions
  terminate and never get stuck on values of their parameter types, `M(P, σ)`
  is `Good`, and the current theorems apply to it as they are, with the facts
  that remain as their hypothesis. In general, `Good` has to be relativized to
  the calls that are `Ok`. The rules of the templates only use the equation of
  a call under the blocker that guards it. A blocker holds iff evaluation
  reaches its path (`RuleKernel`), and a call reached on the way to `Ok true`
  is itself `Ok`.
- **Contracts** (`Assume`, `Error`, invariants, partial operations). These are
  `Stuck` in the semantics. In the certificate they are clauses that say the
  condition holds on the path that reaches it. In a solution, every reached
  `Assume` holds and every reached constructor satisfies its invariant, since
  otherwise evaluation would be `Stuck`, not `Ok true`. So the contract clauses
  hold in `M(P, σ)` under the blockers' intended meaning. To prove that, the
  agreement theorem's induction has to carry the blockers: each blocker is true
  in the model iff `eval` reaches the guarded subexpression with `Ok` results
  so far.
- **Decreases** (`diverges`, ranks). `OutOfFuel` for every fuel is divergence.
  The decreases clauses give each call a rank from the termination measure, and
  `diverges` stands for calls that may not terminate. Their intended meaning
  is: the rank of a call bounds the fuel its evaluation needs, and `diverges`
  is false exactly when every reached call has a rank. With it, a reached call
  of a solution is `Ok` at fuel equal to its rank. The checker needs this so
  that the relativized `Good` covers every call that the rules use.

### What the certificate has to carry

Today the sources are SMT terms, `(function (f x1 … xn) body)` and
`(expression t)`. To tie them to the semantics, the certificate needs:

- the program `P` as a value of the semantics' `Program`, printed as the
  `inox-sem` datatypes' s-expressions;
- the query as an `Expr`, with its free variables and their types;
- a typing environment for the translation: the parameter and return types of
  each function, and the field types of each constructor;
- the map between the script's symbols and the program's identifiers (the
  `Sym`s already hold it).

The checker would then check that each `(function …)` source is `tr` of the
function's body in `P`, and that each `(expression …)` is `tr` of the query.
One gap remains: the body in a source is the one the solver unfolds, after its
simplifications. Either the certificate gives the unsimplified body, or the
simplifications have to be shown to preserve `eval`. The first is simpler.

### What the proofs need from the generated Lean

The generated file already gives the form the proofs need. `eval`, `eval_list`,
`call` and `apply` are ordinary definitions, not `partial` ones, so their
equation lemmas (`eval.eq_def`) unfold them; since the recursion is
well-founded, `rfl` and `decide` don't. There is one inductive per `datatype`
and one constructor per constructor, with the names of `semantics.md`, `Id` is
`String`, and `Result` is its own inductive. The functions that quantify over
values or compare closures (`forall_result`, `closures_equal`, `value_eq`, the
typing of values) are fields of the oracle, so a theorem about `eval` assumes
`O.Sound` where it reaches them.

What is still missing:

- **Fuel monotonicity.** "More fuel never changes a result other than
  `OutOfFuel`" is the lemma the intended model needs, since it makes a call's
  value independent of the fuel that finds it. It is proved for the fragment
  (`Inox/Mono.lean`), by induction over `eval`'s cases against the generated
  definitions, and is still missing for the rest of `eval`.

### What is proved of it so far

**The intended model** ([`Inox/Model.lean`](Inox/Model.lean)). A program is a
signature: each `Def` has the constant it defines (`name`, `ty`), its `params`
and its `ret` sort. Over `interp : Def → List SmtValue → SmtValue`, a model
`M0` for the sorts and the other function values, a model `N` for the free
variables, and `cd : Codes`, `star P interp M0 cd N` interprets:

- a constant that `d` defines by `interp d []` if `d` has no parameters, and
  otherwise by the function value `funVal cd d []`, of sort
  `arrow d.params d.ret`, whose code is `cd.code d.name d.ty []`;
- the function value that codes `d` applied to `vs`, applied to `i`, by
  `funVal cd d (vs ++ [i])` while parameters remain, and by
  `interp d (vs ++ [i])` once none do (`applied`);
- everything else as `N` (the values of constants) and `M0` (function values,
  sorts) do.

Where `interp` doesn't give a canonical value of the expected sort (the
evaluation is stuck, out of fuel, or ill-typed), the model falls back to `N` or
`M0` (`typedOr`). So it is a model for any `interp`:

```lean
theorem wf_star (hwf : model_wf M0) {N : SmtModel} (hN : model_wf N)
    (hu : N.usortDom = M0.usortDom) : model_wf (star P interp M0 cd N)
```

and `star_def`, `fns_code` and `star_undef` state that it interprets the
constants and the partial applications as above, where `interp` gives a
canonical value of the expected sort.

**`Good` relativized** ([`Inox/Relative.lean`](Inox/Relative.lean)). For a
predicate `ok` on equations and argument values (for the bridge: the calls that
are `Ok`), `GoodOn ok eqs M` asks that each equation evaluate to a Boolean for
all arguments of its parameter types, and to `true` for those that `ok`
selects. `Good` is the case `ok = fun _ _ => True` (`good_iff_goodOn`). An
unfolding `(=> g s)` of an equation holds in the `GoodOn` models when its guard
only selects calls that `ok` selects:

```lean
def GuardOk (ok : Equation → List SmtValue → Prop) (eqs : List Equation)
    (assums : List Term) (c : Term) : Prop :=
  ∀ M, GoodOn ok eqs M → Satisfies M assums →
    ∀ g s, __eo_to_smt c = SmtTerm.imp g s →
      __smtx_model_eval M g = SmtValue.Boolean true →
      ∀ e ∈ eqs, ∀ us, instB e g s us = true →
        ok e (us.map (__smtx_model_eval M))

theorem no_good_model_of_unfold_on (sound : LogosSound) (hty : LogosTyping)
    (ok : Equation → List SmtValue → Prop)
    {certificate : Sexp} {checked : Checked} {r : TermSteps}
    (hAccept : accept certificate = .ok checked)
    (hr : termSteps checked = .ok r)
    (hcheck : r.check = true) (hkeeps : r.keeps = true)
    (hfacts : FactsHoldBy (GoodOn ok r.equations)
      (GuardedUnfold ok r.equations) (extend r.base r.fresh) r.facts) :
    ∀ M, GoodOn ok r.equations M → ¬ Satisfies M r.base
```

where `GuardedUnfold ok eqs assums t` is
`unfoldB eqs t = true ∧ GuardOk ok eqs assums t`, and `FactsHoldBy` asks each
fact to hold in the `GoodOn` models or to be justified so.
`no_good_model_of_unfold_on_closed` ([`Inox/Closed.lean`](Inox/Closed.lean))
discharges `sound` and `hty`.

The guard obligation is the blocker meaning of [Where `Stuck` and `OutOfFuel`
show up](#where-stuck-and-outoffuel-show-up): a guard that is true in the
intended model selects a call that evaluation reaches, and so one that is `Ok`.
Proving it needs the agreement theorem. The instance and verified facts of
`no_good_model_of_instances` are not relativized yet: their proofs use the
equations at the instance's arguments without a guard, so restating them needs
the same obligation at each use of an equation. The gap is large: on the
regression corpus, `no_good_model_of_unfold_on` covers the 24 unfoldings of the
1,360 facts that `no_good_model_of_instances` covers, and the other 1,336 stay
in `hfacts`.

**Fuel monotonicity** ([`Inox/Mono.lean`](Inox/Mono.lean)), against the
generated `eval` of [`proofs/semantics`](../semantics). `Le r r'` is
`r = OutOfFuel ∨ r' = r`. For a program whose function bodies are in `Frag`
(`ProgFrag`), and for `e` in `Frag`:

```lean
theorem eval_mono (hP : ProgFrag P) (hnm : n ≤ m) {e : Expr} (he : Frag e)
    (env : Env) : Le (eval O P n env e) (eval O P m env e)
theorem call_mono' (hP : ProgFrag P) (hnm : n ≤ m) (f tps tenv vs) :
    Le (call O P n f tps tenv vs) (call O P m f tps tenv vs)
```

with `eval_ok_mono` and `call_ok_mono` for `Ok` results. `Frag` covers
`Assume`, `Variable`, `Let`, `Lambda` (a value, so fuel-independent), `Error`,
`FunctionInvocation`, `IfExpr`, the literals of characters, bit-vectors,
integers, fractions, Booleans, strings and unit, `ADT`, `IsConstructor`,
`ADTSelector`, `Equals`, `And`, `Or`, `Implies`, `Not`, `Plus`, `Minus`,
`UMinus`, `Times`, `Division`, `Remainder`, `Modulo`, `LessThan`,
`GreaterThan`, `LessEquals` and `GreaterEquals`. It leaves out `Application`
(it calls the closure's body through `apply`), `Forall` and `UninterpretedCall`
(they go through the oracle and classical choice), the floating-point literals
and rounding modes, and the string, bit-vector and floating-point operations.

**The agreement theorem** ([`Inox/Bridge.lean`](Inox/Bridge.lean)). The
translation is for integers, Booleans, reals, bit-vectors, datatypes without
type parameters and sets ([`Inox/Data.lean`](Inox/Data.lean)). `D : List Data`
gives each datatype its name, its declaration in Logos and its constructors
with their fields. `trT D` sends `IntegerType`, `BooleanType` and `RealType` to
`Int`, `Bool` and `Real`, `BVType s w` to `BitVec w`, whatever the sign `s`,
and `ADTType d []` to the datatype of `d`, `trV D` sends `IntV i` and `BoolV b`
to `Numeral i` and `Boolean b`, `RealV n d` to the real number of the fraction
`n / d`, `BVV s w x` to `Binary w x` and `ADTV c vs` to the constructor of `c`
applied to the translations of `vs`, and `tr D S Γ e` sends an expression to a
Logos term: a variable `x` of type `T` in `Γ` to `UConst (nm x) (trT D T)`, an
invocation of `f` to the application spine of `f`'s constant, `ADT`,
`IsConstructor` and `ADTSelector` to the constructor, the tester and the
selector of Logos, which are indices into the declaration, a `FractionLiteral`
to the division of its integers, as Inox prints it (`(/ (- 1) 2)`), and the
operators to their SMT-LIB counterparts. Those of the integers are also those
of the reals, except `/` for `Division`, and the bit-vectors have others
(`bvadd` for `Plus`, `bvudiv` or `bvsdiv` for `Division`, `bvult` or `bvslt`
for `LessThan`): `isBv`, `isSigned` and `isReal` say which an expression is of,
from its variables, its literals and the signatures. `S : List Sig` gives each
function its parameters and return type, which the semantics' `FunDef` doesn't
carry. `HasTy D S Γ e T` is the typing of the fragment: variables, the integer
and Boolean literals, `IfExpr`, `And`, `Or`, `Not`, `Implies`, `Equals`,
`Plus`, `Minus`, `Times`, `Division`, `Remainder`, `Modulo`, `UMinus`,
`LessThan`, `GreaterThan`, `LessEquals`, `GreaterEquals`, `Assume`,
`FunctionInvocation` without type arguments of a function of `S`, the literals
of the reals, with a denominator that is not zero, with `Plus`, `Minus`,
`Times`, `Division`, `UMinus` and the four comparisons on them, the literals of
the bit-vectors with `Plus`, `Minus`, `Times`, `Division`, `Remainder`,
`Modulo`, `UMinus`, `BVNot`, `BVAnd`, `BVOr`, `BVXor`, the three shifts and the
four comparisons on them, signed or not, `BVUnsignedToSigned` and
`BVSignedToUnsigned`, which translate to their operand, `BVNarrowingCast` to a
smaller width and `BVWideningCast` to a larger one, and `ADT`, `IsConstructor`
and `ADTSelector` of a constructor or a field of `D`. A bit-vector of the
semantics is its unsigned integer with a sign, which says how the division, the
remainder, the modulo and the comparisons read it, and Logos defines the signed
operators of SMT-LIB from the unsigned ones by the cases of the top bits:
[`Inox/Signed.lean`](Inox/Signed.lean) proves that they agree (`bvsdiv_eq`,
`bvsrem_eq`, `bvsmod_eq`, `bvsgt_eq`, `bvsge_eq`). The two signs have one sort.
[`Inox/Bits.lean`](Inox/Bits.lean) proves the agreement of the bitwise
operators, which the semantics defines by recursion on the bits and Logos by
those of `BitVec` (`bvand_eq`, `bvor_eq`, `bvxor_eq`), of the shifts, where the
semantics cuts the amount at the width and the arithmetic one of Logos is by
the cases of the top bit (`bvshl_eq`, `bvlshr_eq`, `bvashr_eq`), and of the
casts, which Inox prints as `extract`, `sign_extend` and `zero_extend`
(`extract_eq`, `sign_extend_eq`, `zero_extend_eq`). `BVToInt` and `IntToBV` are
not there. The reals of the semantics are the fractions in lowest terms, and
those of Logos the real numbers: the operators agree on the fractions
(`real_eq`, `ratOf_add` and the like), and a real number that is not a fraction
is the translation of no value. `DataOk D` asks that the names of the
datatypes, of the constructors and of the fields be distinct, that the fields
have types of the fragment, and that each declaration be well-formed and the
one that Logos types its datatype with. Under it a value translates to a value
of Logos of its type (`typed_trV`), each canonical value of Logos of a type
without reals (`NoReal`), in datatypes without real fields (`RealFree D`), is
the translation of one (`typed_inv1`), and `value-eq` on two values of a type
says whether they are the same value of Logos (`value_eq_hasV`). `ProgData D P`
says that the program has the constructors and the sorts of `D`, without
invariants. For a model whose function constants agree with `call` at fuel `n`
(`CallsOk`) and whose variable constants agree with the environment (`VarsOk`):

The sets are those of a type of the fragment: `trT D` sends `SetType A` to
`Set` of the sort of `A`, and `HasTy` has `FiniteSet` of no element or of one,
`SetAdd`, `ElementOfSet`, `SubsetOf`, `SetUnion`, `SetIntersection` and
`SetDifference`, which `tr` sends to `set.empty`, `set.singleton`, the union
with a singleton, `set.member`, `set.subset`, `set.union`, `set.inter` and
`set.minus`. Inox prints a set of several elements as insertions into a set of
one or of none, which is how the certificate is read: as `SetAdd`s. A set of
the semantics is the list of its elements in the order of their insertion, with
the type of its elements, and a set of Logos is a map to the Booleans whose
entries are sorted and none of which is the default, so that two sets with the
same elements are the same value. [`Inox/Sets.lean`](Inox/Sets.lean) builds the
set of Logos of a list by inserting its elements (`setOf`) and proves that it
is canonical, that its members are those of the list and that it depends on
them only (`setOf_lookup`, `setOf_ext`), that the operators of Logos on such
sets are those of the lists (`union_eq`, `inter_eq`, `minus_eq`, `member_eq`,
`subset_eq`), and that every canonical set of Logos is the set of the list of
its keys (`set_inv`). `trV D` sends `SetV A xs` to the set of the translations
of `xs`. Two lists with the same elements in another order are two values of
the semantics with one translation, so the translation is no longer injective:
`value-eq` on them is true, the agreement theorem is up to it, and the function
of the intended model is well defined because the calls to values with the same
translations give values with the same translation (`call_congr`: the value of
a call is that of the term of its body in a model that depends on the
translations of the arguments only, by the agreement theorem and induction on
the fuel).

```lean
theorem ev (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S)
    (hPD : ProgData D P) {n : Int} (hct : CallTy O P D S n)
    {Γ : List (Id × Ty)} {e : Expr} {T : Ty} (h : HasTy D S Γ e T) :
    Ev O P D S n Γ e T
-- Ev: eval O P n env e = Ok v → HasV D v T ∧
--   ∀ M, model_wf M → CallsOk O P D S n M → VarsOk D Γ env M →
--     __smtx_model_eval M (tr D S Γ e) = trV D v
```

The intended model is `Model.star (defs D S) (interpOf O P D S) M0 cd N`, with
`interpOf` giving the function of `s` on `vs.map (trV D)` the value of
`call O P n s.name [] [] vs` for some fuel `n` where it is `Ok` (unique by fuel
monotonicity, and the same for the values with these translations, by
`call_congr`). `callsOk_star` shows that it satisfies `CallsOk` at every fuel.
`goodOn_star` then shows that it satisfies the defining equations (the equation
of `s` relates the spine of its constant to `tr D S s.params body`, `EqFor`) on
the arguments where the calls give values (`okCall`), and so:

```lean
theorem no_star_model (sound : LogosSound) (hO : O.Sound) (hty : LogosTyping)
    (hS : SigOk D S) (hPF : ProgFrag P) (hP : ProgTy D S P)
    (hAccept : accept certificate = .ok checked)
    (hr : termSteps checked = .ok r)
    (hcheck : r.check = true) (hkeeps : r.keeps = true)
    (hE : ∀ e ∈ r.equations, ∃ s ∈ S, EqFor P D S s e)
    (hfacts : FactsHoldBy (GoodOn (okCall O P D S) r.equations)
      (GuardedUnfold (okCall O P D S) r.equations)
      (extend r.base r.fresh) r.facts)
    (cd : Codes) (hM0 : model_wf M0) (hN : model_wf N)
    (hu : N.usortDom = M0.usortDom) :
    ¬ Satisfies (Model.star (defs D S) (interpOf O P D S) M0 cd N) r.base
```

`GuardOk (okCall O P D S)` is discharged for programs whose functions all
terminate on values of their parameter types (`guardOk_total`). For others it
stays a hypothesis, inside `hfacts`.

**The calls that evaluation goes through have values**
([`Inox/Reach.lean`](Inox/Reach.lean)). A solution doesn't need every call to
give a value, only those that its evaluation goes through, and they do: a call
that is stuck or out of fuel makes the expression around it so. `reaches K c t`
decides on terms that evaluating the expression of `t` goes through the call
`c` in the models where the literals `K` have their values: `c` is `t`, or it
is reached in an operand that is evaluated. The operands of `ite`, `and`, `or`
and `=>` after the first are evaluated only when the first has the value that
selects them, which `red K` has to give.

```lean
theorem called_of_reaches (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S)
    (hP : ProgTy D S P) {n : Int} (hct : CallTy O P D S n) {Γ : List (Id × Ty)}
    {e : Expr} {T : Ty} (h : HasTy D S Γ e T) {env : Env} {v : Value}
    (hE : EnvTy D Γ env) (he : eval O P n env e = .Ok v) {M : SmtModel}
    (hw : model_wf M) (hc : CallsOk O P D S n M) (hV : VarsOk D Γ env M)
    {K : List (SmtTerm × Bool)} (hK : KSound M K) {c : SmtTerm}
    (hr : reaches K c true (tr D S Γ e) = true) : Called O P D S M c
```

`Called O P D S M c` says that `c` is a function of `S` applied to terms whose
values in `M` are those of values of its parameters' types, on which the call
is `Ok` at some fuel. `called_of_call` is the same of the body of a function
whose call is `Ok`, with the arguments of the call for its parameters.
`reaches` is `reachesW` with the terms as they are, and `reachesW` sees them
through a substitution, so that the body is compared with the terms of the
certificate without counting the calls of the arguments.

**The query has no solution** ([`Inox/NoSolution.lean`](Inox/NoSolution.lean)).
For a program whose calls all give values (`Total O P D S`: each function of
`S`, on values of the types of its parameters, is `Ok` at some fuel, and no
real is among the parameters and the fields of the datatypes, `Discrete D S`,
so that the arguments of a model are all values of the semantics), the intended
model satisfies the defining equations for all arguments
(`good_star`), so `no_good_model_of_instances` applies to it with all that it
covers, not only the unfoldings. A solution of the query gives the model `N`:
`varsModel D M0 Γ vs` sets the constants of the free variables `Γ` to their
values `vs`, and the intended model over it satisfies each base clause that is
the translation of an expression of the query that the solution makes true
(`satisfies_star`, by `ev` and `varsOk_star`). So:

```lean
def Solution (O : Oracle) (P : Program) (D : List Data)
    (Γ : List (Id × Ty)) (qs : List Expr) (vs : List Value) : Prop :=
  List.Forall₂ (HasV D) vs (Γ.map Prod.snd) ∧
    ∃ bs, bind_all (Γ.map Prod.fst) vs = .Ok bs ∧
      ∀ q ∈ qs, ∃ n, eval O P n (Env.Env [] bs) q = .Ok (.BoolV true)

theorem no_solution (sound : LogosSound) (hO : O.Sound) (hty : LogosTyping)
    (hS : SigOk D S) (hPF : ProgFrag P) (hP : ProgTy D S P)
    (htot : Total O P D S)
    (hAccept : accept certificate = .ok checked)
    (hr : termSteps checked = .ok r)
    (hcheck : r.check = true) (hkeeps : r.keeps = true)
    (hE : ∀ e ∈ r.equations, ∃ s ∈ S, EqFor P D S s e)
    (hΓ : VarsFresh D S Γ) (hbase : BaseFor D S Γ qs r.base)
    (hfacts : FactsHoldExcept (Good r.equations) r.covered
      (extend r.base r.fresh) r.facts) :
    ∀ vs, ¬ Solution O P D Γ qs vs
```

`BaseFor D S Γ qs base` says that each base clause is `tr D S Γ q` for a
Boolean expression `q` of the query, and `VarsFresh` that the free variables
have types of the fragment and are named after no function. This is the theorem
of an UNSAT answer for this fragment, up to its hypotheses: `Total`, the two
that relate the certificate to the program and the query (`hE`, `hbase`), and
`hfacts` for the facts that the check doesn't cover. A solution gives the free
variables values of the semantics, so a real variable a fraction: the theorem
says that the query has no rational solution, where the certificate shows that
it has no real one.

**The program and the query of a certificate**
([`Inox/Source.lean`](Inox/Source.lean)). `no_solution` is about a program and
a query, and asks that the equations and the base clauses of the certificate
are their translations. `no_solution_of_check` takes them from the certificate:
`back` reads a term of Logos as an expression, `dataOf r` is the datatypes that
its terms and their sorts mention, `programOf (dataOf r) r.equations` is the
program of their constructors and of the functions that the defining equations
read as, with the signatures `sigsOf r.equations`, and `queryOf r.query` the
expressions that the base clauses read as, over the free variables `varsOf`,
where `r.query` is the base with the assumptions that are inside the source
expressions marked, as for the bodies (see below). Logos names a constructor by
its datatype and its index, so the program has the constructors and their
fields under names made from these (`ctorName`, `fieldName`), not under those
of the script, and a sort `BitVec w` is read as the unsigned type, since
SMT-LIB has one sort for the two: a signed operator is read as the operator of
Inox on its operands turned signed (`BVUnsignedToSigned`), and `bvsdiv`,
`bvsrem` and `bvsmod` with their result turned unsigned. Nothing is proved of
`back`. Instead `sourceCheck r` translates what it gives and compares the
result with the terms, types the bodies and the query (`infer`, with
`infer_sound`), and checks the names, the types and the datatypes
(`dataCheck`), which gives `DataOk`, `ProgData`, `EqFor`, `BaseFor`, `SigOk`,
`ProgTy`, `ProgFrag` and `VarsFresh`:

```lean
theorem no_solution_of_check (sound : LogosSound) (hO : O.Sound)
    (hty : LogosTyping)
    (hAccept : accept certificate = .ok checked)
    (hr : termSteps checked = .ok r)
    (hcheck : r.check = true) (hkeeps : r.keeps = true)
    (hsrc : sourceCheck r = true)
    (htot : Total O (programOf (dataOf r) r.equations) (dataOf r)
      (sigsOf r.equations))
    (hfacts : FactsHoldExcept (Good r.equations) r.covered
      (extend r.base r.fresh) r.facts) :
    ∀ vs, ¬ Solution O (programOf (dataOf r) r.equations) (dataOf r)
      (varsOf (sigsOf r.equations) r.query) (queryOf r.query) vs
```

The program read is the one that the certificate states, as Logos reads it: its
names are those that Logos gives the constants, an n-ary operation is nested
with its unit (`(+ a b)` reads as `a + (b + 0)`), and a body is the one that
Inox unfolds, after its simplifications. That it is the program that Inox
answered about is what the certificate's sources state, and is not proved. A
call of a function without parameters is read as a variable, so the check
refuses a certificate that has one.

When the check of the certificate covers every fact (`r.facts.all r.covered`),
`no_solution_of_covered` has no hypothesis on the facts: what is left is
`Total` and the oracle.

On the certificates that Inox prints for two inputs of the fragment, a
recursive function over the integers and a recursive predicate with a query
that has free variables, the checker accepts and `sourceCheck` holds, and the
check covers every fact of both, so `no_solution_of_covered` applies. They are
not kept here. On the regression certificates, which are mostly about ADTs and
first-class functions, it only holds of a few that define no function.

**The query has no solution, whatever the calls**
([`Inox/Reached.lean`](Inox/Reached.lean)). The models of a solution satisfy
the defining equation of a function only where its call gives a value
(`goodOn_calls`), so the certificate has to use the equations on such calls
only. It does, and `reachedCheck` decides it:

- an instance of a defining equation is guarded by the activation literal of
  its call, `(=> d (= (f u1 … un) body))`, as it is or once the definitions
  of the local symbols of its instance are in place (`guardedEq`);
- the literal holds only if one of its blockers does (`Step.Only`);
- under each blocker, with the literals that its definition and those of the
  constants it mentions make known (`closeK`), evaluation goes through the call
  (`Paths.guards`): a base clause reaches it, or the body of a call that is
  already guarded, by a literal that is known, reaches it (`reachedBy`). A
  term reaches the calls of its operands that are evaluated: those of a branch
  of an `ite` whose condition is known, and those that both branches make;
- the other facts hold without the equations (`TermSteps.covered` with none),
  and no fresh symbol is a function of the program or a variable of the query
  (`apart`).

Then a guard that holds implies that its call gives a value, by induction along
the guarded calls (`inv_calls`), and so each fact holds in the models where the
calls and the variables agree (`Agrees`), which the intended model of a
solution is one of:

```lean
theorem no_solution_of_reached {O : Oracle} (sound : LogosSound) (hO : O.Sound)
    (hty : LogosTyping) {certificate : Logos.Sexp} {checked : Checked}
    {r : TermSteps} (hAccept : accept certificate = .ok checked)
    (hr : termSteps checked = .ok r) (hcheck : r.check = true)
    (hsrc : sourceCheck r = true) (hreached : reachedCheck r = true) :
    ∀ vs, ¬ Solution O (programOf (dataOf r) r.equations) (dataOf r)
      (varsOf (sigsOf r.equations) r.query) (queryOf r.query) vs
```

Nothing is assumed of the calls of the program, and `r.keeps` is not needed.
The checks hold of the two certificates above, and of the certificate of a
function that doesn't terminate on negative integers, with a query that only
calls it on 0 and 1, which `Total` leaves out. Like `sourceCheck`,
`reachedCheck` is defined over the semantics, so `inox-check` doesn't run it.

**Running the checks.** `inox-solution`, an executable of the verification
package ([`SolutionMain.lean`](SolutionMain.lean)), runs the hypotheses of
`no_solution_of_reached` that are computed (`accept`, `r.check`, `sourceCheck`
and `reachedCheck`) on each certificate of its files. It prints `no solution`
for a certificate that they hold of: given the soundness of Logos, the query
that it reads has no solution in the program that it reads. For another it
prints which check fails: the part of `sourceCheck` that puts it outside the
fragment, or how many facts `reachedCheck` doesn't cover, by the kinds of their
rules, and with `--remaining` their clauses. It exits with 1 unless they hold
of every certificate.

```sh
cd proofs/lean/verification && lake build inox-solution
.lake/build/bin/inox-solution answers.txt
```

The first build compiles the modules that the executable imports, those of
Mathlib too, which takes a quarter of an hour. Of the 36 certificates of the
corpus, the checks hold of 7: the 3 of `error-is-infeasible.smt3`, one of
`empty-function-codomains.smt3`, that of `size-negative.smt3`, whose function
is over lists, and those of `bitvector-division-by-zero-is-total.smt3` and
`real-division-by-zero-is-infeasible.smt3`. 25 are outside the fragment, 2
have facts that are not covered, and 2 have a proof with a constant array,
which Logos doesn't read.

**Assumptions.** A body with assumptions is read with them: Logos doesn't read
`(assume c b)` in a term, so the equation that the clauses instantiate is
without them (`dropAssumes`), and `equations` also reads each source with every
`(assume c b)` marked as `(ite (xor c false) b b)`, which has the value of `b`
and which no expression of the fragment translates to (`markAssumes`,
`Equation.source`). `back` reads the mark as `Assume`, so the program of the
certificate has the assumptions, and the translation of its bodies, which
leaves them out, is still the equation. Where an assumption can fail, such a
program is not `Total`, so `no_solution_of_check` and `no_solution_of_covered`
say nothing of it, and `no_solution_of_reached` is its theorem. A call whose
assumption fails is stuck, so where a call gives a value the assumptions that
its evaluation goes through hold (`assumesW`, `holds_of_assumesW`,
`assumed_of_call` in [`Inox/Reach.lean`](Inox/Reach.lean)). `reachedCovered`
then accepts a clause `(=> g ψ)` where `ψ` is, with the arguments of the call
for the parameters, the term of an assumption that the body of a guarded call
goes through, under the literals that `g` makes known, which make the guard of
the call true (`Paths.assumed`): the precondition of a call is one. A division
by zero is stuck in the same way, and SMT-LIB leaves its value open, so Inox
states that a divisor that is not a literal is not zero, in a clause
`(=> g (not (= d 0)))` under the blocker of the branch of the division
(`(not (= d (/ 0 1)))` on the reals).
`Division` is translated to `div`, and `Remainder` and `Modulo`, which are the
same on integers, to `mod`, which `back` reads as `Modulo`. Where the divisor
is not zero the terms have the values of the expressions (`ev`), `assumesW`
also finds `(not (= d 0))` for a divisor `d` that evaluation goes through, and
`reachedCovered` accepts the clause as it does that of an assumption. The
checks hold of the certificates of a recursive function with a precondition,
with a query that calls it within the precondition, and with one that calls it
outside, which has no solution for that reason, and of those of functions that
divide, one of them by zero on an argument of the query. An `Error` of a source
is read as the assumption that it is lowered to, `(assume false v)`, which is
stuck as it is: the program of the certificate has an `Assume` in its place,
and the clause `(=> g false)` of its branch is that of this assumption. The
checks hold of the certificates of a recursive function with an error, with a
query that stays away from it and with one that only reaches it. The query is
read in the same way: its source expressions are read once without the
assumptions inside them, for the base clauses, and once with them marked, for
`r.query`, which `sourceCheck` checks the base clauses to be the translations
of. `reachedCovered` accepts the clause of an assumption, of a divisor or of an
error that the evaluation of an expression of the query goes through
(`Paths.assumedQuery`), since a solution gives the query a value. The checks
hold of the certificates of queries that divide by zero, that reach an error,
and that assume what doesn't hold. An assumption whose condition still has a
marker, such as the typing of a free variable of a type that is not a sort of
the session, is left out of the query. A mark doubles the body after it, so a
body with many nested assumptions is read slowly.

**The hypotheses that remain.**

- `Total`, for `no_solution` and `no_solution_of_covered`, not for
  `no_solution_of_reached`. It leaves out the functions that don't terminate
  on some arguments and those that are stuck on some, as a function with a
  precondition is where its `Assume` fails. Without it, `no_star_model` has
  `GuardOk` for the unfoldings, that a guard true in the intended model selects
  a call that is `Ok` at some fuel, and the clauses of instances and the facts
  verified directly are not relativized, so they stay in its `hfacts`.
- `LogosSound`, `LogosTyping` (discharged in `InoxClosed`), and `O.Sound`, that
  the oracle of `Forall` and `UninterpretedCall` agrees with the semantics
  (unused on the fragment but required by `call`).
- For `no_solution` and `no_star_model`, the shape of the program
  (`ProgFrag P`, `ProgTy D S P`, `SigOk D S`) and that the equations and the
  base clauses of the certificate are the translations of its bodies and of the
  query (`EqFor`, `BaseFor`). `sourceCheck` decides them for the program and
  the query read from the certificate, so `no_solution_of_check` has
  `sourceCheck r = true` in their place. A reflexivity axiom among the
  equations is not the translation of a body, so the check refuses a
  certificate that has one; the programs of the fragment have none.
- That the program and the query read from the certificate are those that Inox
  answered about.
- For `no_star_model`, `model_wf M0`, a well-formed model for the sorts and the
  other function values, `cd : Codes`, `model_wf N` and
  `N.usortDom = M0.usortDom`. `no_solution` takes none of them: a well-formed
  model exists by the theorem of Logos (`Smtm.model_wf_nonvacuous`), and an
  injection of codes by `Codes.nonempty`.
- `hfacts`: for `no_solution`, the facts that `r.covered` doesn't cover
  (contracts, assertions and the others, see above), and none when it covers
  them all (`no_solution_of_covered`); for `no_star_model`, the facts other
  than guarded unfoldings. `no_solution_of_reached` has none: `reachedCheck`
  asks that every fact be covered.

The translation stops at integers, Booleans, reals, bit-vectors, datatypes
without type parameters and sets. Not translated: unit, `Let`, `Error`,
`Division`, `Remainder`, `Modulo`, type arguments, closures, `Forall` and
`UninterpretedCall`.

A certificate whose program has type parameters or `let`s is in the fragment
all the same, because the program that the theorem is about is the one read
from the terms of the certificate, where neither is left. Inox's session is
monomorphic: each instance of a sort or of a function at given type arguments
has a symbol of its own, `size!0` for `size` of lists of Booleans and `size!1`
for that of lists of integers, and the lowering of a template's source
(`Inox/Lowering.lean`) instantiates the definition at the type arguments of its
call. So the program of the theorem has one datatype for each instance of a
sort and one function for each instance of a function, none of them with type
parameters. A `let` of a source is a `let` of SMT-LIB, which Logos reads as its
body with the bound term in place of the variable, and that is the expression
that `back` reads. The checks were run on certificates made for this, of
functions over lists and pairs at one and at several instances, at nested ones,
and of functions with `let`s, around a recursive call too: the theorem holds of
all of them.

**What would make the generated Lean easier to prove things about.** The
generated `match`es on `Result` (one auxiliary matcher per site) defeat generic
lemmas about binding, so each proof splits them by hand (the `ok_split` macro);
a `Result.bind` with `@[simp]` lemmas would let `simp` do it. `value-eq`
decides with `open Classical`, so equalities of values go through `decide` on a
classical instance. The root module `Inox` is shared between `proofs/semantics`
(`Inox.Semantics`) and this package, so a file outside either package can't
import both. `call` takes a type environment that doesn't matter for functions
without type parameters, but only a lemma (`call_tenv`) shows it.

## What is not proved yet

- **The rules that are facts.** `no_good_model_of_accept` covers the rules that
  introduce fresh symbols, and `no_good_model_of_instances` the unfoldings, the
  clauses of instances that hold by the meanings of their symbols given the
  base, and the facts that hold as they are (congruence, the reflexivity of the
  declared equalities). The theorem to come is the one of an UNSAT answer in
  [`semantics.md`](../semantics.md): the query has no solution. `no_solution`
  states it for the first-order programs over integers, Booleans, reals,
  bit-vectors, datatypes and sets whose calls all give values, with hypotheses
  (see
  [The bridge to the semantics](#the-bridge-to-the-semantics-partly-proved)),
  and `no_solution_of_reached` for those programs whatever their calls, for the
  certificates of which its checks hold. In general it needs the bridge beyond
  that fragment, that its solutions give `Good` models (where the declared
  equalities are reflexive and the completeness assumptions hold, and for the
  programs with calls that give no value, with the clauses of instances
  relativized as the unfoldings are), and for each other kind of rule, that its
  clauses hold in them (`hfacts`): the preconditions, postconditions, ADT
  invariants and refinements of the templates (`contract`), which are
  assumptions about the program; the clauses of assertions about the instances
  of quantifiers, and those whose source expression has a binder or mentions a
  fresh symbol; the typing predicates; the templates whose source is not a
  function; the clauses with binders; and the other rules (`Dispatched`,
  `SameLambda`, the `Congruence` of instances of quantifiers, …).
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
  refuses a certificate with a source that doesn't lower. An error of a source,
  `(error S "message")`, is lowered to an assumption that never holds,
  `(assume false v)` with `v` the `0` or the `false` of its sort, since Logos
  reads the terms of a source, and an error of another sort is refused. Only
  the Scala checker checks that the clauses of a template are those of its
  source
  ([`Sources.scala`](../src/main/scala/inox/certificates/Sources.scala)); this
  checker only checks the clauses that it covers against the lowered source
  (`unfoldB`, and the clauses of instances, given the meanings of their
  symbols).
- **The input and the encoders.** The checker checks that each encoded
  constraint of the certificate's input is what the encoders that the
  certificate names make of its constraint, as the Scala checker does
  ([`Encoders.lean`](Inox/Encoders.lean), a port of
  [`Encoders.scala`](../src/main/scala/inox/certificates/Encoders.scala)),
  and that the body of each function of the source definitions is what they
  make of its definition in the input, simplified by the steps that the
  certificate gives. It doesn't check the steps. No theorem yet states that
  an encoded constraint has a solution whenever its constraint has one, and
  nothing relates the encoded constraints to the sources of the templates:
  the theorem is about the sources. For the encoder of bags,
  [`Bags.lean`](Inox/Bags.lean) proves the parts of that theorem that are
  about the datatype alone, over the semantics of `semantics.md`: a call of
  the encoder's `get` evaluates to the multiplicity of the element
  (`get_eval`), what the encoder makes of the empty bag, of an addition, a
  union, a difference and an intersection encodes the bag that the semantics
  gives for the operation (`enc_empty`, `enc_add`, `enc_union`,
  `enc_difference`, `enc_intersection`), a multiplicity is the call of `get`
  (`enc_get`), and the equality of the datatype, the encoder's `equals`, on
  the encodings of two bags is the equality of the bags (`enc_equal`). They
  assume that the program defines `get`, `equals` and the constructors as the
  encoder does, which the checker checks for `get` and the constructors, and
  that the elements have an equality that is an equivalence.
  [`Encoded.lean`](Inox/Encoded.lean) puts them together for programs. The
  values of the input relate to those of the encoded program by their kinds
  (`Rel`): elements, integers and booleans are the same, a bag relates to its
  encoding, values of the sorts of the program and tuples relate field by
  field, and two functions relate when the body of one is what the encoder
  makes of the body of the other and the variables that they keep have values
  that relate. `encodes_eval` proves, by induction on the fuel, that when an
  expression evaluates to a value in the program of the input, what the encoder
  makes of it evaluates, with enough fuel, to a value that relates to it in the
  encoded program. It covers variables, literals, sums, differences,
  comparisons, equalities, connectives, conditionals, lets, assumptions, the
  bag operations above, multiplicities, tuples, the constructors, selectors and
  testers of the sorts of the program, calls of its functions, whose bodies in
  the encoded program are what the encoder makes of their bodies in the input
  (`Funs`), lambdas and applications, quantifiers over integers and booleans,
  errors, and calls of uninterpreted functions without type arguments, whose
  interpretations in the encoded program are what the encoder makes of their
  interpretations in the input. An equality is covered where its operands have
  no functions in them. A quantifier holds when all of its instances hold with
  the same fuel, so the theorem also bounds the fuel of an encoding that has no
  operations of bags by the fuel of its expression, and covers quantifiers,
  lambdas and functions whose bodies are of these. It assumes the invariant of
  the datatype as the encoder defines it, sorts of the program without
  invariants nor equalities, one type of elements, which the type parameters of
  functions and sorts are instantiated with (integers where the input has no
  type parameter), and doesn't cover bag literals with elements, bags of bags,
  quantifiers over other values nor the other theories yet.
  [`Input.lean`](Inox/Input.lean) reads the definitions and the constraints of
  a certificate's input and what the encoders make of them as expressions of
  the semantics, decides whether each encoded expression is what the encoder
  makes of its expression (`encodesCheck`, proven sound), and `covers_encoded`
  states the theorem for a certificate: where the constraints that are covered
  all evaluate to `true` in a program that has the functions of the input, so
  do their encoded terms in a program that has their bodies after the encoders
  and defines the encoder's datatype as the encoder does, on values of the free
  variables that relate. `inox-solution --input` says how many constraints of
  each certificate that covers, and what the first of the others has that isn't
  read. On the corpus it covers 12 of the 36 constraints, among which that of
  `bags/split-preserves-content`, with its two recursive functions, three with
  quantifiers, and five with uninterpreted functions or errors: the others have
  quantifiers over elements or datatypes, sets, maps, bitvectors, reals, or
  sorts whose type arguments are not the elements. Nor is this theorem joined
  to `no_solution_of_reached` yet, whose program has neither sorts with type
  parameters nor sorts with an equality.
- **The link between the proof and the script.** The checker checks that each
  assumption of the proof is the text of an assert of the script, up to how
  cvc5 prints testers (`(is C e)` for `((_ is C) e)`), once the terms that the
  proof defines are in place. The theorem is about the assumptions as Logos
  reads them.

As for Logos itself: its parser is not verified, it doesn't read the constant
arrays of Inox's maps and bags, which are in cvc5's expert signature (the
checker then checks the rules, and Ethos the proof), and it reports a proof
outside of what its theorem covers as `incomplete`, which `inox-check` refuses.
