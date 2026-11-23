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

With `--rules`, it checks the rules only. `check.sh DIR` runs it on the files of
`DIR`, which is what CI does on the corpus of the Scala checker (the
`certificates` job).

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

- **The rules.** The check of the rules is run, and nothing is proved of it
  yet. The theorem to come is the one of an UNSAT answer in
  [`semantics.md`](../semantics.md): the query has no solution. It needs the
  semantics of Inox in Lean, and for each kind of rule, that its clauses hold
  under the interpretation that a solution of the query gives.
- **The sources of the templates.** The checker lowers the source of every
  template to the syntax of the session, as the Scala checker does
  ([`Lowering.lean`](Inox/Lowering.lean), a port of
  [`Lowering.scala`](../src/main/scala/inox/certificates/Lowering.scala)), and
  refuses a certificate with a source that doesn't lower. Only the Scala
  checker checks that the clauses of a template are those of its source
  ([`Sources.scala`](../src/main/scala/inox/certificates/Sources.scala)).
- **The link between the proof and the script.** The checker checks that each
  assumption of the proof is the text of an assert of the script, up to how
  cvc5 prints testers (`(is C e)` for `((_ is C) e)`), once the terms that the
  proof defines are in place. The theorem is about the assumptions as Logos
  reads them.

As for Logos itself: its parser is not verified, it doesn't read the constant
arrays of Inox's maps and bags, which are in cvc5's expert signature (the
checker then checks the rules, and Ethos the proof), and it reports a proof
outside of what its theorem covers as `incomplete`, which `inox-check` refuses.
