# Checking certificates

Inox answers a `(get-proof)` after an unsat `(check-sat)` with a certificate
(see [its format](../../src/main/scala/inox/solvers/certificates/README.md)).
This directory checks certificates apart from the solver, in two steps.

1. `inox.certificates.Checker`
   ([`Checker.scala`](../src/main/scala/inox/certificates/Checker.scala)) reads
   what Inox printed and checks the rules of each certificate: each rule is an
   instance of its kind and builds the asserts that it names, every assert of
   the script is named by a rule or is an assumption, each fresh symbol is
   introduced once, and the proof only assumes asserts of the script. It shares
   no code with the solver. With `--cpc <dir>`, it writes the CPC proof of each
   certificate that holds to `<dir>`.

   ```sh
   inox --solvers=smt-cvc5 file.smt3 > answers.txt   # the file has a (get-proof)
   sbt "proofs/runMain inox.certificates.Checker --cpc out answers.txt"
   ```

2. Ethos checks the CPC proofs against cvc5's signature. `get-ethos.sh DIR`
   builds Ethos and fetches the signature at the versions that match the cvc5
   of the tests, and `check.sh DIR` runs it on every proof of `DIR`:

   ```sh
   eval "$(proofs/certificates/get-ethos.sh /tmp/ethos)" && export ETHOS CPC
   proofs/certificates/check.sh out
   ```

`CheckerSuite` checks the certificates of the regression files that
[`corpus.txt`](corpus.txt) lists, and writes their CPC proofs to
`$INOX_CPC_DIR` when it is set. CI runs it and then Ethos (the `certificates`
job).

## What is checked, and what is not

A certificate that holds, with a proof that Ethos accepts, shows that the
clauses of its script have no model, and that each of them is a clause that a
rule of `unrolling.RuleKernel` builds. Two things are left to the reader:

- **The templates.** The checker takes the clauses of each template as given.
  Nothing yet relates them to the input query and its functions.
- **The side conditions of the rules.** The checker checks the shape of each
  rule, and that the symbols that `Define`, `Hypothesis` and `Root` introduce
  are introduced once. It doesn't check what a rule states about the program,
  such as that the blockers of a `Congruence` are those of two calls of the
  same function, or that an assumption states the completeness of an open
  conjunction that refutations may assume (it checks that it is a literal).

Both need the trace from the input to the templates, which the certificate
doesn't hold yet.
