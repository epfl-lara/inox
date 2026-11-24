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
`$INOX_CPC_DIR` and what Inox printed to `$INOX_ANSWERS_DIR` when they are set.
CI runs it, then Ethos, then the checker in Lean (the `certificates` job).

[`proofs/lean`](../lean/README.md) has the same check of the rules in Lean,
where Logos checks the proofs, which comes with a theorem.

## What is checked, and what is not

A certificate that holds, with a proof that Ethos accepts, shows that the
clauses of its script have no model, and that each of them is a clause that a
rule of `unrolling.RuleKernel` builds. Two things are left to the reader:

- **The templates.** Every template, of a function, a type, a lambda, a
  quantifier or an expression that holds such as the query, comes with its
  source, and the checker checks that its clauses are those of the source
  ([`Sources.scala`](../src/main/scala/inox/certificates/Sources.scala)): the
  values of its subexpressions, each under the blocker of its path, its
  assumptions, what its divisions, selectors and invariants need, and that
  the rank of a call decreases. It refuses a certificate with a template whose
  clauses it can't relate to the source, and says which clause is in the way.
  It checks the clauses of a typing against its marker and the meaning that
  the source gives it, and not that the meaning is that of the type, nor that
  the functions that a capture orders are those of the captured value.

  The certificate defines each function once, and the source of a template of
  that function is the body of the definition at the arguments of the call,
  which the checker instantiates. An uninterpreted function with the type
  parameters of the definition in its type arguments becomes the symbol that
  the source symbols record for the instantiated type arguments. Where the template has another term for a
  subterm of the body (the symbol of a lambda, the instantiations of a
  quantifier, a construction or uninterpreted call under the assumptions that
  the clauses make of it), the source names the subterm with that term, and
  the checker replaces it: it checks that every named subterm is in the body,
  and not that the name is a term for it.

  Sources are in Inox's SMT-LIB 3 syntax, and clauses in that of the solver's
  session. [`Lowering.scala`](../src/main/scala/inox/certificates/Lowering.scala)
  first rewrites each source to the session's syntax, from the certificate's
  tables alone. The printer writes each symbol whose session symbol depends on
  a type under the sort that the solver symbols record for it, `(as x S)`, and
  the lowering picks the session symbol of the same Inox definition and of that
  sort (a constructor, selector or tester of that datatype, the instance of a
  generic function at those type arguments, the dynamic application of that
  function sort): it infers no sort. Sorts are compared without their
  refinements (`:var` and `:restrict`), which the session's sorts don't have.
  Its documentation lists how each construct lowers. What this trusts:
  - that distinct types print as distinct sorts, which the solver checks
    when it prints them;
  - that the descriptions of symbols (the identifiers, and the index of a
    selector) are those of the same Inox definitions in both tables, which
    the solver prints from the same identifiers;
  - that each construct lowers to a term of the same meaning, such as
    `(insert s e)` to `(set.insert e s)`, `(exists ..)` to `(not (forall ..))`,
    `Char` to `(_ BitVec 16)`, a function sort to `Int` (the session's sort of
    function values), and the signedness annotations of bit vectors to
    nothing (the session's operations say how they read their arguments).

  The lowering refuses a source whose symbol the session has none or several
  of, or that uses a construct that it doesn't lower:
  lambdas, `tuple.unit`, bags, string operations and floating points, which
  no source of the corpus uses.

  Nothing yet relates the sources to the input query and its functions.
- **The side conditions of the rules.** The checker checks the shape of each
  rule, and that the symbols that `Define`, `Hypothesis` and `Root` introduce
  are introduced once. It doesn't check what a rule states about the program,
  such as that the blockers of a `Congruence` are those of two calls of the
  same function, or that an assumption states the completeness of an open
  conjunction that refutations may assume (it checks that it is a literal).

The second needs the trace from the input to the sources, which the
certificate doesn't hold yet.
