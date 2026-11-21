# End-to-end certificates

A `(get-proof)` after a `(check-sat)` that Inox answers `unsat` prints the
certificate of that query on standard output:

    (certificate
    (script
    <the SMT-LIB script of the clauses that the unrolling solver checked>
    )
    (templates
    (script
    <the SMT-LIB script of the clauses of the templates that the solver instantiated>
    )
    (<index> (params <its start blocker and arguments>) <the indices of the asserts of its clauses>)
    ...)
    (rules
    (<kind> <the indices of the asserts of its clauses>)
    (<kind> (instance <template index> ((<template symbol> <value>) ...)) <the indices>)
    ...)
    (assumptions <the indices of the asserts of the assumptions of the check>)
    (cpc
    <cvc5's proof that the script has no model>
    ))

Inox only produces certificates; an external checker checks them, given the
input file. When there is no certificate, `get-proof` prints an
`(error "...")` that says why.

## Through the solver interface

A check configuration asks for proofs: under `Proof` and `ModelAndProof`, which
Inox uses for a query that a `get-proof` follows, an unsat answer is always an
`UnsatWithProof`, which holds the proof or why there is none. The proof is
structured (`Proofs.scala`): s-expressions parsed from the solver's answer, in
which each symbol of the solver's session is a `Sym` that maps back to the Inox
variable, function, sort, constructor, selector or tester that it stands for (a
`Ref`, in Inox trees: certificates are for programs of Inox trees). The other atoms keep the solver's
text, since CPC has literals such as `-1` and `1/2` that SMT-LIB doesn't. A
proof prints as below.

The `smt-cvc5` solver produces proofs when `optProduceProofs` is set, and the
other solvers say that they don't. Proof production slows cvc5 down from its
first assertion, so that Inox sets it only for an input that has a `get-proof`
(it isn't a command-line option). A portfolio then takes an unsat answer from a solver that proves it:
when Z3 answers unsat first, cvc5 keeps working. The portfolio takes an answer
without a proof only when no solver proves the query.

## What a certificate holds

Nothing is recomputed: the certificate is what the unrolling solver did. Every
clause that it asserts comes from a rule of `unrolling.RuleKernel`, each of
which states why its clauses hold under the intended interpretation of every
solution, where a blocker holds iff evaluation reaches the path it guards. This
doesn't assume that the functions terminate.

With proofs, the solver logs the rules that it applies, through the hooks that
`unrolling.RuleChecker` checks them with. A rule such as `Unfold`, whose clauses
are an instance of a template (the clauses of a function's body, of a lambda's
body, or of the query), names the template and the values of its symbols, its
start blocker and arguments and the fresh symbols that replace its other
symbols, while the rules that the instance applies in turn, such as for the
calls that it makes, are logged on their own.

cvc5 then runs with `:produce-proofs`, and the unrolling solver checks it under
a proof configuration in each check whose unsat answer can be its own. Under it,
cvc5 answers `UnsatWithProof` with a `ScriptProof`: the commands of its session,
which declare its symbols and assert the clauses and assumptions of the check,
and its CPC proof (from `get-proof`). When the unrolling solver refutes the
query, the certificate holds that proof, each template that the rules
instantiate once, printed in the same session, and the rules that gave the
clauses.

## Checking a certificate

A checker checks that:
- each template is the template of its function, lambda or query, which it
  checks once however often the template is instantiated;
- each rule is an instance of its kind for the program, whose clauses are the
  asserts that it names (for an instance of a template, the template's clauses
  under the values of its symbols), and that defines each fresh symbol once;
- every assert is named by a rule, or is an assumption that the checker can
  justify (the refutation assumptions of open junctions, see
  `unrolling.OpenJunctions`);
- the proof's `assume` commands are the script's asserts, and the proof checks
  (Ethos, or Logos in Lean, which is proved sound).

Certificates need cvc5 1.4 or later (the `cvc5` of the `smt-cvc5` solver),
whose proofs match the CPC signature that the checkers use.
