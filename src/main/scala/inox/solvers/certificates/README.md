# Certificates of unsat answers

A `(get-proof)` after a `(check-sat)` that Inox answers `unsat` prints the
certificate of that query on standard output:

    (inox-certificate 2
    (script
    <the SMT-LIB script of the clauses that the unrolling solver checked>
    )
    (templates
    (script
    <the SMT-LIB script of the clauses of the templates that the solver instantiated>
    )
    (<index> (params <its start blocker and arguments>) <its source> <the indices of the asserts of its clauses>)
    ...)
    (rules
    (<kind> (args (<name> <term> ...) ...) <the indices of the asserts of its clauses>)
    (<kind> (args ...) (instance <template index> ((<template symbol> <value>) ...)) <the indices>)
    ...)
    (assumptions (query <the indices of their asserts>) (complete <the indices of their asserts>))
    (solver-symbols
    (<symbol of the script> <kind> "<identifier, type or index>" ...)
    ...)
    (source-symbols
    (<symbol of the sources> <kind> "<identifier, type or index>" ...)
    ...)
    (cpc
    <cvc5's proof that the script has no model>
    ))

The number is the version of the format. Inox only produces certificates; an
external checker checks them (see [Checking a certificate](#checking-a-certificate)).
When there is no certificate, `get-proof` prints an `(error "...")` that says
why.

## What a certificate states

A certificate states that the script has no model, and that each clause of the
script holds under the intended interpretation of every solution of the query
(see `unrolling.RuleKernel`), given that the clauses of each template hold for
the function, lambda or query that the template is of. Together, they give
that the query has no solution, which is the theorem of an UNSAT answer in
[`proofs/semantics.md`](../../../../../../proofs/semantics.md).

The source of a template is the expression that its clauses are of:

    (function <the call of the function on the template's arguments> <its body>)
    (expression <a term that holds under the template's start blocker>)

The body is the one that the solver unfolds, after its simplifications. A
source is an Inox expression, which Inox's SMT-LIB 3 printer prints
(`inox.smtlib3.Printer`, the syntax of `.smt3` inputs, with an
`(assume <condition> <body>)` for each assumption). Its variables are those of
the script, under the script's names, and its other symbols are those of the
printer, which names identifiers as the script does. The source symbols say
what each symbol of the sources stands for, as the solver symbols do for the script;
the printer's declarations and definitions, such as the datatypes and the
bodies of the functions, are left out.

A checker can check that the clauses of the template are those of its source,
under the encoding of the solver: they name the values of its subexpressions
and the paths that lead to them. The templates of types, lambdas and
quantifiers have no source yet. There is no certificate when a source can't be
printed. The certificate doesn't yet hold the input query and the encoding of
its program either, which relate the sources to the input.

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
`unrolling.RuleChecker` checks them with. Each rule is logged with the
arguments that its clauses are built from, by name (`Rule.arguments`): the
literal and the value of a `Define`, the blocker and the target of an
`Enables`, and so on. A rule such as `Unfold`, whose clauses are an instance of
a template (the clauses of a function's body, of a lambda's body, or of the
query), names the template and the values of its symbols: its start blocker and
arguments, then the symbols that replace its other symbols. These are fresh,
except for the representative that equal lambdas share. The rules that the
instance applies in turn, such as for the calls that it makes, are logged on
their own. The log follows the solver's scopes.

cvc5 then runs with `:produce-proofs`, and the unrolling solver checks it under
a proof configuration in each check whose unsat answer can be its own. Under it,
cvc5 answers `UnsatWithProof` with a `ScriptProof`: the commands of its session,
which declare its symbols and assert the clauses and assumptions of the check,
and its CPC proof (from `get-proof`). When the unrolling solver refutes the
query, the certificate holds that proof, each template that the rules
instantiate once, printed in the same session, and the rules that gave the
clauses.

The assumptions of the check are those of the query, and those that state that
an open conjunction or disjunction is complete, which refutations may assume
(`unrolling.OpenJunctions` says why for each one). A check that assumes
anything else gives no certificate. The symbols are those of the session, each
with the Inox definition that it stands for: a variable (a blocker or another
symbol of the unrolling is one too), a function with its type arguments, a
sort, or a constructor, selector or tester.

## Checking a certificate

The checker is in [`proofs/certificates`](../../../../../../proofs/certificates/README.md),
apart from the solver. From the text of a certificate, it checks that:
- each rule is an instance of its kind: the clauses that its kind builds from
  its arguments are the asserts that it names, and for an instance of a
  template, the template's clauses under the values of its symbols;
- every assert is named by a rule, or is an assumption;
- each fresh symbol that a `Define`, `Hypothesis` or `Root` rule introduces is
  introduced once;
- the proof's `assume` commands are asserts of the script.

Ethos then checks the proof (as can Logos in Lean, which is proved sound, for
the proofs in cvc5's standard signature). CI does both for a corpus of
regression files.

Certificates need cvc5 1.4 or later (the `cvc5` of the `smt-cvc5` solver),
whose proofs match the CPC signature that the checkers use. cvc5 runs with
`--arrays-exp` for the constant arrays of Inox's maps and bags, which are in
cvc5's expert signature (`CpcExpert.eo`): Ethos checks them with it, and Logos
doesn't support them yet.
