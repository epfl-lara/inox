# Certificates of unsat answers

A `(get-proof)` after a `(check-sat)` that Inox answers `unsat` prints the
certificate of that query on standard output:

    (inox-certificate 6
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
    (<symbol of the script> <kind> "<identifier, type or index>" ... [<sort>])
    ...)
    (source-definitions
    <the SMT-LIB 3 declarations of the datatypes and definitions of the functions of the sources>
    )
    (source-symbols
    (<symbol of the sources> <kind> "<identifier, type or index>" ... [<sort>])
    ...)
    (input
    (encoders "<name>" ...)
    (definitions
    <the SMT-LIB 3 declarations of the datatypes and definitions of the functions of the input>
    )
    (constraint <a constraint of the input> (encoded <what the encoders make of it>))
    ...
    (function <the call of a function of the sources on its parameters> (encoded <its body>))
    ...
    (symbols
    (<symbol of the input> <kind> "<identifier, type or index>" ... [<sort>])
    ...))
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

    (definition <the call of the function on the template's arguments> [(names (<name> <subterm>) ...)])
    (function <the call of the function on the template's arguments> <its body>)
    (expression <a term that holds under the template's start blocker>)

The body of a function is the one that the solver unfolds, after its
simplifications. The source definitions define each function once with that
body, as a `define-fun`, `define-fun-rec` or `define-funs-rec` over its
parameters and type parameters, and a `definition` source stands for the body
of the definition at the arguments of the call and the type arguments that
their sorts determine. Its names are the subterms of that body that the
template has another term for, each with that term: the symbol of a lambda,
the instantiations of a quantifier, or a construction or uninterpreted call
under the assumptions that the clauses make of it. A `function` source gives
its body in place: that of a lambda, the value that the solver computed for
a call, or the body of a function that has equal subterms that the template
has different terms for. A source is an Inox expression, which Inox's SMT-LIB 3 printer prints
(`inox.smtlib3.Printer`, the syntax of `.smt3` inputs, with an
`(assume <condition> <body>)` for each assumption and an
`(error <sort> "<message>")` for each error). Its variables are those of
the script, under the script's names, and its other symbols are those of the
printer, which names identifiers as the script does. The source symbols say
what each symbol of the sources stands for, as the solver symbols do for the script.
The source definitions are the commands that printing the sources made: the
declarations of the datatypes and of the uninterpreted functions, and the
definitions of the functions.

Sorts relate the two vocabularies. The symbols of the script that depend on a
type end with the SMT-LIB 3 sort of that type, as the printer of the sources
prints it: a sort, constructor, selector or tester with that of its datatype,
a dynamic application with the function sort that it applies, and the instance
of a generic function with the list of the sorts of its type arguments, such as

    (Cons!0 constructor "Cons$0" "List$0[BigInt]" (List!1 Int))
    (first!0 function "first$0" "BigInt" (Int))

and the variables of the sources end with their sort. Each instantiation of an
uninterpreted function is a function of its own in the sources, which ends
with the sorts of its type arguments when it has some:

    (any!1 uninterpreted "any$1" (T!0))
    (any!2 uninterpreted "any$1" (Int))

so that the body of a definition that calls `any!1`, instantiated at `Int`,
calls `any!2`.

A source says which symbol of the script each of its symbols stands for: a
symbol whose symbol of the script depends on a type is printed under the sort
that the solver symbols record for it, `(as <symbol> <sort>)`, so that a
checker reads the symbol of the script from the tables and infers no sort:

    ((as Cons!5 (List!1 Int)) x (as Nil!5 (List!1 Int)))   a constructor of a generic datatype
    ((as head!5 (List!1 Int)) l)                           a selector, under its datatype
    ((as (_ is Cons!5) (List!1 Int)) l)                    a tester
    ((as first!3 (Int)) l)                                 a generic function, under its type arguments
    ((as @ (-> Int Int)) f x)                              an application, under the function sort
    ((as tuple (Tuple Int Bool)) x b)                      a tuple, under its sort

The symbols of datatypes and functions without type parameters are printed
as they are. The body of a definition is generic: its sorts mention the type
parameters of the definition, which the type arguments of a call replace.
Distinct types must print as distinct sorts, since the sort picks the symbol
of the script; the solver checks that they do, and gives no certificate
otherwise.

The checker checks that the clauses of the template are those of its source: they
name the values of its subexpressions and the paths that lead to them. Every
template has a source, that of a type, a lambda or a quantifier included; when
the solver can't print the source of a template, there is no certificate.

The input is what the solver was given, before its encoders: the program of the
session is the program of the input after the encoders that `encoders` names,
in their order (`propositions`, which makes propositions Booleans, `bags`,
which makes a bag a datatype with a function for its multiplicities,
`map-merge`, and for other solvers `strings`, `sets` and `reals`; see
`solvers.theories`). The definitions are those of the datatypes and functions
of the input that its constraints mention, each constraint is one that was
asserted, with the term that the encoders make of it, and the symbols say what
those of the input stand for, as the source symbols do: a symbol of the input
and one of the sources that stand for the same identifier are the function, the
sort or the variable before and after the encoders. The input is `(input)` when
the solver's program is not one that the session's printer prints. Each
function that the source definitions define comes with its body in the program
of the session, after the encoders. The `simplifications` section relates these
terms to the sources: an encoded constraint, under the typing of its variables,
is the original of the expression of its template, and the body of a function
is the original of its entry there, or the body of its source definition when
the solver left it as it is.

A source names what its body doesn't have with markers (`unrolling.TemplateGenerator.markers`), whose
meanings a `(where (<marker> <meaning>) ...)` after the body gives. A marker
is an uninterpreted Boolean function of the sources, which the source
declarations don't declare, qualified by the sort of the type it is about: the
typing of a value is `((as typing!0 <sort>) "<mode>" x <closures>)`, which means
the conditions that its type puts on `x` (and `((as reads!0 <sort>) ...)` those
on the values that reads of a collection give, `(as inhabited!0 <sort>)` that
the type has a value), and the functions that a lambda `f` captures through a
value `x` come before `f`, `((as typing!0 <sort>) "capture" x f)`, which the
source of the template that orders them assumes. The sort keeps the type's
refinements, which are the conditions that the meaning states. The checker checks the clauses against the
marker and its meaning; it doesn't check that the meaning is that of the type,
nor that the functions that a capture orders are those of the value.

The `where` also gives the meanings of symbols of the template: the lambdas that
the source holds, and each symbol that the clauses don't define with one
equation, such as the result of a conditional, whose clauses give its value on
each branch, and which means the conditional of those values, or the symbol
that stands for an error, which no clause defines and which means that error.
The generator
records them where it creates the symbols, so that the checker reads what a
symbol stands for rather than finds it from the shapes of the clauses. The
checker doesn't rely on them: under them, each clause must hold for the source.

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
- each fresh symbol is introduced once: those that a `Define`, `Hypothesis` or
  `Root` rule introduces, the lambda whose body a template is (`(@ f x1 .. xn)`
  as the call of a `function` source), which only the instances of that
  template define and which is not one of its parameters, and the parameter `p`
  of an `expression` source `(= p e)`, under its assumptions, such as the result
  of a probe or of a comparison of lambdas, which its instance defines as `e`;
- the clauses of each template are those of its source, once the source is
  lowered to the syntax of the script;
- each encoded constraint of the input is what the named encoders make of its
  constraint, and the body of each function of the sources what they make of
  its definition in the input, which the steps of its simplification lead to
  the body of its source definition;
- the proof's `assume` commands are asserts of the script.

Ethos then checks the proof. The checker also exists in Lean
([`proofs/lean`](../../../../../../proofs/lean/README.md)), where Logos, which
is proved sound, checks the proofs in cvc5's standard signature. CI does both
for a corpus of regression files.

Certificates need cvc5 1.4 or later (the `cvc5` of the `smt-cvc5` solver),
whose proofs match the CPC signature that the checkers use. cvc5 runs with
`--arrays-exp` for the constant arrays of Inox's maps and bags, which are in
cvc5's expert signature (`CpcExpert.eo`): Ethos checks them with it, and Logos
doesn't support them yet.
