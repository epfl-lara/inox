# Proofs of Inox's answers

[`semantics.md`](semantics.md) defines what an Inox expression means,
independently of any proof checker: the theorem that a proof of an UNSAT answer
states is that no values of the free variables make the query evaluate to
`true` under this semantics.

Its fenced `inox-sem` blocks are read by `inox.semantics.Codegen`, which writes
the semantics for each tool that needs it. Today that is a Scala evaluator,
[`src/main/scala/inox/semantics/generated/Semantics.scala`](src/main/scala/inox/semantics/generated/Semantics.scala),
which the checker of certificates evaluates closed terms with, and which
`SemanticsSuite` compares with Inox's `RecursiveEvaluator` on the
functions of the regression files and on random expressions over every theory.
The functions that quantify over values (`forall`, `exists`) can't be computed,
so the evaluator leaves them abstract, and the tests give them by enumerating
small finite types.

It also writes Lean definitions,
[`semantics/Inox/Semantics.lean`](semantics/Inox/Semantics.lean), in a Lake
package of its own that depends on nothing but Lean: an inductive type per
datatype and a total definition per function, so that `eval` is a function of
Lean that proofs unfold. Lean has to see that each recursion ends. Where it
doesn't find the measure itself, `LeanBackend.measures` gives it: evaluation
decreases the fuel, then the expression. Two kinds of functions are not defined
but given by an `Oracle`, with `Oracle.Sound` stating that the oracle satisfies
their definitions: the functions that quantify and are defined in terms of
themselves (the equality and the types of first-class functions), which no
recursion defines, and those of `LeanBackend.assumed`, whose termination Lean
isn't shown yet (the equality of values, which looks up the entries of maps,
and the types of values, which follow type parameters through the
environment). `lake build` in `semantics` checks the file, and CI runs it. An
Eunoia backend comes next.

[`certificates`](certificates/README.md) checks the certificates that Inox
prints for its unsat answers, apart from the solver.
[`lean`](lean/README.md) has that checker in Lean, where Logos, which is proved
sound, checks the proofs of the certificates: what it accepts comes with a
theorem.

This directory is the sbt project `proofs`, which depends on Inox but is not
part of it: it is not published, and Inox's jars don't contain it. `sbt test`
runs its tests along with Inox's, and `sbt proofs/test` runs them alone.

After changing `semantics.md`, regenerate the embeddings and commit them with
it; a test fails while they are out of date:

```sh
sbt proofs/run
```

A language that compiles to Inox can extend this semantics in its own file,
which imports `semantics.md` and adds constructors and cases (see the end of
`semantics.md`). `sbt "proofs/run <file.md> <output.scala> <package>
<output.lean> <namespace>"` generates its evaluator and its Lean definitions,
which give the expressions of Inox the same meaning. The Lean file is closed:
it holds the definitions of the imported files too, since an inductive type
can't be extended from another file.
