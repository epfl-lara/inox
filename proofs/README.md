# Proofs of Inox's answers

[`semantics.md`](semantics.md) defines what an Inox expression means,
independently of any proof checker: the theorem that a proof of an UNSAT answer
states is that no values of the free variables make the query evaluate to
`true` under this semantics.

Its fenced `inox-sem` blocks are read by `inox.semantics.Codegen`, which writes
the semantics for each tool that needs it. Today that is a Scala evaluator,
[`src/test/scala/inox/semantics/generated/Semantics.scala`](src/test/scala/inox/semantics/generated/Semantics.scala),
which `SemanticsSuite` compares with Inox's `RecursiveEvaluator` on the
functions of the regression files and on random expressions over every theory.
The functions that quantify over values (`forall`, `exists`) can't be computed,
so the evaluator leaves them abstract, and the tests give them by enumerating
small finite types. Lean and Eunoia backends come next.

[`certificates`](certificates/README.md) checks the certificates that Inox
prints for its unsat answers, apart from the solver.

This directory is the sbt project `proofs`, which depends on Inox but is not
part of it: it is not published, and Inox's jars don't contain it. `sbt test`
runs its tests along with Inox's, and `sbt proofs/test` runs them alone.

After changing `semantics.md`, regenerate the embeddings and commit them with
it; a test fails while they are out of date:

```sh
sbt proofs/run
```
