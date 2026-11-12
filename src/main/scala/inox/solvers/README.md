# Solvers

A solver takes a set of boolean Inox expressions and decides whether some
assignment of their free variables makes them all evaluate to `true`. The
reference semantics is the evaluator in `../evaluators/RecursiveEvaluator`.
A solver can answer in three ways:

- **`Unsat`** means no such assignment exists. This is how a VC is proven:
  Inox checks the VC's negation and gets `Unsat`.
- **`SatWithModel(m)`** means `m` is such an assignment, which is a
  counterexample when the input is a negated VC. Besides the values of the
  free variables, a model gives the interpretations of the uninterpreted
  functions that these values and the query call.
- **`Unknown`** is returned on timeouts and interruptions, when the unroll
  bound is reached, and for models that cannot be trusted, such as models of
  quantifiers outside the supported fragment or models that fail validation.

Models are only evaluated against the query before they are returned when
`optCheckModels` is set (`--check-models`, off by default).

The layers, from the top:

| Directory | Role |
|---|---|
| `combinators/` | Wrappers: timeouts, portfolios, solver pools, program encodings, non-incremental solving |
| `evaluating/` | A solver that decides ground queries with the evaluator alone |
| `invariant/` | Invariant inference through Horn clauses (Eldarica), outside the unrolling procedure |
| `unrolling/` | The decision procedure for recursive functions, lambdas, dependent types and quantifiers |
| `theories/` | Encodings of strings, sets, bags, map merges and reals into what each backend supports |
| `z3/`, `smtlib/`, `princess/` | Quantifier-free backends: native Z3, SMT-LIB processes (Z3, cvc4, cvc5, Bitwuzla), Princess |

[`unrolling/README.md`](unrolling/README.md) presents the formalization
behind the procedure (Voirol, EPFL thesis no. 9479). It covers the guarantees
the procedure gives and where the implementation departs from the thesis.
