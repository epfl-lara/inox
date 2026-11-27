# Checking certificates

Inox answers a `(get-proof)` after an unsat `(check-sat)` with a certificate
(see [its format](../../src/main/scala/inox/solvers/certificates/README.md)).
This directory checks certificates apart from the solver, in two steps.

1. `inox.certificates.Checker`
   ([`Checker.scala`](../src/main/scala/inox/certificates/Checker.scala)) reads
   what Inox printed and checks the rules of each certificate: each rule is an
   instance of its kind and builds the asserts that it names, every assert of
   the script is named by a rule or is an assumption, each fresh symbol is
   introduced once (those that `Define`, `Hypothesis` and `Root` rules
   introduce, the lambdas whose bodies templates are, and the symbols that
   instances of expressions `(= p e)` define), and the proof only assumes asserts of the script (where
   the solver may have inlined their bindings). It shares
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

  The `simplifications` section relates the sources to the input query and
  its functions. Before generating templates, the solver simplifies each
  formula (inlining, path simplification, let and quantifier simplification).
  For each function whose source body differs from its original definition,
  and for each source expression that differs from the formula it was made
  from, the section holds the original term and the steps that rewrite it
  into the source. [`Simplifications.scala`](../src/main/scala/inox/certificates/Simplifications.scala)
  replays them. The steps are not found by comparing the two terms: the
  simplifiers record each rewrite as they apply it. A step is
  `(<rule> <position> <subterm>)`: the rule, the position of the smallest
  subterm outside of which the step leaves the term as it is, and what that
  subterm becomes. The checker checks the rule at the position, or at a
  subterm around it. A step may only refine the subterm: wherever the
  original has a value, the rewritten term has the same value.
  The rules are three-valued propositional reasoning over the atoms of the
  term, under the facts of the path to it (`logic`), unfolding a function
  call (`unfold`), beta reduction (`beta`), replacing a variable by the
  value of its let (`expand`), selecting a field of a construction or an
  element of a tuple (`select`), a construction of the fields of a term
  (`eta`), binding a subterm that is always evaluated (`bind`), lifting a
  let or an assumption out of an operand that is always evaluated (`lift`),
  merging quantifiers (`merge`), dropping the unused variables of a
  quantifier over inhabited sorts (`unused`), lifting the quantifiers of
  the operands of a connective (`prenex`), polynomial arithmetic
  (`arith`), renaming bound variables (`rename`), and the evaluation of a
  closed term (`evaluate`): the term and its value are read as terms of
  Inox with the source definitions, where the functions have their original
  bodies, and both are evaluated, with fuel, by
  the evaluator that is generated from [`semantics.md`](../semantics.md),
  to the same value. The simplifiers name
  every rewrite, and don't judge which ones the checker can check: a step
  of a rule that the checker doesn't know is applied as it is given, and
  the certificate then holds over the simplified program only, which the
  checker says with the rules. This is the case of the evaluation of a term
  that the generated evaluator gives no value to (it covers a fragment of
  Inox, and doesn't compare functions) and that doesn't reduce to the value
  either (the checker reduces calls, bindings, conditionals and selections
  to literals, lambdas and constructions, which is how it checks the values
  of functions, and takes an equality of closures, or the membership of a
  closure in a set of closures, to be false where the evaluator gives the
  closures different values on an integer or Boolean input, and true where
  they reduce to the same lambda), and of the steps that a simplifier
  can't tell are ones of `logic`, which the checker checks as such, and
  reports when they are not: an assumption that is lifted out of a binder
  (`lift-assumptions`, a step of `logic` out of a quantifier over sorts
  that have values, whose body always evaluates the assumption), and what
  a simplifier makes of a term without a rule of its own (`simplify`). A
  step of a rule that the
  checker knows, and which doesn't hold, makes the certificate fail, and so
  does what a simplifier did without recording it (`unrecorded`). When the
  program compares functions (`--function-equality` is not `none`), a
  refinement under a lambda or in a function body is not enough, as it may
  make two functions equal. Where functions are compared extensionally, the
  steps under a lambda, and those of a function body, must then preserve the
  value of the subterm exactly, which the checker checks of each rule:
  `logic` checks both directions, `select` and `arith` drop no operand that
  may have no value (nor `select` a construction of a sort with an
  invariant), `prenex` lifts out of the last operand only and over
  sorts that have values, and a reduction selects no field out of a
  construction of a sort with an invariant.
  Where they are compared intensionally, a step may change a lambda that the
  program compares as written: the checker doesn't check the steps, and says
  so. What remains trusted:
  - that the originals are the program and the query that the solver was
    given: the certificate states them, and nothing compares them with an
    input;
  - the names of the sources: the symbol of a lambda or of the instantiations
    of a quantifier stands for the subterm that the section gives for it, and
    so does the symbol of the equality of a sort, applied to the operands of
    an equality that the simplifiers keep, as the check of the sources trusts
    too (the checker checks that a name is not a symbol of the original, that
    the operands are those of the equality, and that a quantifier that the
    source assumes is where it must hold, as is the universal one whose
    negation names an existential one). The source also names a call of an
    uninterpreted function under the assumptions of its typing, and a
    construction under the assumption of the invariant of its sort, which
    the checker checks to be the invariant that the source definitions
    declare (`datatype-invariant`), as it is of the construction or as a
    function of the same body, and evaluates or reports otherwise;
  - the theory encoders (sets, bags, maps, propositions) that run before the
    simplifier, whose output is the original that the steps start from;
  - the rules themselves, which the Lean checker doesn't prove yet (it skips
    the section, and its result holds over the simplified program).

  The certificate also holds the input of the solver: its constraints before
  the solver's encoders, each with the term that the encoders make of it. The
  checker checks that term against the constraint
  ([`Encoders.scala`](../src/main/scala/inox/certificates/Encoders.scala)):
  both have the same shape, a symbol of the input facing the symbol of the
  sources of the same identifier, except where the input has a term of an
  encoder's theory, which faces what the encoder makes of it, such as
  `(bag.union a b)` and `(Node 0 a b)`. It knows the encoders that cvc5 runs
  with (`propositions`, `bags` and `map-merge`), and refuses a certificate
  that names another. It checks that the datatype of bags and its functions
  `get` and `inv` in the source definitions are those of the encoder of
  bags. It doesn't check the sorts that only the encoded term has, nor the
  encoder's equality of bags and its `mapMerge`.

  The same goes for the functions: the input gives, for each function of the
  source definitions, its body after the encoders, which the checker checks
  against the definition of the function in the input, and which must be the
  original of the function in the `simplifications` section, whose steps lead
  to the body of the source definition, or that body when the section has no
  entry for the function. The datatypes of the input are checked against those
  of the sources in the same way.
- **The side conditions of the rules.** The checker checks the shape of each
  rule, and that the symbols that `Define`, `Hypothesis` and `Root` introduce
  are introduced once, as are the lambdas whose bodies templates are, each by
  the instances of one template, and the parameters `p` of the expressions
  `(= p e)` that instances define. Without that, a certificate could give one
  lambda the bodies of two, or have a probe define a symbol that the script
  already constrains. Introduced once is not fresh: the Scala checker doesn't
  check that no clause before the introduction mentions the symbol, which the
  Lean checker's check on terms does for the symbols of the rules. It doesn't check what a rule states about the program,
  such as that the blockers of a `Congruence` are those of two calls of the
  same function, or that an assumption states the completeness of an open
  conjunction that refutations may assume (it checks that it is a literal).

The second needs the trace from the input to the sources, which the
`simplifications` section starts to hold.
