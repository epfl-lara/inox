Inox API
========

Trees
-----

Extendability is core to the design of the Inox AST (Abstract Syntax Tree).
The [Trees](/src/main/scala/inox/ast/Trees.scala) trait can be extended with
new constructs and provide useful override points to enable extensions with
new features. See [Stainless](https://github.com/epfl-lara/stainless) for some
concrete examples.

### Identifiers

Inox uses the `Identifier` type to represent symbols in the program. Note that
no type is attached to an instance of `Identifier`. Values and variables will
attach a type to their identifier, and function invocations will rely on the
symbol table to compute their type. See the [Definitions](#definitions) section
for more information on the symbol table.

### [Expressions](/src/main/scala/inox/ast/Expressions.scala)

The classes defined here correspond to the base expressions supported by Inox.
Inox can currently handle
- Type parametric recursive higher-order functions (see [Definitions](#definitions) and `FunctionInvocation` expression)
- First-class functions (see `Lambda` and `Application` expressions)
- Mathematical integer arithmetic
- Bitvector arithmetic
- Algebraic datatypes (see [Definitions](#definitions) and `ADT`, `ADTSelector` expressions)
- Strings
- Sets / Multisets
- Total maps
- Quantifiers (see `Forall`)

Note that Strings, Sets / Multisets and Total maps can all be implemented using
recursive and first-class functions in conjunction with ADTs. We list them here as
Inox uses the underlying SMT solvers' native theory APIs for these constructs.

The relevant type definitions associated with these expressions can be found in
[Types](/src/main/scala/inox/ast/Types.scala).

### [Definitions](/src/main/scala/inox/ast/Definitions.scala)

Inox uses two main types of definitions: functions and ADTs. These definitions
are stored in a symbol table of type `Symbols` which is used to lookup identifiers
during typing, solving and evaluation.

__Functions__

Functions here refer to named functions as opposition to anonymous ones (lambdas).
Named functions can be recursive and support type-parametric polymorphism. A
function definition is an instance of
```scala
class FunDef(
  val id: Identifier,                 /* The symbol associated with this function. */
  val tparams: Seq[TypeParameterDef], /* The function's type parameters. */
  val params: Seq[ValDef],            /* The function's formal arguments. */
  val returnType: Type,               /* The return type of this function. */
  val fullBody: Expr,                 /* The body of this function. */
  val flags: Set[Flag]                /* Annotations associated to this definition. */)
```
As mentionned [above](#identifiers) in the identifier section, `ValDef` associates
a type with an identifier and has the following signature:
```scala
class ValDef(val id: Identifier, val tpe: Type, val flags: Set[Flag])
```

__ADTs__

Algebraic datatype definitions can be recursive and support type-parametric polymorphism,
as in the named function case. An ADT can either correspond to a *sort*, or a *constructor*.
Sorts can be seen as abstract classes with constructors resembling final classes.

ADT sort definitions take place using the following class:
```scala
class ADTSort(
  val id: Identifier,                 /* The symbol associated with this ADT sort. */
  val tparams: Seq[TypeParameterDef], /* The ADT's type parameters. */
  val cons: Seq[Identifier],          /* The symbols of the sort's constructors. */
  val flags: Set[Flag]                /* Annotations associated to this definition. */)
```
Note that the sort will point to all its potential constructors.

ADT constructor definitions then take place using the class:
```scala
class ADTConstructor(
  val id: Identifier,                 /* The symbol associated with this ADT sort. */
  val tparams: Seq[TypeParameterDef], /* The ADT's type parameters. */
  val sort: Option[Identifier],       /* The symbol of the constructor's (optional) sort. */
  val fields: Seq[ValDef],            /* The fields associated to this constructor. */
  val flags: Set[Flag]                /* Annotations associated to this definition. */)
```

Inox provides the utility types `TypedFunDef`, `TypedADTSort` and `TypedADTConstructor`
that respectively correspond to function and ADT definitions whose type parameters have
been instantiated with concrete types. One can use these to access parameters/fields and
enclosed expressions with instantiated types.

Programs
--------

As mentionned above, Inox expressions only make sense with a corresponding symbol table.
Furthermore, the expression/definition/type instances themselves require an instance of
[Trees](/src/main/scala/inox/ast/Trees.scala) to exist due to path-dependence. Inox wraps
all these concerns into an instance of [Program](/src/main/scala/inox/Program.scala) with
the following signature
```scala
trait Program {
  /* The instance of Trees in which the expressions/defininitions/types of this program live. */
  val trees: Trees
  /* The symbol table to be used for function and ADT lookups in this program. */
  val symbols: Symbols
  /* Wrapper for options and reporter. */
  val ctx: Context
  ... (some other useful stuff) ...
}
```
In general, Inox uses programs to make its path-dependant API feasible and both [solvers](#solvers)
and [evaluators](#evaluators) are bound to some program instance.

Solvers
-------

Inox solvers offer the following main API methods:

### Assert constraint
```scala
def assertCnstr(expr: Expr): Unit
```

Adds the boolean-typed expression `expr` to the set of constraints the solver is trying to satisfy.

### Check
```scala
def check(config: Configuration): config.Response[Model,Assumptions]
```

Queries the solver to determine whether the current set of constraints that have been asserted is
satisfiable. The `check` method takes a `config` argument that determines the exact modalities of the
check (see [SolverResponses](/src/main/scala/inox/solvers/SolverResponses.scala)).
The four configurations are `Simple`, `Model`, `UnsatAssumptions` and `All`.
The result of the check then depends on the actual configuration provided, namely

1. `Simple` will result in either `Sat`, `Unsat` or `Unknown`
2. `Model` will result in either `SatWithModel(model)`, `Unsat` or `Unknown`
3. `UnsatAssumptions` will result in either `Sat`, `UnsatWithAssumptions(assumptions)` or `Unknown`
4. `All` will result in either `SatWithModel(model)`, `UnsatWithAssumptions(assumptions)` or `Unknown`

The `Model` and `Assumptions` type parameters given to `config.Response[Model,Assumptions]` correspond
respectively to the type of `model` in `SatWithModel(model)` and `assumptions` in
`UnsatWithAssumptions(assumptions)`. Note that typically, we have
```scala
type Model = Map[ValDef, Expr]
type Assumptions = Set[Expr]
```

The "Assumptions" cases that appear above actually cannot take place during a call to `check` but
only during a call to [`checkAssumptions`](#check-assumptions).

### Check Assumptions
```scala
def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[Model, Assumptions]
```

Queries the solver to determine whether the current set of constraints is satisfiable *assuming all
assumptions hold as well*. When the query is unsatisfiable, the solver will try to determine which
expressions in the `assumptions` set were at fault and return them in the
`UnsatWithAssumptions(assumptions)` result.

Evaluators
----------

The evaluator API consists simply of an `eval` method with the following signature
```scala
def eval(expr: Expr, model: Map[ValDef, Expr]): EvaluationResult
```
where the [evaluation result](/src/main/scala/inox/evaluators/EvaluationResults.scala)
is either an instance of `Successful(value)` or corresponds to an evaluation error.
