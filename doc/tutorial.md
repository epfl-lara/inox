Tutorial
========

Let us consider the problem of checking whether the following size function on a list is always greater or equal to 0.
```scala
def size[A](list: List[A]): BigInt = list match {
  case Cons(x, xs) => 1 + size(xs)
  case Nil() => 0
}
```

Note that verifying this property requires the use of induction, something Inox does not deal with explicitly.
However, Inox provides all the tools necessary to enable inductive reasonning, as we will see shortly.

Let us start by setting up some useful imports:

```scala
import inox._
import inox.trees._
import inox.trees.dsl._
import inox.solvers._
```

The explanation is the following:
- `inox._` imports [`InoxProgram` and many others](/src/main/scala/inox/package.scala#L19)
- `inox.trees._` imports the content of the default implementation [`trees`](/src/main/scala/inox/package.scala#L58) extending [`Trees`](/src/main/scala/inox/ast/Trees.scala#L10).
- `inox.trees.dsl._` imports the [domain-specific-language helpers](/src/main/scala/inox/ast/DSL.scala#L20) to create [`trees`](/src/main/scala/inox/package.scala#L58) expressions.
- `inox.solvers._` imports the [solvers](/src/main/scala/inox/solvers/package.scala#L8).

## Creating the Symbol Table

Inox uses a symbol table to lookup function and ADT definitions, so we start by setting up the
required definitions.

### ADT Definitions

The dsl we just imported provides us with the following helper methods to define ADTs (see
the [Definitions](/doc/API.md#definitions) section in the API documentation for more details):

1. For ADT sort definitions

    ```scala
    def mkSort(id: Identifier)
              (tpNames: String*)
              (cons: Seq[Identifier]): ADTSort
    ```

2. For ADT constructor definitions

    ```scala
    def mkConstructor(id: Identifier)
                     (tpNames: String*)
                     (sort: Option[Identifier])
                     (fieldBuilder: Seq[TypeParameter] => Seq[ValDef]): ADTConstructor
    ```

We therefore start by setting up the identifiers for the `List` sort
```scala
val list: Identifier = FreshIdentifier("List")
val cons: Identifier = FreshIdentifier("Cons")
val nil: Identifier = FreshIdentifier("Nil")
```
It is also useful to create identifiers for the fields of ADTs, as we will see shortly
```scala
val head: Identifier = FreshIdentifier("head")
val tail: Identifier = FreshIdentifier("tail")
```

Based on these, we can construct the relevant ADT sort and constructors
```scala
val listSort = mkSort(list)("A")(Seq(cons, nil))
val consConstructor = mkConstructor(cons)("A")(Some(list)) {
  case Seq(tp) => /* `tp` is the type parameter required by the "A" argument to `mkConstructor`. */
    /* We use the previously defined `head` and `tail` identifiers for the fields' symbols.
     * The type `T(list)(tp)` is a shorthand for `ADTType(list, Seq(tp))`. */
    Seq(ValDef(head, tp), ValDef(tail, T(list)(tp)))
}
val nilConstructor = mkConstructor(nil)("A")(Some(list))(tps => Seq.empty)
```
Note that we have defined a list *sort* with identifier `list` that has two constructors with identifiers
`cons` and `nil`. All three definitions are parametric in a type "A" (Inox imposes the restriction that
sorts and their constructors must have the same number of type parameters).

### Function Definition

Let us now consider the function `size`. We start by defining the symbol corresponding to the function's definition.
```scala
val size: Identifier = FreshIdentifier("size")
```

The main point of interest here lies in constructing the body of `size`. Let us assume we have in scope
some type parameter `tp: TypeParameter` and variable `ls: Variable` (we will see shortly how Inox provides you
with these).

We start by defining the conditional. Inox has no concept of pattern matching
(but [Stainless](https://github.com/epfl-lara/stainless) does!), however it is quite trivial to desugar
the pattern matching in our `size` definition to an __if__-expression. We can thus write the conditional in
Inox as
```scala
if_ (ls.isInstOf(T(cons)(tp))) {
  ... /* `1 + size(ls.tail)` */
} else_ {
  ... /* 0 */
}
```
We then complete the *then* and *else* expressions of the conditional as follows
```scala
/* The `E(BigInt(i))` calls correspond to `IntegerLiteral(i)` ASTs. */
if_ (ls.isInstOf(T(cons)(tp))) {
  /* The recursive call to `size` written `E(size)(tp)(...)` corresponds to
   * the AST `FunctionInvocation(size, Seq(tp), Seq(...))`.
   * Note that we refer to the symbol `tail` of the `consConstructor`'s second
   * field when building the selector AST. */
  E(BigInt(1)) + E(size)(tp)(ls.asInstOf(T(cons)(tp)).getField(tail))
} else_ {
  E(BigInt(0))
}
```
The expression we just defined corresponds to the body of our `size` function, however we are
still lacking the inductive invariant. In Inox, one can use the `Assume` AST to provide this feature,
leading to the full `size` body:
```scala
/* We use a `let` binding here to avoid dupplication. */
let("res" :: IntegerType, if_ (ls.isInstOf(T(cons)(tp))) {
  E(BigInt(1)) + E(size)(tp)(ls.asInstOf(T(cons)(tp)).getField(tail))
} else_ {
  E(BigInt(0))
}) { res =>
  /* We assume the inductive hypothesis, namely the result of `size` is greater or equal to 0. */
  Assume(res >= E(BigInt(0)), res)
}
```

Inox provides the following helper method to define functions (see
the [Definitions](/doc/API.md#definitions) section in the API documentation for more details):
```scala
def mkFunDef(id: Identifier)
            (tpNames: String*)
            (builder: Seq[TypeParameter] => (Seq[ValDef], Type, Seq[Variable] => Expr)): FunDef
```
and we can then construct the function definition as
```scala
val sizeFunction = mkFunDef(size)("A") { case Seq(tp) => (
  /* We now define the argument list of the size function.
   * Note that `"ls" :: T(list)(tp)` is a shorthand for the definition
   * `ValDef(FreshIdentifier("ls"), ADTType(list, Seq(tp)))`. */
  Seq("ls" :: T(list)(tp)),
  /* Now comes the return type of the size function (a mathematical integer). */
  IntegerType,
  /* And finally, the body constructor.
   * The function we pass in here will receive instances of `Variable` corresponding
   * to the `ValDef` parameters specified above. */
  { case Seq(ls) =>
    let("res" :: IntegerType, if_ (ls.isInstOf(T(cons)(tp))) {
      E(BigInt(1)) + E(size)(tp)(ls.asInstOf(T(cons)(tp)).getField(tail))
    } else_ {
      E(BigInt(0))
    }) (res => Assume(res >= E(BigInt(0)), res))
  })
}
```

### Symbols

A symbol table in Inox is an instance of `Symbols`. The easiest way to construct one is to use
```scala
implicit val symbols = {
  NoSymbols
    .withFunctions(Seq(sizeFunction))
    .withADTs(Seq(listSort, consConstructor, nilConstructor))
}
```
We make the symbols value implicit as many methods in Inox require an implicit `Symbols` argument
(such as `getType`, `getFunction`, `getADT`, etc.).

## Verifying Properties

Now that we have set up the relevant definitions, we want to move on to some actual verification.
The property we want to verify is that forall `ls: List[A]`, we have `size(ls) >= 0`. As Inox
primarily focuses on satisfiability checks, we will show instead that there exists no
`ls: List[A]` such that `size(ls) < 0`.

__Note__: It is __not__ sound to simply check that the expression `E(size)(tp)(ls) < 0` is not
satisfiable! Indeed, would simply assume this to be true given the `Assume` statement in the body of
`size`.

__Disclaimer__: In general, it is not the philosophy of Inox to implement sound verification, but
rather to enable it. All `Assume` statements provided to Inox will be unchecked and taken as truth.
It is the burden of the user to construct a sound verification procedure with the provided tools.

Sound assume/guarantee reasonning can be implemented by checking that the body of `size` (without
the `Assume` statement) satisfies the condition we are trying to prove. (Note that termination of
`size` is also a requirement here.) The property we are interested in is therefore
```scala
val tp: TypeParameter = TypeParameter.fresh("A")
val ls: Variable = Variable.fresh("ls", T(list)(tp))
val prop = (if_ (ls.isInstOf(T(cons)(tp))) {
  E(BigInt(1)) + E(size)(tp)(ls.asInstOf(T(cons)(tp)).getField(tail))
} else_ {
  E(BigInt(0))
}) >= E(BigInt(0))
```
__Note__: Inox will assume the inductive invariant on the recursive call to `size(xs)`.

In order to verify the property, we get an instance of an Inox solver (see
[Programs](/doc/API.md#programs) and [Solvers](/doc/API.md#solvers) for more details):
```scala
val program = InoxProgram(Context.empty, symbols)
val solver = program.getSolver.getNewSolver
solver.assertCnstr(Not(prop))
solver.check(SolverResponses.Simple) // Should return `Unsat`
```
Et voila, all done!
