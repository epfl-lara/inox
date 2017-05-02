Inox String Interpolation
=========================

# Table of Content

- ***[Introduction](#introduction)***
  - [Importing](#importing)
- ***[Syntax](#syntax)***
  - [Literals](#literals)
    - [Boolean](#boolean-literals)
    - [Numeric](#numeric-literals)
      - [Real](#real-literals)
    - [String](#string-literals)
    - [Character](#character-literals)
  - [Arithmetic](#arithmetic)
  - [Conditionals](#conditionals)
  - [Let bindings](#let-bindings)
  - [Lambda expressions](#lambda-expressions)
  - [Quantifiers](#quantifiers)
    - [Universal quantifiers](#universal-quantifiers)
    - [Existential quantifiers](#existential-quantifiers)
  - [Choose](#choose)

- ***[Primitives](#primitives)***
  - [Strings](#primitive-strings)
  - [Sets](#primitive-sets)
  - [Bags](#primitive-bags)
  - [Maps](#primitive-maps)

<a name="introduction"></a>
# Introduction

In this document, we describe the string interpolation facility offered in Inox. String interpolations make it possible to build and deconstruct Inox types and expressions using a succinct and expressive language. Throughout this document, we will describe the syntax of this language and its primitive constructs.

<a name="importing"></a>
## Importing the interpolator

The first step to use this feature is to import it. The string interpolator is located within the `Symbols` class.

```scala
import inox._
import inox.trees._

implicit val mySymbols = NoSymbols
import mySymbols.interpolator._
```

Once imported, it is possible to build Inox types and expressions using a friendlier syntax:

```scala
scala> val tpe = t"Boolean"
tpe: mySymbols.interpolator.trees.Type = Boolean

scala> val expr = e"1 + 1 == 2"
expr: mySymbols.interpolator.trees.Expr = 1 + 1 == 2
```

It is also possible to embed types and expressions:

```scala
scala> e"let x: $tpe = $expr in !x"
res1: mySymbols.interpolator.trees.Expr =
val x: Boolean = 1 + 1 == 2
¬x
```

<a name="syntax"></a>
# Syntax

<a name="literals"></a>
## Literals

<a name="boolean-literals"></a>
### Boolean literals

```scala
scala> e"true"
res2: mySymbols.interpolator.trees.Expr = true

scala> e"false"
res3: mySymbols.interpolator.trees.Expr = false
```

<a name="numeric-literals"></a>
### Numeric literal

```scala
scala> e"1"
res4: mySymbols.interpolator.trees.Expr = 1
```

Note that the type of numeric expressions is infered. In case of ambiguity, `BigInt` is chosen by default.

```scala
scala> val bigIntLit = e"1"
bigIntLit: mySymbols.interpolator.trees.Expr = 1

scala> bigIntLit.getType
res5: mySymbols.interpolator.trees.Type = BigInt
```

It is however possible to annotate the desired type.

```scala
scala> val intLit = e"1 : Int"
intLit: mySymbols.interpolator.trees.Expr = 1

scala> intLit.getType
res6: mySymbols.interpolator.trees.Type = Int
```

```scala
scala> val realLit = e"1 : Real"
realLit: mySymbols.interpolator.trees.Expr = 1

scala> realLit.getType
res7: mySymbols.interpolator.trees.Type = Real
```

<a name="real-literals"></a>
#### Real literals

```scala
scala> e"3.75"
res8: mySymbols.interpolator.trees.Expr = 15/4
```

<a name="string-literals"></a>
### String literals

```scala
scala> e"'Hello world!'"
res9: mySymbols.interpolator.trees.Expr = "Hello world!"
```

<a name="character-literals"></a>
### Character literals

```scala
scala> e"`a`"
res10: mySymbols.interpolator.trees.Expr = a
```

<a name="arithmetic"></a>
## Arithmetic

Arithmetic operators are infix and have there usual associativity and priority.

```scala
scala> e"1 + 2 * 5 + 6 - 7 / 17"
res11: mySymbols.interpolator.trees.Expr = ((1 + 2 * 5) + 6) - 7 / 17
```

<a name="conditionals"></a>
## Conditionals

```scala
scala> e"if (1 == 2) 'foo' else 'bar'"
res12: mySymbols.interpolator.trees.Expr =
if (1 == 2) {
  "foo"
} else {
  "bar"
}
```

<a name="let-bindings"></a>
## Let bindings

```scala
scala> e"let word: String = 'World!' in concatenate('Hello ', word)"
res13: mySymbols.interpolator.trees.Expr =
val word: String = "World!"
"Hello " + word
```

<a name="lambda-expressions"></a>
## Lambda expressions

```scala
scala> e"lambda x: BigInt, y: BigInt. x + y"
res14: mySymbols.interpolator.trees.Expr = (x: BigInt, y: BigInt) => x + y
```

It is also possible to use the unicode `λ` symbol.

```scala
scala> e"λx: BigInt, y: BigInt. x + y"
res15: mySymbols.interpolator.trees.Expr = (x: BigInt, y: BigInt) => x + y
```

Type annotations can be omitted for any of the parameters if their type can be infered.

```scala
scala> e"lambda x. x * 0.5"
res16: mySymbols.interpolator.trees.Expr = (x: Real) => x * 1/2
```

<a name="quantifiers"></a>
## Quantifiers

<a name="universal-quantifiers"></a>
### Universal Quantifier

```scala
scala> e"forall x: Int. x > 0"
res17: mySymbols.interpolator.trees.Expr = ∀x: Int. (x > 0)

scala> e"∀x. x || true"
res18: mySymbols.interpolator.trees.Expr = ∀x: Boolean. (x || true)
```

<a name="existential-quantifiers"></a>
### Existential Quantifier

```scala
scala> e"exists x: BigInt. x < 0"
res19: mySymbols.interpolator.trees.Expr = ¬∀x: BigInt. (x >= 0)

scala> e"∃x, y. x + y == 0"
res20: mySymbols.interpolator.trees.Expr = ¬∀x: BigInt, y: BigInt. (x + y ≠ 0)
```

<a name="choose"></a>
## Choose

```scala
scala> e"choose x. x * 3 < 17"
res21: mySymbols.interpolator.trees.Expr = choose((x: BigInt) => x * 3 < 17)

scala> e"choose x: String. true"
res22: mySymbols.interpolator.trees.Expr = choose((x: String) => true)
```

<a name="primitives"></a>
# Primitives

<a name="primitive-strings"></a>
## Strings

### Literal Syntax

```
''
'hello world'
'hey!'
```

### Functions

| Function | Type | Description | Inox Constructor |
| -------- | ---- | ----------- | ---------------- |
| `length`   | `String => BigInt` | Returns the length of the string. | `StringLength` |
| `concatenate` | `(String, String) => String` | Returns the concatenation of the two strings. | `StringConcat` |
| `substring` | `(String, BigInt, BigInt) => String` | Returns the substring from the first index inclusive to the second index exclusive. | `SubString ` |

### Operators

| Operator | Type | Associativity | Precedence | Description | Inox Constructor |
| -------- | ---- | ------------- | ---------- | ----------- | ---------------- |
| `++` | `(String, String) => String` | Left-associative | ??? | Returns the concatenation of the two strings. | `StringConcat` |

<a name="primitive-sets"></a>
## Sets

### Constructor

| Constructor | Description | Inox Constructor |
| ----------- | ----------- | ---------------- |
| `Set[A](elements: A*)` | Returns a set containing the given `elements`. | `FiniteSet` |

### Literal Syntax

```
{}
{1, 2, 3}
{'foo', 'bar', 'baz'}
```

### Functions

| Function | Type | Description | Inox Constructor |
| -------- | ---- | ----------- | ---------------- |
| `contains[A]` | `(Set[A], A) => Boolean` | Returns `true` if the given set contains the given element, `false` otherwise. | `ElementOfSet` |
| `add[A]` | `(Set[A], A) => Set[A]` | Returns the set with an element added. | `SetAdd` |
| `subset[A]` | `(Set[A], Set[A]) => Boolean` | Returns `true` if the first set is a subset of the second, `false` otherwise. | `SubsetOf` |
| `union[A]` | `(Set[A], Set[A]) => Set[A]` | Returns the unions of the two sets. | `SetUnion` |
| `intersection[A]` | `(Set[A], Set[A]) => Set[A]` | Returns the intersection of the two sets. | `SetIntersection` |
| `difference[A]` | `(Set[A], Set[A]) => Set[A]` | Returns the elements of the first set minus the elements of the second set. | `SetDifference` |

### Operators

| Operator | Type | Associativity | Precedence | Description | Inox Constructor |
| -------- | ---- | ------------- | ---------- | ----------- | ---------------- |
| `∈` | `(A, Set[A]) => Boolean` | Left-associative | ??? | Returns `true` if the element is part of the set, `false` otherwise. | `ElementOfSet` |
| `⊆` | `(Set[A], Set[A]) => Boolean` | Left-associative | ??? | Returns `true` if the first set is a subset of the second, `false` otherwise. | `SubsetOf` | |
| `∪` | `(A, Set[A]) => Boolean` | Left-associative | ??? | Returns the unions of the two sets. | `SetUnion` |
| `∩` | `(A, Set[A]) => Boolean` | Left-associative | ??? | Returns the intersection of the two sets. | `SetIntersection` |
| `∖` | `(A, Set[A]) => Boolean` | Left-associative | ??? | Returns the elements of the first set minus the elements of the second set. | `SetDifference` |

<a name="primitive-bags"></a>
## Bags

### Constructor

| Constructor | Description | Inox Constructor |
| ----------- | ----------- | ---------------- |
| `Bag[A](bindings: (A -> BigInt)*)` | Returns a bag containing the given `bindings`. | `FiniteBag` |

### Literal Syntax

```
{1 -> 2, 2 -> 4, 3 -> 6}
{'foo' -> 5, 'bar' -> 2, 'baz' -> 2}
```

### Functions

| Function | Type | Description | Inox Constructor |
| -------- | ---- | ----------- | ---------------- |
| `multiplicity[A]` | `(Bag[A], A) => BigInt` | Returns the number of occurences in the given bag of the given value. | `MultiplicityInBag` |
| `bagAdd[A]` | `(Bag[A], A) => Bag[A]` | Returns the bag with an element added. | `BagAdd` |
| `bagUnion[A]` | `(Bag[A], Bag[A]) => Bag[A]` | Returns the unions of the two bags. | `BagUnion` |
| `bagIntersection[A]` | `(Bag[A], Bag[A]) => Bag[A]` | Returns the intersection of the two bags. | `BagIntersection` |
| `bagDifference[A]` | `(Bag[A], Bag[A]) => Bag[A]` | Returns the elements of the first bag minus the elements of the second bag. | `BagDifference` |

<a name="primitive-maps"></a>
## Maps

### Constructor

| Constructor | Description | Inox Constructor |
| ----------- | ----------- | ---------------- |
| `Map[A](default: A, bindings: (A -> BigInt)*)` | Returns a map with default value `default` containing the given `bindings`. | `FiniteMap` |

### Literal syntax

```
{*: Int -> 42}
{* -> '???', 'hello' -> 'HELLO', 'world' -> 'WORLD'}
```

### Functions

| Function | Type | Description | Inox Constructor |
| -------- | ---- | ----------- | ---------------- |
| `apply[K, V]` | `(Map[K, V], K) => V` | Returns the value associated to the given key. | `MapApply` |
| `updated[K, V]` | `(Map[K, V], K, V) => Map[K, V]` | Returns the map with a bidding from the key to the value added. | `MapUpdated` |
