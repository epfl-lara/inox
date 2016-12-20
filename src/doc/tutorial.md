Tutorial
========

Let us consider the problem of checking whether the following size function on a list is always greater or equal to 0.
```scala
def size[T](list: List[T]): BigInt = list match {
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
```

## ADT Definitions

The dsl we just imported provides us with the following helper methods to define ADTs (see
the [Definitions](/src/doc/API.md#definitions) section in the API documentation for more details):

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

We therefore start by 
