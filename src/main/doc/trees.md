Extending the Trees
===================

Inox trees are designed to be extensible with minimal pain and maximal gain.
By extending the [```Trees```](/src/main/scala/inox/ast/Trees.scala) trait,
one can introduce new `Tree` subtypes and extend the supported language.
```scala
trait Trees extends inox.ast.Trees {
  // new Expressions and Types and stuff
}
```

## Deconstructors

Alongside the tree definitions, one must provide a *deconstructor* for the
new ASTs by extending
[`TreeDeconstructor`](/src/main/scala/inox/ast/Extractors.scala):
```scala
trait TreeDeconstructor extends inox.ast.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees
  
  // Deconstructs expression trees into their constituent parts.
  // The sequence of `s.Variable` returned is used to automatically
  // compute the free variables in your new trees.
  override def deconstruct(e: s.Expr): (
    Seq[s.Variable], Seq[s.Expr], Seq[s.Type],
    (Seq[t.Variable], Seq[t.Expr], Seq[t.Type]) => t.Expr
  ) = e match {
    // cases that deconstruct your new expression trees
    case _ => super.deconstruct(e)
  }
  
  // Deconstructs type trees into their constituent parts.
  // Certain types (such as `s.TypeParameter` for example) can have
  // flags attached to them, so these should be deconstructed here
  // as well.
  override def deconstruct(tpe: s.Type): (
    Seq[s.Type], Seq[s.Flag],
    (Seq[t.Type], Seq[t.Flag]) => t.Type
  ) = tpe match {
    // cases that deconstruct your new type trees
    case _ => super.deconstruct(tpe)
  }
  
  // Deconstructs flags into their constituent parts.
  // Flags can contain both expressions and types.
  override def deconstruct(f: s.Flag): (
    Seq[s.Expr], Seq[s.Type],
    (Seq[t.Expr], Seq[t.Type]) => t.Flag
  ) = f match {
    // cases that deconstruct your new flags
    case _ => super.deconstruct(f)
  }
}
```
Note that if you extend your new instance of `Trees` with some further `Trees2`
type, you should extend the `TreeDeconstructor` associated with `Trees` when
defining the new `TreeDeconstructor2` associated with `Trees2`.

Now that you have defined your new deconstructor, it remains to register it
as *the* deconstructor for your new tree type:
```scala
trait Trees extends inox.ast.Trees {
  // new Expressions and Types and stuff

  // Scala's type checker unfortunately needs a little help here
  override def getDeconstructor(that: inox.ast.Trees) = that match {
    case tree: Trees => new TreeDeconstructor {
      protected val s: self.type = self
      protected val t: tree.type = tree
    }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]
    
    case _ => super.getDeconstructor(that)
  }
}
```

## Override points

We provide a large number of override points in order to make extension
as seemless as possible. Here is a (non-exhaustive) list of useful override points:

- [Printing](/src/main/scala/inox/ast/Printers.scala):
  the most noteworthy method is `ppBody` which prints an arbitrary `Tree`, and one
  should be aware of `isSimpleExpr`, `noBracesSub`, `requiresBraces` and
  `requiresParentheses` which controll braces and parentheses wrapping of sub-trees.

- [Symbols](/src/main/scala/inox/ast/Definitions.scala):
  If the symbol table provided by Inox is not sufficient for your needs, you can
  extend it by providing a new subtype to `AbstractSymbols` and strengthening the
  abstract type `Symbols`' upper bound. Modifying Inox' typing relation can then
  take place through the `typeBound` method found in
  [TypeOps](/src/main/scala/inox/ast/TypeOps.scala).
  
- [Symbol](/src/main/scala/inox/ast/SymbolOps.scala),
  [Type](/src/main/scala/inox/ast/TypeOps.scala) and
  [Expression](/src/main/scala/inox/ast/ExprOps.scala) operators:
  `AbstractSymbols` is also the place to override methods from
  [SymbolOps](/src/main/scala/inox/ast/SymbolOps.scala) and
  [TypeOps](/src/main/scala/inox/ast/TypeOps.scala). As for
  [ExprOps](/src/main/scala/inox/ast/ExprOps.scala), one can override the `exprOps`
  field of `Trees`.

## From one tree type to another

Given tree extensions (and thus multiple tree types), transforming from one tree type
to another becomes a relevant feature. Inox provides two different transformation
interfaces for such cases:

1. [TreeTransformer](/src/main/scala/inox/ast/TreeOps.scala):
   as long as the transformation can be performed without any extra context
   (*i.e.* symbol table or program), one should create an instance of `TreeTransformer`:
    ```scala
    new inox.ast.TreeTransformer {
      val s: source.type = source
      val t: target.type = target
      
      override def transform(e: s.Expr): t.Expr = e match {
        // do some useful expression transformations
        case _ => super.transform(e)
      }
      
      override def transform(tpe: s.Type): t.Type = tpe match {
        // do some useful type transformations
        case _ => super.transform(tpe)
      }
      
      override def transform(f: s.Flag): t.Flag = f match {
        // do some useful flag transformations
        case _ => super.transform(f)
      }
    }
    ```
    
2. [SymbolTransformer](/src/main/scala/inox/ast/TreeOps.scala):
   if one needs extra context for the transformation or wants to add/remove definitions
   from the symbol table, one should create an instance of `SymbolTransformer`:
    ```scala
    new inox.ast.SymbolTransformer {
      val s: source.type = source
      val t: target.type = target
      
      override def transform(syms: s.Symbols): t.Symbols = { /* ... stuff ... */ }
    }
    ```
    
It is sometimes useful to have a bidirectional translation between two sorts of trees.
Inox provides a mechanism to maintain an encoder/decoder pair alongside a pair of
source and target programs through an instance of
[ProgramTransformer](/src/main/scala/inox/ast/ProgramEncoder.scala).

## Providing new semantics

In order to gain access to Inox' main features (namely the evaluator and solver) with
our new tree definitions, two different approaches can be taken:

1. Extend the [RecursiveEvaluator](/src/main/scala/inox/evaluators/RecursiveEvaluator.scala)
   and [UnrollingSolver](/src/main/scala/inox/solvers/unrolling/UnrollingSolver.scala) from
   Inox with support for your new trees (or even define new concrete implementations of
   [DeterministicEvaluator](/src/main/scala/inox/evaluators/Evaluator.scala) or
   [Solver](/src/main/scala/inox/solvers/Solver.scala)). For some examples of this approach,
   one should take a look at the `RecursiveEvaluator` and `CodeGenEvaluator` from
   [Stainless](https://github.com/epfl-lara/stainless).
   
2. Define a [ProgramTransformer](/src/main/scala/inox/ast/ProgramEncoder.scala) and use an
   [EncodingSolver](/src/main/scala/inox/solvers/combinators/EncodingSolver.scala) and an
   [EncodingEvaluator](/src/main/scala/inox/evaluators/EncodingEvaluator.scala). Note that
   the implicit contract Inox assumes on your program transformer is that all types can be
   translated back and forth, however only *values* need be decodable. See the
   `InoxEncoder` and `SolverFactory` definitions in
   [Stainless](https://github.com/epfl-lara/stainless) for some examples of this option.
   
In order for the `getSemantics` method on `Program { val trees: yourTrees.type }` to be
available, it remains to define an implicit instance of
`SemanticsProvider { val trees: yourTrees.type }` (see
[SemanticsProvider](/src/main/scala/inox/Semantics.scala)) and make sure it is in scope.
