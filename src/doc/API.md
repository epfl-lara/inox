Inox API
========

Trees
-----

Extendability is core to the design of the Inox AST (Abstract Syntax Tree).
The [Trees](/src/main/scala/inox/ast/Trees.scala) trait can be extended with
new constructs and provide useful override points to enable extensions with
new features. See [Stainless](https://githum.com/epfl-lara/stainless) for some
concrete examples.

Programs are constructed from
1. [Expressions](/src/main/scala/inox/ast/Expressions.scala)

  
