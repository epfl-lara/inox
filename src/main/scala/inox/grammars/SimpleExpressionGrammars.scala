/* Copyright 2009-2015 EPFL, Lausanne */

package inox
package grammars

/** An [[ExpressionGrammar]] whose productions for a given [[Label]]
  * depend only on the underlying [[Type]] of the label
  */
trait SimpleExpressionGrammars { self: GrammarsUniverse =>
  import program.trees._
  import program.symbols

  trait SimpleExpressionGrammar extends ExpressionGrammar {
    type Prod = ProductionRule[Type, Expr]

    /** Generates a [[ProductionRule]] without nonterminal symbols */
    def terminal(builder: => Expr, tag: Tag = Top, cost: Int = 1) = {
      ProductionRule[Type, Expr](Nil, { (subs: Seq[Expr]) => builder }, tag, cost)
    }

    /** Generates a [[ProductionRule]] with nonterminal symbols */
    def nonTerminal(subs: Seq[Type], builder: (Seq[Expr] => Expr), tag: Tag = Top, cost: Int = 1) = {
      ProductionRule[Type, Expr](subs, builder, tag, cost)
    }

    def filter(f: Prod => Boolean) = {
      new SimpleExpressionGrammar {
        def computeProductions(lab: Type) = {
          SimpleExpressionGrammar.this.computeProductions(lab).filter(f)
        }
      }
    }

    // Finalize this to depend only on the type of the label
    final def computeProductions(lab: Label): Seq[ProductionRule[Label, Expr]] = {
      computeProductions(lab.getType).map { p =>
        ProductionRule(p.subTrees.map(Label(_)), p.builder, p.tag, p.cost)
      }
    }

    /** Version of [[ExpressionGrammar.computeProductions]] which depends only a [[Type]] */
    def computeProductions(tpe: Type): Seq[Prod]
  }
}
