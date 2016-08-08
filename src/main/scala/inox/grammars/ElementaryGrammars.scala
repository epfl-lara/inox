/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package grammars

trait ElementaryGrammars { self: GrammarsUniverse =>
  import program.trees._
  import program.symbols._

  /** Generates one production rule for each expression in a sequence that has compatible type */
  case class OneOf(inputs: Seq[Expr]) extends SimpleExpressionGrammar {
    def computeProductions(lab: Type): Seq[Prod] = {
      inputs.collect {
        case i if isSubtypeOf(i.getType, lab.getType) =>
          terminal(i)
      }
    }
  }

  case class Union(gs: Seq[ExpressionGrammar]) extends ExpressionGrammar {
    val subGrammars: Seq[ExpressionGrammar] = gs.flatMap {
      case u: Union => u.subGrammars
      case g => Seq(g)
    }

    def computeProductions(label: Label): Seq[ProductionRule[Label, Expr]] =
      subGrammars.flatMap(_.computeProductions(label))
  }

  /** The empty expression grammar */
  case class Empty() extends ExpressionGrammar {
    def computeProductions(l: Label) = Nil
  }

}

