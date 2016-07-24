/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package grammars

trait EqualityGrammars { self: GrammarsUniverse =>
  import program._
  import trees._
  import symbols._

  /** A grammar of equalities
    *
    * @param types The set of types for which equalities will be generated
    */
  case class EqualityGrammar(types: Set[Type]) extends SimpleExpressionGrammar {
    def computeProductions(t: Type)(implicit ctx: InoxContext): Seq[Prod] = t match {
      case BooleanType =>
        types.toList map { tp =>
          nonTerminal(List(tp, tp), { case Seq(a, b) => equality(a, b) }, Equals)
        }

      case _ => Nil
    }
  }
}
