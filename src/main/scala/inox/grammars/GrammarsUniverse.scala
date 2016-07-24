package inox
package grammars

trait GrammarsUniverse extends Tags
  with Productions
  with Aspects
  with aspects.PersistentAspects
  with aspects.AllAspects
  with Labels
  with ExpressionGrammars
  with SimpleExpressionGrammars
  with AllGrammars
{
  val program: Program
}
