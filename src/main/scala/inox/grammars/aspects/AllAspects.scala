package inox.grammars
package aspects

trait AllAspects extends SizeAspects
  with ExtraTerminalsAspects
  with SimilarToAspects
  with DepthBoundAspects
  with TypeDepthBoundAspects
  with TaggedAspects
{
  self: GrammarsUniverse =>
}
