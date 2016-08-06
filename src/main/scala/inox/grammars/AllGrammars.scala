package inox.grammars

trait AllGrammars extends ElementaryGrammars
  with BaseGrammars
  with ValueGrammars
  with ConstantGrammars
  with ClosureGrammars
  with EqualityGrammars
  with FunctionCallsGrammars {
    self: GrammarsUniverse =>
}
