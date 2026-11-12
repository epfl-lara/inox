/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

trait SimpleSymbols { self: Trees =>

  override val NoSymbols = mkSymbols(Map.empty, Map.empty)

  def mkSymbols(functions: Map[Identifier, FunDef], sorts: Map[Identifier, ADTSort], modes: TypingModes): Symbols

  final def mkSymbols(functions: Map[Identifier, FunDef], sorts: Map[Identifier, ADTSort]): Symbols =
    mkSymbols(functions, sorts, TypingModes())

  abstract class SimpleSymbols(override val trees: self.type) extends AbstractSymbols { self0: Symbols =>
    def this() = this(self)

    override def withFunctions(functions: Seq[FunDef]): Symbols = mkSymbols(
      this.functions ++ functions.map(fd => fd.id -> fd),
      this.sorts,
      this.modes
    )

    override def withSorts(sorts: Seq[ADTSort]): Symbols = mkSymbols(
      this.functions,
      this.sorts ++ sorts.map(s => s.id -> s),
      this.modes
    )

    override def withModes(modes: TypingModes): Symbols =
      if (modes == this.modes) this else mkSymbols(this.functions, this.sorts, modes)
  }
}
