/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

trait SimpleSymbols { self: Trees =>

  override val NoSymbols = Symbols(Map.empty, Map.empty)

  val Symbols: (Map[Identifier, FunDef], Map[Identifier, ADTSort]) => Symbols

  abstract class SimpleSymbols extends AbstractSymbols { self: Symbols =>

    override def withFunctions(functions: Seq[FunDef]): Symbols = Symbols(
      this.functions ++ functions.map(fd => fd.id -> fd),
      this.sorts
    )

    override def withSorts(sorts: Seq[ADTSort]): Symbols = Symbols(
      this.functions,
      this.sorts ++ sorts.map(s => s.id -> s)
    )
  }
}
