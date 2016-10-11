/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

trait SimpleSymbols { self: Trees =>

  val NoSymbols = Symbols(Map.empty, Map.empty)

  val Symbols: (Map[Identifier, FunDef], Map[Identifier, ADTDefinition]) => Symbols

  abstract class SimpleSymbols extends AbstractSymbols { self: Symbols =>

    def withFunctions(functions: Seq[FunDef]): Symbols = Symbols(
      this.functions ++ functions.map(fd => fd.id -> fd),
      this.adts
    )

    def withADTs(adts: Seq[ADTDefinition]): Symbols = Symbols(
      this.functions,
      this.adts ++ adts.map(adt => adt.id -> adt)
    )
  }
}
