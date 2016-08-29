/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

trait SimpleSymbols { self: Trees =>

  val NoSymbols = new Symbols(Map.empty, Map.empty)

  class Symbols(
    val functions: Map[Identifier, FunDef],
    val adts: Map[Identifier, ADTDefinition]
  ) extends AbstractSymbols {

    def withFunctions(functions: Seq[FunDef]): Symbols = new Symbols(
      this.functions ++ functions.map(fd => fd.id -> fd),
      this.adts
    )

    def withADTs(adts: Seq[ADTDefinition]): Symbols = new Symbols(
      this.functions,
      this.adts ++ adts.map(adt => adt.id -> adt)
    )
  }
}
