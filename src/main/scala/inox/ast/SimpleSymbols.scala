/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

trait SimpleSymbols { self: Trees =>

  override val NoSymbols = mkSymbols(Map.empty, Map.empty)

  // NOTE(gsps): [Inox issue] Inox used to declare val Symbols, but overrode it via a case class companion
  //  This led to two co-inciding methods at the bytecode level, which actually broke in dotc (but worked in scalac).
  def mkSymbols(functions: Map[Identifier, FunDef], sorts: Map[Identifier, ADTSort]): Symbols

  abstract class SimpleSymbols extends AbstractSymbols { self: Symbols =>

    override def withFunctions(functions: Seq[FunDef]): Symbols = mkSymbols(
      this.functions ++ functions.map(fd => fd.id -> fd),
      this.sorts
    )

    override def withSorts(sorts: Seq[ADTSort]): Symbols = mkSymbols(
      this.functions,
      this.sorts ++ sorts.map(s => s.id -> s)
    )
  }
}
