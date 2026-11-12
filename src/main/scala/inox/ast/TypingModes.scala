/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

/** Whether quantifiers are booleans or propositions.
  *
  * - [[QuantifierMode.Boolean]]: a `Forall` is a boolean, which evaluators compute by calling a
  *   solver. Quantifiers can then appear anywhere a boolean can.
  * - [[QuantifierMode.Propositional]]: a `Forall` is a proposition (see `PropType`). It has a
  *   truth value but no evaluation rule, and can't be used as a value.
  */
enum QuantifierMode {
  case Boolean, Propositional
}

/** The modes of a symbol table, which the typing of its trees depends on.
  *
  * They belong to the symbols, and not to the options of a context, so that a program can't be
  * typed under one semantics and solved or evaluated under another. Symbol tables that are
  * derived from another one keep its modes.
  */
case class TypingModes(quantifiers: QuantifierMode = QuantifierMode.Boolean)

/** Selects the [[QuantifierMode]] of the programs that are built from the inputs of a context. */
object optQuantifiers extends OptionDef[QuantifierMode] {
  val name: String = "quantifiers"
  val usageRhs: String = "boolean|propositional"
  val default: QuantifierMode = QuantifierMode.Boolean
  override def formatDefault: String = default.toString.toLowerCase

  override def parser: OptionParsers.OptionParser[QuantifierMode] = s =>
    QuantifierMode.values.find(_.toString.toLowerCase == s.toLowerCase)
}
