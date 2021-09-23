/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package parsing

import scala.util.parsing.input.Positional

trait DefinitionIRs { self: IRs =>

  /** IR for definitions. */
  object DefinitionIR {

    import ExprIR.{Identifier, Expression}
    import TypeIR.{Expression => Type}

    sealed abstract class Definition(pre: String) extends Positional with Product {
      override def productPrefix = s"$pos@$pre"
    }

    case class FunDef(
      id: Identifier,
      tparams: Seq[Identifier],
      params: Seq[(Identifier, Type)],
      returnType: Type,
      body: Expression
    ) extends Definition("Function")

    case class TypeDef(
      id: Identifier,
      tparams: Seq[Identifier],
      constructors: Seq[(Identifier, Seq[(Identifier, Type)])]
    ) extends Definition("Type")
  }
}
