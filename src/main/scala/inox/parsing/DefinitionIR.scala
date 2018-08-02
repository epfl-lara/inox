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
      override def productPrefix = pos + "@" + pre
    }

    case class FunctionDefinition(
      id: Identifier,
      tparams: Seq[Identifier],
      params: Seq[(Identifier, Type)],
      returnType: Type,
      body: Expression
    ) extends Definition("Function")

    case class TypeDefinition(
      id: Identifier,
      tparams: Seq[Identifier],
      constructors: Seq[(Identifier, Seq[(Identifier, Type)])]
    ) extends Definition("Type")

    def getHoleTypes(definition: Definition): Map[Int, HoleType] = definition match {
      case FunctionDefinition(id, tparams, params, returnType, body) => {
        val idMap = ExprIR.getHoleTypes(id)
        val tparamsMaps = tparams.map(ExprIR.getHoleTypes(_))
        val paramsMaps = params.map {
          case (pid, ptype) => ExprIR.getHoleTypes(pid) ++ TypeIR.getHoleTypes(ptype)
        }
        val returnTypeMap = TypeIR.getHoleTypes(returnType)
        val bodyMap = ExprIR.getHoleTypes(body)

        (tparamsMaps ++ paramsMaps).fold(idMap ++ bodyMap ++ returnTypeMap)(_ ++ _)
      }
      case TypeDefinition(id, tparams, constructors) => {
        val idMap = ExprIR.getHoleTypes(id)
        val tparamsMaps = tparams.map(ExprIR.getHoleTypes(_))
        val constructorsMaps = constructors.map {
          case (cid, cparams) => {
            val cidMap = ExprIR.getHoleTypes(cid)
            val cparamsMaps = cparams.map {
              case (pid, ptype) => ExprIR.getHoleTypes(pid) ++ TypeIR.getHoleTypes(ptype)
            }
            cparamsMaps.fold(cidMap)(_ ++ _)
          }
        }

        (tparamsMaps ++ constructorsMaps).fold(idMap)(_ ++ _)
      }
    }
  }
}
