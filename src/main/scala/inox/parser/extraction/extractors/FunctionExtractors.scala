package inox
package parser
package extraction
package extractors

trait FunctionExtractors { self: Extractors =>

  import Functions.Function
  implicit object FunctionX extends Extractor[Function, trees.FunDef, Unit] {
    override def extract(template: Function, scrutinee: trees.FunDef): Matching[Unit] = {
      DefIdX.extract(template.identifier, scrutinee.id).flatMap { optName =>
        DefIdSeqX.extract(template.typeParams, scrutinee.tparams.map(_.id)).flatMap { optTypeParams =>
          BindingSeqX.extract(template.params, scrutinee.params).flatMap { optParams =>
            Matching.optionally(template.returnType.map(st => TypeX.extract(st, scrutinee.returnType))) <>
            ExprX.extract(template.body, scrutinee.fullBody).extendLocal(optParams.flatten).extendLocal(optName.toSeq)
          }.extendLocal(optTypeParams.flatten)
        }
      }
    }
  }
}