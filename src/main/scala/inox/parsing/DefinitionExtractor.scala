/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package parsing

trait DefinitionExtractors { self: Extractors =>

  trait DefinitionExtractor { self0: Extractor =>

    import DefinitionIR._

    def extract(fd: trees.FunDef, template: FunctionDefinition): Option[Match] = extract(
      toIdObl(fd.id -> template.id),
      toIdObls(fd.tparams.map(_.id) -> template.tparams),
      toBindingObls(fd.params, template.params),
      toTypeObl(fd.getType -> template.returnType),
      toExprObl(fd.fullBody -> template.body))

    def extract(sort: trees.ADTSort, template: TypeDefinition): Option[Match] = extract(
      toIdObl(sort.id -> template.id),
      toIdObls(sort.tparams.map(_.id) -> template.tparams),
      toIdObls(sort.constructors.map(_.id) -> template.constructors.map(_._1)),
      extract((sort.constructors zip template.constructors).map { case (cons, (_, fields)) =>
        toBindingObls(cons.fields -> fields)
      } : _*))
  }
}
