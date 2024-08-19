/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package parsing

trait DefinitionExtractors { self: Extractors =>

  trait DefinitionExtractor { self0: Extractor =>
    import symbols.given
    import DefinitionIR._

    def extract(fd: trees.FunDef, template: FunDef): Option[Match] = extract(
      toIdObl(fd.id -> template.id),
      toIdObls(fd.tparams.map(_.id) -> template.tparams),
      toIdObls(fd.params.map(_.id) -> template.params.map(_._1)),
      toTypeObls(fd.params.map(_.getType) -> template.params.map(_._2)),
      toTypeObl(fd.getType -> template.returnType),
      toExprObl(fd.fullBody -> template.body))

    def extract(sort: trees.ADTSort, template: TypeDef): Option[Match] = extract(
      toIdObl(sort.id -> template.id),
      toIdObls(sort.tparams.map(_.id) -> template.tparams),
      toIdObls(sort.constructors.map(_.id) -> template.constructors.map(_._1)),
      extract((sort.constructors zip template.constructors).map { case (cons, (_, fields)) =>
        extract(
          toIdObls(cons.fields.map(_.id) -> fields.map(_._1)),
          toTypeObls(cons.fields.map(_.getType) -> fields.map(_._2))
        )
      }*))
  }
}
