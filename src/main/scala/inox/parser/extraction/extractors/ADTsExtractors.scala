package inox
package parser
package extraction
package extractors

trait ADTsExtractors { self: Extractors =>

  import ADTs._
  object SortX extends Extractor[Sort, trees.ADTSort, Unit] {
    override def extract(template: Sort, scrutinee: trees.ADTSort): Matching[Unit] =
      DefIdX.extract(template.identifier, scrutinee.id).flatMap { optPair =>
        DefIdSeqX.extract(template.typeParams, scrutinee.tparams.map(_.id)).flatMap { optPairs =>
          ConstructorSeqX.extract(template.constructors, scrutinee.constructors)
            .extendLocal(optPair.toSeq ++ optPairs.flatten)
            .withValue(())
        }
      }
  }

  object ConstructorX extends Extractor[Constructor, trees.ADTConstructor, Unit] {
    override def extract(template: Constructor, scrutinee: trees.ADTConstructor): Matching[Unit] =
      DefIdX.extract(template.identifier, scrutinee.id) <>
      BindingSeqX.extract(template.params, scrutinee.fields)
  }

  object ConstructorSeqX extends HSeqX[Constructor, trees.ADTConstructor, Unit](ConstructorX, ())
}