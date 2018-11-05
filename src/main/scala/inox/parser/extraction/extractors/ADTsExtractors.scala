package inox
package parser
package extraction
package extractors

trait ADTsExtractors { self: Extractors =>

  import ADTs._
  class SortX extends Extractor[Sort, trees.ADTSort, Unit] {
    override def extract(template: Sort, scrutinee: trees.ADTSort): Matching[Unit] =
      DefIdX.extract(template.identifier, scrutinee.id).flatMap { optPair =>
        DefIdSeqX.extract(template.typeParams, scrutinee.tparams.map(_.id)).flatMap { optPairs =>
          ConstructorSeqX.extract(template.constructors, scrutinee.constructors)
            .extendLocal(optPair.toSeq ++ optPairs.flatten, isType=true)
            .withValue(())
        }
      }
  }
  val SortX = new SortX

  class ConstructorX extends Extractor[Constructor, trees.ADTConstructor, Unit] {
    override def extract(template: Constructor, scrutinee: trees.ADTConstructor): Matching[Unit] = template match {
      case ConstructorValue(templateIdentifier, templateParams) =>
        DefIdX.extract(templateIdentifier, scrutinee.id) <>
        BindingSeqX.extract(templateParams, scrutinee.fields)
      case ConstructorHole(index) => Matching(index -> scrutinee)
    }
  }
  val ConstructorX = new ConstructorX

  class ConstructorSeqX extends HSeqX[Constructor, trees.ADTConstructor, Unit](ConstructorX, ())
  val ConstructorSeqX = new ConstructorSeqX
}