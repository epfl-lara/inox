/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

trait Extractors
  extends IRs
     with ExpressionDeconstructors
     with TypeDeconstructors
     with ExpressionExtractors
     with DefinitionExtractors
     with TypeExtractors {

  trait Extractor
    extends ExpressionDeconstructor
       with TypeDeconstructor
       with ExpressionExtractor
       with DefinitionExtractor
       with TypeExtractor {

    type Match = Map[Int, Any]

    def matching(index: Int, value: Any): Match = Map(index -> value)
    val empty: Match = Map()
    val success = Some(Map[Int, Any]())
    val fail = None
  }
}
