package inox
package parser

import extraction._
import extractors._

trait Extractors
  extends Trees
     with IRs
     with Matchings
     with IdentifierExtractors
     with TypeExtractors
     with ExprExtractors {

  trait Extractor[-A, -B] {
    def extract(template: A, scrutinee: B): Matching
  }
}