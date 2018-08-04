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

  trait Extractor[-A <: IR, -B] {
    def extract(template: A, scrutinee: B): Matching
  }

  implicit class ExtractorDecorator[-A <: IR, -B](template: A)(implicit extractor: Extractor[A, B]) {
    def extract(scrutinee: B): Matching = extractor.extract(template, scrutinee)
  }

  class HSeqX[A <: IR, B](extractor: Extractor[A, B]) extends Extractor[HSeq[A], Seq[B]] {
    override def extract(template: HSeq[A], scrutinee: Seq[B]): Matching = {
      val elems = template.elems
      val minSize = elems.count(_.isRight)
      if (scrutinee.size < minSize) {
        Matching.fail
      }
      else {
        val (prefix, suffix) = elems.span(_.isRight)
        val (prefixParts, suffixParts) = scrutinee.splitAt(prefix.size)

        val prefixMatchings = prefix.zip(prefixParts).map {
          case (elem, part) => extractor.extract(elem.right.get, part)
        }

        val matchings = if (suffix.isEmpty) {
          prefixMatchings
        }
        else {
          val firstIndex = suffix.head.left.get
          val rest = suffix.tail

          val (firstParts, restParts) = suffixParts.splitAt(minSize - prefix.size)

          val (restMatchings, Seq()) = rest.foldLeft((Seq[Matching](), restParts)) {
            case ((acc, rest), Left(index)) => (acc :+ Matching(index -> Seq()), rest)
            case ((acc, rest), Right(elem)) => (acc :+ extractor.extract(elem, rest.head), rest.tail)
          }

          prefixMatchings ++ (Matching(firstIndex -> firstParts) +: restMatchings)
        }


        matchings.fold(Matching.success)(_ <> _)
      }
    }
  }
}