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
     with BindingExtractors
     with ExprExtractors
     with FunctionExtractors
     with ADTsExtractors
     with NumberUtils {

  trait Extractor[-A, -B, +R] {
    def extract(template: A, scrutinee: B): Matching[R]
  }

  class HSeqX[-A <: IR, -B, +R](extractor: Extractor[A, B, R], default: R) extends Extractor[HSeq[A], Seq[B], Seq[R]] {
    override def extract(template: HSeq[A], scrutinee: Seq[B]): Matching[Seq[R]] = {
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
          val firstIndex = suffix.head.left.get.index
          val rest = suffix.tail

          val (firstParts, restParts) = suffixParts.splitAt(scrutinee.size - minSize)

          val (restMatchings, Seq()) = rest.foldLeft((Seq[Matching[R]](), restParts)) {
            case ((acc, rest), Left(r)) => (acc :+ Matching(r.index -> Seq()).withValue(default), rest)
            case ((acc, rest), Right(elem)) => (acc :+ extractor.extract(elem, rest.head), rest.tail)
          }

          prefixMatchings ++ (Matching(firstIndex -> firstParts).withValue(default) +: restMatchings)
        }


        Matching.sequence(matchings)
      }
    }
  }
}