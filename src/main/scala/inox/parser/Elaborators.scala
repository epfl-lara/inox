package inox
package parser

import elaboration._
import elaborators._

trait Elaborators
  extends Trees
     with IRs
     with SimpleTypes
     with Constraints
     with ExprElaborators
     with TypeElaborators
     with IdentifierElaborators {

  trait Store {
    def getIdentifier(name: String): Constrained[inox.Identifier]
    def getSort(identifier: inox.Identifier): Constrained[trees.ADTSort]
    def getHole[A: Manifest](index: Int): Constrained[A]
  }

  trait Elaborator[-A <: IR, -C, +R] {
    def elaborate(template: A, context: C)(implicit store: Store): Constrained[R]
  }

  implicit class ElaborateDecorator[-A <: IR, -C, +R](template: A)(implicit elaborator: Elaborator[A, C, R]) {
    def elaborate(context: C)(implicit store: Store): Constrained[R] = elaborator.elaborate(template, context)(store)
  }

  class HSeqE[A <: IR, C, R: Manifest](elaborator: Elaborator[A, C, R]) extends Elaborator[HSeq[A], Seq[C], Seq[R]] {
    override def elaborate(template: HSeq[A], contexts: Seq[C])(implicit store: Store): Constrained[Seq[R]] = {
      val elems = template.elems
      require(elems.size == contexts.size)

      Constrained.sequence(elems.zip(contexts).map {
        case (Left(index), _) => store.getHole[Seq[R]](index)
        case (Right(t), c) => elaborator.elaborate(t, c).map(Seq(_))
      }).map(_.flatten)
    }
  }
}