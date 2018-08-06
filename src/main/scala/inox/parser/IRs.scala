package inox
package parser

import irs._

trait IRs
  extends Exprs
     with Identifiers
     with Bindings
     with Types {

  sealed trait HoleType
  object HoleTypes {
    case object Identifier extends HoleType
    case object Type extends HoleType
    case object Expr extends HoleType
    case object ValDef extends HoleType
    case class Sequence(inner: HoleType) extends HoleType
  }

  case class Hole(index: Int, holeType: HoleType)

  trait IR {
    def getHoles: Seq[Hole]
  }

  class HSeq[+A <: IR](val elems: Seq[Either[Int, A]], val holeType: HoleType) extends IR {
    def size = elems.size

    override def getHoles: Seq[Hole] = elems.flatMap {
      case Left(index) => Seq(Hole(index, HoleTypes.Sequence(holeType)))
      case Right(x) => x.getHoles
    }
  }
}