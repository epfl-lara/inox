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
    case class Pair(lhs: HoleType, rhs: HoleType) extends HoleType
    case class Sequence(inner: HoleType) extends HoleType
  }

  case class Hole(index: Int, holeType: HoleType)

  trait IR {
    def getHoles: Seq[Hole]
  }

  trait HoleTypable[A <: IR] {
    val holeType: HoleType
  }

  final class HSeq[+A <: IR : HoleTypable](val elems: Seq[Either[Int, A]]) extends IR {

    def size = elems.size
    private val holeType = HoleTypes.Sequence(implicitly[HoleTypable[A]].holeType)

    override def getHoles: Seq[Hole] = elems.flatMap {
      case Left(index) => Seq(Hole(index, holeType))
      case Right(x) => x.getHoles
    }
  }
}