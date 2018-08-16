package inox
package parser

import irs._

trait IRs
  extends Exprs
     with Identifiers
     with Bindings
     with Types
     with Functions
     with ADTs
     with Programs {

  type ErrorMessage = String

  sealed trait HoleType
  object HoleTypes {
    case object Identifier extends HoleType
    case object Type extends HoleType
    case object Expr extends HoleType
    case object ValDef extends HoleType
    case object Constructor extends HoleType
    case class Pair(lhs: HoleType, rhs: HoleType) extends HoleType
    case class Sequence(inner: HoleType) extends HoleType
  }

  case class Hole(index: Int, holeType: HoleType)

  trait IR {
    def getHoles: Seq[Hole]
  }

  trait HoleTypable[-A <: IR] {
    val holeType: HoleType
  }

  final class HSeq[+A <: IR : HoleTypable](val elems: Seq[Either[Int, A]]) extends IR {

    def size = elems.size
    private val holeType = HoleTypes.Sequence(implicitly[HoleTypable[A]].holeType)

    override def getHoles: Seq[Hole] = elems.flatMap {
      case Left(index) => Seq(Hole(index, holeType))
      case Right(x) => x.getHoles
    }

    override def toString: String = {
      def go(x: Either[Int, A]): String = x match {
        case Left(index) => "$" + index + "..."
        case Right(elem) => elem.toString
      }

      "HSeq(" + elems.map(go).mkString(",") + ")"
    }
  }

  object HSeq {
    def fromSeq[A <: IR : HoleTypable](xs: Seq[A]): HSeq[A] = new HSeq(xs.map(Right(_)))

    def apply[A <: IR : HoleTypable](xs: Either[Int, A]*): HSeq[A] = new HSeq(xs)

    def unapply[A <: IR](arg: HSeq[A]): Option[Seq[Either[Int, A]]] =
      Some(arg.elems)
  }
}