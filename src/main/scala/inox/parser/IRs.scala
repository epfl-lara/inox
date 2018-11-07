package inox
package parser

import scala.util.parsing.input.Positional

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

  trait HoleType
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

  trait IR extends Positional with Product {
    def getHoles: Seq[Hole]

    override def toString: String = {
      productPrefix + "(" + productIterator.map(_.toString).mkString(",") + ")@" + pos.toString
    }
  }

  trait HoleTypable[-A <: IR] {
    val holeType: HoleType
  }

  case class RepHole[+A <: IR : HoleTypable](index: Int) extends IR {
    override def getHoles = Seq(Hole(index, HoleTypes.Sequence(implicitly[HoleTypable[A]].holeType)))
  }

  case class HSeq[+A <: IR : HoleTypable](elems: Seq[Either[RepHole[A], A]]) extends IR {

    def size = elems.size

    override def getHoles: Seq[Hole] = elems.flatMap {
      case Left(r) => r.getHoles
      case Right(x) => x.getHoles
    }
  }

  object HSeq {
    def fromSeq[A <: IR : HoleTypable](xs: Seq[A]): HSeq[A] = HSeq(xs.map(Right(_)))
  }
}