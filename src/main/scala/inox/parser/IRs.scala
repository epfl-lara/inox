package inox
package parser

import irs._

trait IRs
  extends Exprs
     with Identifiers
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
}