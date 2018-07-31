package inox
package parsing

trait HoleType
case object IdentifierHoleType extends HoleType
case object ExpressionHoleType extends HoleType
case object TypeHoleType extends HoleType
case class SeqHoleType(holeType: HoleType) extends HoleType