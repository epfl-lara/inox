package inox
package parsing

import scala.language.experimental.macros

object MacroInterpolator
  extends Elaborators
     with Extractors
     with ConstraintSolvers {

  val trees = inox.trees

  import trees._

  class Converter(implicit val symbols: Symbols)
    extends Elaborator
       with Extractor

  implicit class ExpressionInterpolator(sc: StringContext)(implicit val symbols: Symbols = NoSymbols) {

    val converter = new Converter()

    object t {
      def apply(args: Any*): Type = macro Macros.t_apply

      def unapply(arg: Type): Option[Any] = macro Macros.t_unapply
    }

    object e {
      def apply(args: Any*): Expr = macro Macros.e_apply
    }
  }
}