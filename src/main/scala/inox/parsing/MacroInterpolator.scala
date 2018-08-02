package inox
package parsing

import scala.reflect.macros.whitebox.Context

import scala.language.experimental.macros

object MacroInterpolators
  extends Interpolators
     with Elaborators
     with Extractors {

  val trees = inox.trees

  import trees._

  class Converter(implicit val symbols: Symbols)
    extends Elaborator
       with Extractor

  implicit class Interpolator(sc: StringContext)(implicit val symbols: Symbols = NoSymbols) {

    val converter = new Converter()

    object t {
      def apply(args: Any*): Type = macro MacroInterpolatorsImpl.t_apply

      def unapply(arg: Type): Option[Any] = macro MacroInterpolatorsImpl.t_unapply
    }

    object e {
      def apply(args: Any*): Expr = macro MacroInterpolatorsImpl.e_apply

      def unapply(arg: Expr): Option[Any] = macro MacroInterpolatorsImpl.e_unapply
    }
  }
}

private class MacroInterpolatorsImpl(context: Context) extends Macros(context) {
  import c.universe._
  override protected val trees = inox.trees
  override protected lazy val targetTrees: c.Tree = q"_root_.inox.trees"
  override protected val interpolator: c.Tree = q"_root_.inox.parsing.MacroInterpolators"
}