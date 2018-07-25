/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

import ast._

trait Interpolator
  extends Parsers
     with Elaborators
     with Extractors
     with ConstraintSolvers {

  import trees._

  class Converter(implicit val symbols: trees.Symbols)
    extends Elaborator
       with Extractor

  implicit class ExpressionInterpolator(sc: StringContext)(implicit symbols: trees.Symbols = trees.NoSymbols) {

    private lazy val converter = new Converter()
    private lazy val parser = new ExpressionParser()

    object e {
      def apply(args: Any*): Expr = {
        val ire = ir(args : _*)
        val expr = converter.getExpr(ire, Unknown.fresh(ire.pos))(Store.empty)
        converter.elaborate(expr)
      }

      def unapplySeq(expr: Expr): Option[Seq[Any]] = {
        val args = Seq.tabulate(sc.parts.length - 1)(MatchPosition(_))
        val ir = parser.getFromSC(sc, args)(parser.phrase(parser.expression))
        converter.extract(expr, ir) match {
          case Some(mappings) if mappings.size == sc.parts.length - 1 => Some(mappings.toSeq.sortBy(_._1).map(_._2))
          case _ => None
        }
      }
    }

    def ir(args: Any*): ExprIR.Expression = {
      parser.getFromSC(sc, args)(parser.phrase(parser.expression))
    }

    def v(args: Any*): ValDef = {
      val (id, ir) = parser.getFromSC(sc, args)(parser.phrase(parser.inoxValDef))
      val tpe = converter.getType(ir)(Store.empty)
      trees.ValDef(id, converter.elaborate(tpe))
    }

    def r(args: Any*): Seq[Lexer.Token] = {
      val reader = Lexer.getReader(sc, args)

      import scala.util.parsing.input.Reader 

      def go[A](r: Reader[A]): Seq[A] = {
        if (r.atEnd) Seq()
        else r.first +: go(r.rest)
      }

      go(reader)
    }

    object t {
      def apply(args: Any*): Type = {
        val ir = parser.getFromSC(sc, args)(parser.phrase(parser.typeExpression))
        val tpe = converter.getType(ir)(Store.empty)
        converter.elaborate(tpe)
      }

      def unapplySeq(tpe: Type): Option[Seq[Any]] = {
        val args = Seq.tabulate(sc.parts.length - 1)(MatchPosition(_))
        val ir = parser.getFromSC(sc, args)(parser.phrase(parser.typeExpression))
        converter.extract(tpe, ir) match {
          case Some(mappings) if mappings.size == sc.parts.length - 1 => Some(mappings.toSeq.sortBy(_._1).map(_._2))
          case _ => None
        }
      }
    }
  }
}
