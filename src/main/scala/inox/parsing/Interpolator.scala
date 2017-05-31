/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

import ast._

trait Interpolator extends BuiltIns
                      with Constraints
                      with TypeIRs
                      with ExprIRs
                      with ConstraintSolvers
                      with Lexers
                      with TypeParsers
                      with ExpressionParsers {

  protected val trees: Trees

  import trees._

  implicit class ExpressionInterpolator(sc: StringContext)(implicit symbols: trees.Symbols = trees.NoSymbols) {

    private lazy val convertor = new ExpressionConvertor(symbols)
    private lazy val parser = new ExpressionParser()

    object e {
      def apply(args: Any*): Expr = {
        convertor.getExpr(ir(args : _*))
      }

      def unapplySeq(expr: Expr): Option[Seq[Any]] = {
        val args = Seq.tabulate(sc.parts.length - 1)(MatchPosition(_))
        val ir = parser.getFromSC(sc, args)(parser.phrase(parser.expression))
        convertor.extract(expr, ir) match {
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
      trees.ValDef(id, convertor.getType(ir))
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
        convertor.getType(ir)
      }

      def unapplySeq(tpe: Type): Option[Seq[Any]] = {
        val args = Seq.tabulate(sc.parts.length - 1)(MatchPosition(_))
        val ir = parser.getFromSC(sc, args)(parser.phrase(parser.typeExpression))
        convertor.extract(tpe, ir) match {
          case Some(mappings) if mappings.size == sc.parts.length - 1 => Some(mappings.toSeq.sortBy(_._1).map(_._2))
          case _ => None
        }
      }
    }
  }
}