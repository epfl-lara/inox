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

  class Converter(using val symbols: trees.Symbols)
    extends Elaborator
       with Extractor

  implicit class ExpressionInterpolator(sc: StringContext)(using symbols: trees.Symbols = trees.NoSymbols) {
    private lazy val converter = new Converter()
    private lazy val parser = new DefinitionParser()

    object e {
      def apply(args: Any*): Expr = {
        val ire = ir(args : _*)
        val expr = converter.getExpr(ire, Unknown.fresh(using ire.pos))(using Store.empty)
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
      val tpe = converter.getType(ir)(using Store.empty)
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
        val tpe = converter.getType(ir)(using Store.empty)
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

    object td {
      def apply(args: Any*): ADTSort = {
        val ir = parser.getFromSC(sc, args)(parser.phrase(parser.datatype))
        val srt = converter.getSort(ir)(using Store.empty)
        converter.elaborate(srt)
      }

      def unapplySeq(sort: ADTSort): Option[Seq[Any]] = {
        val args = Seq.tabulate(sc.parts.length - 1)(MatchPosition(_))
        val ir = parser.getFromSC(sc, args)(parser.phrase(parser.datatype))
        converter.extract(sort, ir) match {
          case Some(mappings) if mappings.size == sc.parts.length - 1 => Some(mappings.toSeq.sortBy(_._1).map(_._2))
          case _ => None
        }
      }
    }

    object fd {
      def apply(args: Any*): FunDef = {
        val ir = parser.getFromSC(sc, args)(parser.phrase(parser.function))
        val fundef = converter.getFunction(ir)(using Store.empty)
        converter.elaborate(fundef)
      }

      def unapplySeq(fun: FunDef): Option[Seq[Any]] = {
        val args = Seq.tabulate(sc.parts.length - 1)(MatchPosition(_))
        val ir = parser.getFromSC(sc, args)(parser.phrase(parser.function))
        converter.extract(fun, ir) match {
          case Some(mappings) if mappings.size == sc.parts.length - 1 => Some(mappings.toSeq.sortBy(_._1).map(_._2))
          case _ => None
        }
      }
    }
  }
}
