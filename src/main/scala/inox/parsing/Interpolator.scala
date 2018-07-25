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

  class Elaborator(implicit val symbols: trees.Symbols)
    extends ExpressionElaborator
       with TypeElaborator
       with ExpressionConverter
       with TypeConverter {

    lazy val solver = new Solver

    class ElaborationException(val errors: Seq[ErrorLocation])
      extends Exception(errors.map(_.toString).mkString("\n\n"))

    def elaborate[A](c: Constrained[A]): A = c match {
      case Unsatisfiable(es) => throw new ElaborationException(es)
      case WithConstraints(ev, constraints) =>
        implicit val u = solver.solveConstraints(constraints)
        ev
    }
  }

  implicit class ExpressionInterpolator(sc: StringContext)(implicit symbols: trees.Symbols = trees.NoSymbols) {

    private lazy val elaborator = new Elaborator()
    private lazy val parser = new ExpressionParser()

    object e {
      def apply(args: Any*): Expr = {
        val ire = ir(args : _*)
        val expr = elaborator.getExpr(ire, Unknown.fresh(ire.pos))(Store.empty)
        elaborator.elaborate(expr)
      }

      def unapplySeq(expr: Expr): Option[Seq[Any]] = {
        val args = Seq.tabulate(sc.parts.length - 1)(MatchPosition(_))
        val ir = parser.getFromSC(sc, args)(parser.phrase(parser.expression))
        elaborator.extract(expr, ir) match {
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
      val tpe = elaborator.getType(ir)(Store.empty)
      trees.ValDef(id, elaborator.elaborate(tpe))
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
        val tpe = elaborator.getType(ir)(Store.empty)
        elaborator.elaborate(tpe)
      }

      def unapplySeq(tpe: Type): Option[Seq[Any]] = {
        val args = Seq.tabulate(sc.parts.length - 1)(MatchPosition(_))
        val ir = parser.getFromSC(sc, args)(parser.phrase(parser.typeExpression))
        elaborator.extract(tpe, ir) match {
          case Some(mappings) if mappings.size == sc.parts.length - 1 => Some(mappings.toSeq.sortBy(_._1).map(_._2))
          case _ => None
        }
      }
    }
  }
}
