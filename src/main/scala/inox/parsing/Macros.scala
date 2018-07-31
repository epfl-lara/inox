package inox
package parsing

import scala.reflect.macros.whitebox.Context
import scala.language.experimental.macros


class Macros(val c: Context) extends Parsers with IRs {

  import c.universe._

  implicit lazy val quantifierLiftable = Liftable[ExprIR.Quantifier] {
    case ExprIR.Lambda => q"_root_.inox.parsing.MacroInterpolator.ExprIR.Lambda"
    case ExprIR.Forall => q"_root_.inox.parsing.MacroInterpolator.ExprIR.Forall"
    case ExprIR.Exists => q"_root_.inox.parsing.MacroInterpolator.ExprIR.Exists"
    case ExprIR.Choose => q"_root_.inox.parsing.MacroInterpolator.ExprIR.Choose"
  }

  implicit lazy val fieldLiftable = Liftable[ExprIR.Field] {
    case ExprIR.FieldName(name) => q"_root_.inox.parsing.MacroInterpolator.ExprIR.FieldName($name)"
    case ExprIR.FieldHole(index) => q"_root_.inox.parsing.MacroInterpolator.ExprIR.FieldHole($index)"
    case _ => throw new Error("Unexpected construct.")
  }

  implicit lazy val identifierLiftable = Liftable[ExprIR.Identifier] {
    case ExprIR.IdentifierName(name) => q"_root_.inox.parsing.MacroInterpolator.ExprIR.IdentifierName($name)"
    case ExprIR.IdentifierHole(index) => q"_root_.inox.parsing.MacroInterpolator.ExprIR.IdentifierHole($index)"
    case _ => throw new Error("Unexpected construct.")
  }

  implicit lazy val exprIRLiftable: Liftable[ExprIR.Expression] = Liftable[ExprIR.Expression] {
    case ExprIR.Variable(id) =>
      q"_root_.inox.parsing.MacroInterpolator.ExprIR.Variable($id)"
    case ExprIR.Application(callee, args) =>
      q"_root_.inox.parsing.MacroInterpolator.ExprIR.Application($callee, _root_.scala.collection.immutable.Seq(..$args))"
    case ExprIR.Abstraction(quantifier, bindings, body) =>
      q"_root_.inox.parsing.MacroInterpolator.ExprIR.Abstraction($quantifier, _root_.scala.collection.immutable.Seq(..$bindings), $body)"
    case ExprIR.Operation(operator, args) =>
      q"_root_.inox.parsing.MacroInterpolator.ExprIR.Operation($operator, _root_.scala.collection.immutable.Seq(..$args))"
    case ExprIR.Selection(structure, field) =>
      q"_root_.inox.parsing.MacroInterpolator.ExprIR.Selection($structure, $field)"
    case ExprIR.TypeApplication(callee, args) =>
      q"_root_.inox.parsing.MacroInterpolator.ExprIR.TypeApplication($callee, _root_.scala.collection.immutable.Seq(..$args))"
    case ExprIR.Let(bindings, body) =>
      q"_root_.inox.parsing.MacroInterpolator.ExprIR.Let(_root_.scala.collection.immutable.Seq(..$bindings), $body)"
    case ExprIR.Literal(ExprIR.NumericLiteral(value)) =>
      q"_root_.inox.parsing.MacroInterpolator.ExprIR.Literal(_root_.inox.parsing.MacroInterpolator.ExprIR.NumericLiteral($value))"
    case ExprIR.Literal(ExprIR.DecimalLiteral(whole, trailing, repeating)) =>
      q"_root_.inox.parsing.MacroInterpolator.ExprIR.Literal(_root_.inox.parsing.MacroInterpolator.ExprIR.DecimalLiteral($whole, $trailing, $repeating))"
    case ExprIR.Literal(ExprIR.StringLiteral(value)) =>
      q"_root_.inox.parsing.MacroInterpolator.ExprIR.Literal(_root_.inox.parsing.MacroInterpolator.ExprIR.StringLiteral($value))"
    case ExprIR.Literal(ExprIR.BooleanLiteral(value)) =>
      q"_root_.inox.parsing.MacroInterpolator.ExprIR.Literal(_root_.inox.parsing.MacroInterpolator.ExprIR.BooleanLiteral($value))"
    case ExprIR.Literal(ExprIR.CharLiteral(value)) =>
      q"_root_.inox.parsing.MacroInterpolator.ExprIR.Literal(_root_.inox.parsing.MacroInterpolator.ExprIR.CharLiteral($value))"
    case ExprIR.Literal(ExprIR.UnitLiteral) =>
      q"_root_.inox.parsing.MacroInterpolator.ExprIR.Literal(_root_.inox.parsing.MacroInterpolator.ExprIR.UnitLiteral)"
    case ExprIR.ExpressionHole(index) =>
      q"_root_.inox.parsing.MacroInterpolator.ExprIR.ExpressionHole($index)"
    case ExprIR.ExpressionSeqHole(index) =>
      q"_root_.inox.parsing.MacroInterpolator.ExprIR.ExpressionSeqHole($index)"
  }

  implicit lazy val typeOperatorLiftable = Liftable[TypeIR.Operator] {
    case TypeIR.Group => q"_root_.inox.parsing.MacroInterpolator.TypeIR.Group"
    case TypeIR.Tuple => q"_root_.inox.parsing.MacroInterpolator.TypeIR.Tuple"
    case TypeIR.Sigma => q"_root_.inox.parsing.MacroInterpolator.TypeIR.Sigma"
    case TypeIR.Arrow => q"_root_.inox.parsing.MacroInterpolator.TypeIR.Arrow"
    case TypeIR.Pi => q"_root_.inox.parsing.MacroInterpolator.TypeIR.Pi"
  }

  implicit lazy val typeIRLiftable: Liftable[TypeIR.Expression] = Liftable[TypeIR.Expression] {
    case TypeIR.Literal(TypeIR.Name(name)) =>
      q"_root_.inox.parsing.MacroInterpolator.TypeIR.Literal(_root_.inox.parsing.MacroInterpolator.TypeIR.Name($name))"
    case TypeIR.Application(callee, args) =>
      q"_root_.inox.parsing.MacroInterpolator.TypeIR.Application($callee, _root_.scala.collection.immutable.Seq(..$args))"
    case TypeIR.Operation(operator, args) =>
      q"_root_.inox.parsing.MacroInterpolator.TypeIR.Operation($operator, _root_.scala.collection.immutable.Seq(..$args))"
    case TypeIR.TypeHole(index) =>
      q"_root_.inox.parsing.MacroInterpolator.TypeIR.TypeHole($index)"
    case TypeIR.NameHole(index) =>
      q"_root_.inox.parsing.MacroInterpolator.TypeIR.NameHole($index)"
    case TypeIR.TypeSeqHole(index) =>
      q"_root_.inox.parsing.MacroInterpolator.TypeIR.TypeSeqHole($index)"
    case TypeIR.Refinement(id, tpe, pred) =>
      q"_root_.inox.parsing.MacroInterpolator.TypeIR.Refinement($id, $tpe, $pred)"
    case TypeIR.TypeBinding(id, tpe) =>
      q"_root_.inox.parsing.MacroInterpolator.TypeIR.TypeBinding($id, $tpe)"
  }

  val trees = inox.trees

  val parser = new DefinitionParser()

  def holeTypeToType(holeType: HoleType): c.Type = holeType match {
    case IdentifierHoleType => typeOf[inox.Identifier]
    case ExpressionHoleType => typeOf[inox.trees.Expr]
    case TypeHoleType => typeOf[inox.trees.Type]
    case SeqHoleType(holeType) => c.typecheck(tq"_root_.scala.collection.Traversable[${holeTypeToType(holeType)}]", c.TYPEmode).tpe
  }

  def t_apply(args: c.Expr[Any]*): c.Tree = {

    val Select(self, _) = c.prefix.tree

    def getString(expr: c.Tree): String = expr match {
      case Literal(Constant(s : String)) => s
    }

    val parts = self match {
      case Block(ValDef(_, _, _, Apply(_, ls)) :: _, _) => ls.map(getString)
    }

    val sc = StringContext(parts: _*)

    val argsplaceholders = Seq.tabulate(sc.parts.length - 1)(MatchPosition(_))
    val ir = parser.getFromSC(sc, argsplaceholders)(parser.phrase(parser.typeExpression))

    val holeTypes = TypeIR.getHoleTypes(ir)

    for (i <- 0 until args.size) {
      val actual = args(i).actualType
      val expected = holeTypeToType(holeTypes(i))
      if (!(actual weak_<:< expected)) {
        c.error(args(i).tree.pos, s"Invalid argument of type $actual. Expected an argument of type $expected.")
      }
    }

    q"""
      {
        import _root_.inox.parsing.MacroInterpolator._

        val self = $self
        val ir = self.converter.replaceHoles($ir)(new HoleValues(_root_.scala.collection.immutable.Seq(..$args)), new DummyImplicit)
        val tpe = self.converter.getType(ir)(Store.empty)
        self.converter.elaborate(tpe)
      }
    """
  }

  def e_apply(args: c.Expr[Any]*): c.Tree = {

    val Select(self, _) = c.prefix.tree

    def getString(expr: c.Tree): String = expr match {
      case Literal(Constant(s : String)) => s
    }

    val parts = self match {
      case Block(ValDef(_, _, _, Apply(_, ls)) :: _, _) => ls.map(getString)
    }

    val sc = StringContext(parts: _*)

    val argsplaceholders = Seq.tabulate(sc.parts.length - 1)(MatchPosition(_))
    val ir = parser.getFromSC(sc, argsplaceholders)(parser.phrase(parser.expression))

    val holeTypes = ExprIR.getHoleTypes(ir)

    for (i <- 0 until args.size) {
      val actual = args(i).actualType
      val expected = holeTypeToType(holeTypes(i))
      if (!(actual weak_<:< expected)) {
        c.error(args(i).tree.pos, s"Invalid argument of type $actual. Expected an argument of type $expected.")
      }
    }

    q"""
      {
        import _root_.inox.parsing.MacroInterpolator._

        val self = $self
        val ir = self.converter.replaceHoles($ir)(new HoleValues(_root_.scala.collection.immutable.Seq(..$args)))

        val expr = self.converter.getExpr(ir, Unknown.fresh(ir.pos))(Store.empty)
        self.converter.elaborate(expr)
      }
    """
  }
}
