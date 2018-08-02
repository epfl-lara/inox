package inox
package parsing

import scala.reflect.macros.whitebox.Context
import scala.language.experimental.macros


abstract class Macros(final val c: Context) extends Parsers with IRs {

  import c.universe._

  protected val interpolator: c.Tree

  protected lazy val targetTrees: c.Tree = q"$interpolator.trees"

  implicit lazy val quantifierLiftable = Liftable[ExprIR.Quantifier] {
    case ExprIR.Lambda => q"$interpolator.ExprIR.Lambda"
    case ExprIR.Forall => q"$interpolator.ExprIR.Forall"
    case ExprIR.Exists => q"$interpolator.ExprIR.Exists"
    case ExprIR.Choose => q"$interpolator.ExprIR.Choose"
  }

  implicit lazy val fieldLiftable = Liftable[ExprIR.Field] {
    case ExprIR.FieldName(name) => q"$interpolator.ExprIR.FieldName($name)"
    case ExprIR.FieldHole(index) => q"$interpolator.ExprIR.FieldHole($index)"
    case _ => c.abort(c.enclosingPosition, "Unexpected construct.")
  }

  implicit lazy val identifierLiftable = Liftable[ExprIR.Identifier] {
    case ExprIR.IdentifierName(name) => q"$interpolator.ExprIR.IdentifierName($name)"
    case ExprIR.IdentifierHole(index) => q"$interpolator.ExprIR.IdentifierHole($index)"
    case _ => c.abort(c.enclosingPosition, "Unexpected construct.")
  }

  implicit lazy val valueLiftable = Liftable[ExprIR.Value] {
    case ExprIR.NumericLiteral(value) =>
      q"$interpolator.ExprIR.NumericLiteral($value)"
    case ExprIR.DecimalLiteral(whole, trailing, repeating) =>
      q"$interpolator.ExprIR.DecimalLiteral($whole, $trailing, $repeating)"
    case ExprIR.StringLiteral(value) =>
      q"$interpolator.ExprIR.StringLiteral($value)"
    case ExprIR.BooleanLiteral(value) =>
      q"$interpolator.ExprIR.BooleanLiteral($value)"
    case ExprIR.CharLiteral(value) =>
      q"$interpolator.ExprIR.CharLiteral($value)"
    case ExprIR.UnitLiteral =>
      q"$interpolator.ExprIR.UnitLiteral"
    case _ => c.abort(c.enclosingPosition, "Unexpected construct.")
  }

  implicit lazy val exprIRLiftable: Liftable[ExprIR.Expression] = Liftable[ExprIR.Expression] {
    case ExprIR.Variable(id) =>
      q"$interpolator.ExprIR.Variable($id)"
    case ExprIR.Application(callee, args) =>
      q"$interpolator.ExprIR.Application($callee, _root_.scala.collection.immutable.Seq(..$args))"
    case ExprIR.Abstraction(quantifier, bindings, body) =>
      q"$interpolator.ExprIR.Abstraction($quantifier, _root_.scala.collection.immutable.Seq(..$bindings), $body)"
    case ExprIR.Operation(operator, args) =>
      q"$interpolator.ExprIR.Operation($operator, _root_.scala.collection.immutable.Seq(..$args))"
    case ExprIR.Selection(structure, field) =>
      q"$interpolator.ExprIR.Selection($structure, $field)"
    case ExprIR.TypeApplication(callee, args) =>
      q"$interpolator.ExprIR.TypeApplication($callee, _root_.scala.collection.immutable.Seq(..$args))"
    case ExprIR.Let(bindings, body) =>
      q"$interpolator.ExprIR.Let(_root_.scala.collection.immutable.Seq(..$bindings), $body)"
    case ExprIR.Literal(value) =>
      q"$interpolator.ExprIR.Literal($value)"
    case ExprIR.ExpressionHole(index) =>
      q"$interpolator.ExprIR.ExpressionHole($index)"
    case ExprIR.ExpressionSeqHole(index) =>
      q"$interpolator.ExprIR.ExpressionSeqHole($index)"
  }

  implicit lazy val typeOperatorLiftable = Liftable[TypeIR.Operator] {
    case TypeIR.Group => q"$interpolator.TypeIR.Group"
    case TypeIR.Tuple => q"$interpolator.TypeIR.Tuple"
    case TypeIR.Sigma => q"$interpolator.TypeIR.Sigma"
    case TypeIR.Arrow => q"$interpolator.TypeIR.Arrow"
    case TypeIR.Pi => q"$interpolator.TypeIR.Pi"
  }

  implicit lazy val typeIRLiftable: Liftable[TypeIR.Expression] = Liftable[TypeIR.Expression] {
    case TypeIR.Literal(TypeIR.Name(name)) =>
      q"$interpolator.TypeIR.Literal($interpolator.TypeIR.Name($name))"
    case TypeIR.Application(callee, args) =>
      q"$interpolator.TypeIR.Application($callee, _root_.scala.collection.immutable.Seq(..$args))"
    case TypeIR.Operation(operator, args) =>
      q"$interpolator.TypeIR.Operation($operator, _root_.scala.collection.immutable.Seq(..$args))"
    case TypeIR.TypeHole(index) =>
      q"$interpolator.TypeIR.TypeHole($index)"
    case TypeIR.NameHole(index) =>
      q"$interpolator.TypeIR.NameHole($index)"
    case TypeIR.TypeSeqHole(index) =>
      q"$interpolator.TypeIR.TypeSeqHole($index)"
    case TypeIR.Refinement(id, tpe, pred) =>
      q"$interpolator.TypeIR.Refinement($id, $tpe, $pred)"
    case TypeIR.TypeBinding(id, tpe) =>
      q"$interpolator.TypeIR.TypeBinding($id, $tpe)"
  }

  private val parser = new DefinitionParser()

  private val self = {
    val Select(self, _) = c.prefix.tree
    self
  }

  private val sc = StringContext({

    def getString(expr: c.Tree): String = expr match {
      case Literal(Constant(s : String)) => s
    }

    val ls = self match {
      case Block(ValDef(_, _, _, Apply(_, ls)) :: _, _) => {
        // TODO: Should we issue a warning ?
        // c.warning(c.enclosingPosition, "No implicit Symbols in scope. Using NoSymbols by default.")
        ls  // In case of default symbols.
      }
      case Apply(Apply(_, Apply(_, ls) :: _), _) => ls  // In case of implicit symbols.
      case _ => c.abort(c.enclosingPosition, "Unexpected macro use.")
    }

    ls.map(getString)
  }: _*)

  private val holes = Seq.tabulate(sc.parts.size - 1)(MatchPosition(_))

  private def parse[A](p: parser.Parser[A]): A = {
    parser.fromSC(sc, holes)(parser.phrase(p)) match {
      case Right(v) => v
      case Left(e) => c.abort(c.enclosingPosition, e)
    }
  }

  private def getTypes(holeTypes: Map[Int, HoleType]): Seq[c.Type] =
    Seq.tabulate(holeTypes.size) { (i: Int) => holeTypeToType(holeTypes(i)) }

  private lazy val identType = typeOf[inox.Identifier]
  private lazy val exprType = c.typecheck(tq"$targetTrees.Expr", c.TYPEmode).tpe
  private lazy val typeType = c.typecheck(tq"$targetTrees.Type", c.TYPEmode).tpe

  private def holeTypeToType(holeType: HoleType): c.Type = holeType match {
    case IdentifierHoleType => identType
    case ExpressionHoleType => exprType
    case TypeHoleType => typeType
    case SeqHoleType(holeType) => c.typecheck(tq"_root_.scala.collection.Seq[${holeTypeToType(holeType)}]", c.TYPEmode).tpe
  }

  private def tupleType(types: Seq[c.Type]): c.Tree = tq"(..$types)"

  private def accessAll(types: Seq[c.Type]): c.Tree = {
    val elems = types.zipWithIndex.map {
      case (tpe, i) => q"x($i).asInstanceOf[$tpe]"
    }
    q"(x: Map[Int, Any]) => (..$elems)"
  }

  private def verifyArgTypes(args: Seq[c.Expr[Any]], types: Seq[c.Type]) {
    assert(args.size == types.size)

    for ((arg, expectedType) <- args.zip(types)) {
      val actualType = arg.actualType
      if (!(actualType weak_<:< expectedType)) {
        c.error(arg.tree.pos, s"Invalid argument of type $actualType. Expected an argument of type $expectedType.")
      }
    }
  }

  def t_apply(args: c.Expr[Any]*): c.Tree = {

    val ir = parse(parser.typeExpression)
    val types = getTypes(TypeIR.getHoleTypes(ir))

    verifyArgTypes(args, types)

    q"""
      {
        import $interpolator._

        val self = $self
        val ir = self.converter.replaceHoles($ir)(new HoleValues(_root_.scala.collection.immutable.Seq(..$args)), new DummyImplicit)
        val tpe = self.converter.getType(ir)(Store.empty)
        self.converter.elaborate(tpe)
      }
    """
  }

  def t_unapply(arg: c.Tree): c.Tree = {

    val ir = parse(parser.typeExpression)

    if (holes.size >= 1) {
      val types = getTypes(TypeIR.getHoleTypes(ir))

      q"""
        new {
          val ir: $interpolator.TypeIR.Expression = $ir

          def unapply(t: $typeType): _root_.scala.Option[${tupleType(types)}] = {
            $self.converter.extract(t, ir).map(${accessAll(types)})
          }
        }.unapply($arg)
      """
    } else {
      q"""
        new {
          val ir: $interpolator.TypeIR.Expression = $ir

          def unapplySeq(t: $typeType): _root_.scala.Option[_root_.scala.collection.Seq[_root_.scala.Nothing]] = {
            $self.converter.extract(t, ir).map(_ => _root_.scala.collection.Seq[_root_.scala.Nothing]())
          }
        }.unapplySeq($arg)
      """
    }
  }

  def e_apply(args: c.Expr[Any]*): c.Tree = {

    val ir = parse(parser.expression)
    val types = getTypes(ExprIR.getHoleTypes(ir))

    verifyArgTypes(args, types)

    q"""
      {
        import $interpolator._

        val self = $self
        val ir = self.converter.replaceHoles($ir)(new HoleValues(_root_.scala.collection.immutable.Seq(..$args)))

        val expr = self.converter.getExpr(ir, Unknown.fresh(ir.pos))(Store.empty)
        self.converter.elaborate(expr)
      }
    """
  }

  def e_unapply(arg: c.Tree): c.Tree = {

    val ir = parse(parser.expression)

    if (holes.size >= 1) {
      val types = getTypes(ExprIR.getHoleTypes(ir))

      q"""
        new {
          val ir: $interpolator.ExprIR.Expression = $ir

          def unapply(t: $exprType): _root_.scala.Option[${tupleType(types)}] = {
            $self.converter.extract(t, ir).map(${accessAll(types)})
          }
        }.unapply($arg)
      """
    } else {
      q"""
        new {
          val ir: $interpolator.ExprIR.Expression = $ir

          def unapplySeq(t: $exprType): _root_.scala.Option[_root_.scala.collection.Seq[_root_.scala.Nothing]] = {
            $self.converter.extract(t, ir).map(_ => _root_.scala.collection.Seq[_root_.scala.Nothing]())
          }
        }.unapplySeq($arg)
      """
    }
  }
}
