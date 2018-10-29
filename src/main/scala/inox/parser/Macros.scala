package inox
package parser

import scala.util.parsing._
import scala.reflect.macros.whitebox.Context
import scala.language.experimental.macros

import inox.parser.sc._

abstract class Macros(final val c: Context) extends Parsers with IRs {
  import c.universe.{Type => _, Function => _, Expr => _, If => _,  _}

  protected val interpolator: c.Tree
  protected lazy val targetTrees: c.Tree = q"$interpolator.trees"

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

  import Identifiers._
  import Bindings._
  import ADTs._
  import Functions._
  import Types._
  import Exprs._
  import Programs._

  implicit lazy val stringContextLiftable: Liftable[StringContext] = Liftable[StringContext] {
    case sc =>
      q"_root_.scala.StringContext(..${sc.parts})"
  }

  implicit lazy val positionLiftable: Liftable[input.Position] = Liftable[input.Position] {
    case input.NoPosition =>
      q"_root_.scala.util.parsing.input.NoPosition"
    case input.OffsetPosition(source, offset) =>
      q"_root_.scala.util.parsing.input.OffsetPosition(${source.toString}, $offset)"
    case InArgumentPosition(arg, context) =>
      q"_root_.inox.parser.sc.InArgumentPosition($arg, $context)"
    case InPartPosition(part, context, partLine, partColumn) =>
      q"_root_.inox.parser.sc.InPartPosition($part, $context, $partLine, $partColumn)"
  }

  implicit lazy val bigIntLiftable: Liftable[BigInt] = Liftable[BigInt] {
    case n => q"_root_.scala.math.BigInt(${n.toString})"
  }

  implicit def repHoleLiftable[A <: IR : TypeTag] = Liftable[RepHole[A]] {
    case ir@RepHole(index) => {
      val tpe = typeOf[A] match {
        case TypeRef(SingleType(_, o), t, _) => c.typecheck(tq"$interpolator.$o.$t", c.TYPEmode).tpe
      }

      q"$interpolator.RepHole[$tpe]($index).setPos(${ir.pos})"
    }
  }

  implicit def hseqLiftable[A <: IR : TypeTag](implicit ev: Liftable[A]) = Liftable[HSeq[A]] {
    case ir@HSeq(es) => {
      val tpe = typeOf[A] match {
        case TypeRef(SingleType(_, o), t, _) => c.typecheck(tq"$interpolator.$o.$t", c.TYPEmode).tpe
      }
      val elems: Seq[Either[RepHole[A], A]] = es

      q"$interpolator.HSeq[$tpe](_root_.scala.collection.Seq(..$elems)).setPos(${ir.pos})"
    }
  }

  implicit lazy val identifiersLiftable: Liftable[Identifier] = Liftable[Identifier] {
    case ir@IdentifierName(name) =>
      q"$interpolator.Identifiers.IdentifierName($name).setPos(${ir.pos})"
    case ir@IdentifierHole(index) =>
      q"$interpolator.Identifiers.IdentifierHole($index).setPos(${ir.pos})"
  }

  implicit lazy val bindingsLiftable: Liftable[Binding] = Liftable[Binding] {
    case ir@InferredValDef(id) =>
      q"$interpolator.Bindings.InferredValDef($id).setPos(${ir.pos})"
    case ir@ExplicitValDef(id, tpe) =>
      q"$interpolator.Bindings.ExplicitValDef($id, $tpe).setPos(${ir.pos})"
    case ir@BindingHole(index) =>
      q"$interpolator.Bindings.BindingHole($index).setPos(${ir.pos})"
  }

  implicit lazy val sortsLiftable: Liftable[Sort] = Liftable[Sort] {
    case ir@Sort(id, tps, cs) =>
      q"$interpolator.ADTs.Sort($id, $tps, $cs).setPos(${ir.pos})"
  }

  implicit lazy val constructorsLiftable: Liftable[Constructor] = Liftable[Constructor] {
    case ir@Constructor(id, ps) =>
      q"$interpolator.ADTs.Constructor($id, $ps).setPos(${ir.pos})"
  }

  implicit lazy val functionsLiftable: Liftable[Function] = Liftable[Function] {
    case ir@Function(id, tps, ps, rt, b) =>
      q"$interpolator.Functions.Function($id, $tps, $ps, $rt, $b).setPos(${ir.pos})"
  }

  implicit lazy val typesLiftable: Liftable[Type] = Liftable[Type] {
    case ir@TypeHole(index) =>
      q"$interpolator.Types.TypeHole($index).setPos(${ir.pos})"
    case ir@Types.Primitive(prim) =>
      q"$interpolator.Types.Primitive($prim).setPos(${ir.pos})"
    case ir@Operation(op, elems) =>
      q"$interpolator.Types.Operation($op, $elems).setPos(${ir.pos})"
    case ir@FunctionType(froms, to) =>
      q"$interpolator.Types.FunctionType($froms, $to).setPos(${ir.pos})"
    case ir@TupleType(elems) =>
      q"$interpolator.Types.TupleType($elems).setPos(${ir.pos})"
    case ir@Types.Invocation(id, args) =>
      q"$interpolator.Types.Invocation($id, $args).setPos(${ir.pos})"
    case ir@Types.Variable(id) =>
      q"$interpolator.Types.Variable($id).setPos(${ir.pos})"
    case ir@RefinementType(b, p) =>
      q"$interpolator.Types.RefinementType($b, $p).setPos(${ir.pos})"
    case ir@PiType(bs, to) =>
      q"$interpolator.Types.PiType($bs, $to).setPos(${ir.pos})"
    case ir@SigmaType(bs, to) =>
      q"$interpolator.Types.SigmaType($bs, $to).setPos(${ir.pos})"
  }

  implicit lazy val typePrimitivesLiftable: Liftable[Types.Primitives.Type] = Liftable[Types.Primitives.Type] {
    case Primitives.BVType(size) =>
      q"$interpolator.Types.Primitives.BVType($size)"
    case Primitives.IntegerType =>
      q"$interpolator.Types.Primitives.IntegerType"
    case Primitives.StringType =>
      q"$interpolator.Types.Primitives.StringType"
    case Primitives.CharType =>
      q"$interpolator.Types.Primitives.CharType"
    case Primitives.BooleanType =>
      q"$interpolator.Types.Primitives.BooleanType"
    case Primitives.UnitType =>
      q"$interpolator.Types.Primitives.UnitType"
    case Primitives.RealType =>
      q"$interpolator.Types.Primitives.RealType"
  }

  implicit lazy val typeOperatorsLiftable: Liftable[Types.Operators.Operator] = Liftable[Types.Operators.Operator] {
    case Operators.Set =>
      q"$interpolator.Types.Operators.Set"
    case Operators.Map =>
      q"$interpolator.Types.Operators.Map"
    case Operators.Bag =>
      q"$interpolator.Types.Operators.Bag"
  }

  implicit lazy val exprsLiftable: Liftable[Expr] = Liftable[Expr] {
    case ir@ExprHole(index) =>
      q"$interpolator.Exprs.ExprHole($index).setPos(${ir.pos})"
    case ir@UnitLiteral() =>
      q"$interpolator.Exprs.UnitLiteral().setPos(${ir.pos})"
    case ir@BooleanLiteral(value) =>
      q"$interpolator.Exprs.BooleanLiteral($value).setPos(${ir.pos})"
    case ir@IntegerLiteral(value) =>
      q"$interpolator.Exprs.IntegerLiteral($value).setPos(${ir.pos})"
    case ir@FractionLiteral(num, denom) =>
      q"$interpolator.Exprs.FractionLiteral($num, $denom).setPos(${ir.pos})"
    case ir@StringLiteral(value) =>
      q"$interpolator.Exprs.StringLiteral($value).setPos(${ir.pos})"
    case ir@CharLiteral(value) =>
      q"$interpolator.Exprs.CharLiteral($value).setPos(${ir.pos})"
    case ir@SetConstruction(t, es) =>
      q"$interpolator.Exprs.SetConstruction($t, $es).setPos(${ir.pos})"
    case ir@BagConstruction(t, ps) =>
      q"$interpolator.Exprs.BagConstruction($t, $ps).setPos(${ir.pos})"
    case ir@MapConstruction(ts, ps, d) =>
      q"$interpolator.Exprs.MapConstruction($ts, $ps, $d).setPos(${ir.pos})"
    case ir@Exprs.Variable(id) =>
      q"$interpolator.Exprs.Variable($id).setPos(${ir.pos})"
    case ir@UnaryOperation(op, expr) =>
      q"$interpolator.Exprs.UnaryOperation($op, $expr).setPos(${ir.pos})"
    case ir@BinaryOperation(op, lhs, rhs) =>
      q"$interpolator.Exprs.BinaryOperation($op, $lhs, $rhs).setPos(${ir.pos})"
    case ir@NaryOperation(op, args) =>
      q"$interpolator.Exprs.NaryOperation($op, $args).setPos(${ir.pos})"
    case ir@Exprs.Invocation(id, tps, args) =>
      q"$interpolator.Exprs.Invocation($id, $tps, $args).setPos(${ir.pos})"
    case ir@PrimitiveInvocation(id, tps, args) =>
      q"$interpolator.Exprs.PrimitiveInvocation($id, $tps, $args).setPos(${ir.pos})"
    case ir@Application(callee, args) =>
      q"$interpolator.Exprs.Application($callee, $args).setPos(${ir.pos})"
    case ir@Abstraction(q, bs, b) =>
      q"$interpolator.Exprs.Abstraction($q, $bs, $b).setPos(${ir.pos})"
    case ir@Let(b, v, e) =>
      q"$interpolator.Exprs.Let($b, $v, $e).setPos(${ir.pos})"
    case ir@If(c, t, e) =>
      q"$interpolator.Exprs.If($c, $t, $e).setPos(${ir.pos})"
    case ir@Selection(s, f) =>
      q"$interpolator.Exprs.Selection($s, $f).setPos(${ir.pos})"
    case ir@Tuple(es) =>
      q"$interpolator.Exprs.Tuple($es).setPos(${ir.pos})"
    case ir@TupleSelection(t, index) =>
      q"$interpolator.Exprs.TupleSelection($t, $index).setPos(${ir.pos})"
    case ir@TypeAnnotation(e, t) =>
      q"$interpolator.Exprs.TypeAnnotation($e, $t).setPos(${ir.pos})"
    case ir@Choose(b, p) =>
      q"$interpolator.Exprs.Choose($b, $p).setPos(${ir.pos})"
    case ir@Assume(p, b) =>
      q"$interpolator.Exprs.Assume($p, $b).setPos(${ir.pos})"
    case ir@IsConstructor(e, c) =>
      q"$interpolator.Exprs.IsConstructor($e, $c).setPos(${ir.pos})"
    case ir@Cast(m, e, t) =>
      q"$interpolator.Exprs.Cast($m, $e, $t).setPos(${ir.pos})"
  }

  implicit lazy val exprPairsLiftable: Liftable[ExprPair] = Liftable[ExprPair] {
    case ir@Pair(lhs, rhs) =>
      q"$interpolator.Exprs.Pair($lhs, $rhs).setPos(${ir.pos})"
    case ir@PairHole(index) =>
      q"$interpolator.Exprs.PairHole($index).setPos(${ir.pos})"
  }

  implicit lazy val exprCastsLiftable: Liftable[Casts.Mode] = Liftable[Casts.Mode] {
    case Casts.Widen =>
      q"$interpolator.Exprs.Casts.Widen"
    case Casts.Narrow =>
      q"$interpolator.Exprs.Casts.Narrow"
  }

  implicit lazy val exprUnaryLiftable: Liftable[Unary.Operator] = Liftable[Unary.Operator] {
    case Unary.Minus =>
      q"$interpolator.Exprs.Unary.Minus"
    case Unary.Not =>
      q"$interpolator.Exprs.Unary.Not"
    case Unary.BVNot =>
      q"$interpolator.Exprs.Unary.BVNot"
  }

  implicit lazy val exprBinaryLiftable: Liftable[Binary.Operator] = Liftable[Binary.Operator] {
    case Binary.Plus =>
      q"$interpolator.Exprs.Binary.Plus"
    case Binary.Minus =>
      q"$interpolator.Exprs.Binary.Minus"
    case Binary.Times =>
      q"$interpolator.Exprs.Binary.Times"
    case Binary.Division =>
      q"$interpolator.Exprs.Binary.Division"
    case Binary.Modulo =>
      q"$interpolator.Exprs.Binary.Modulo"
    case Binary.Remainder =>
      q"$interpolator.Exprs.Binary.Remainder"
    case Binary.Implies =>
      q"$interpolator.Exprs.Binary.Implies"
    case Binary.Equals =>
      q"$interpolator.Exprs.Binary.Equals"
    case Binary.LessEquals =>
      q"$interpolator.Exprs.Binary.LessEquals"
    case Binary.LessThan =>
      q"$interpolator.Exprs.Binary.LessThan"
    case Binary.GreaterEquals =>
      q"$interpolator.Exprs.Binary.GreaterEquals"
    case Binary.GreaterThan =>
      q"$interpolator.Exprs.Binary.GreaterThan"
    case Binary.BVAnd =>
      q"$interpolator.Exprs.Binary.BVAnd"
    case Binary.BVOr =>
      q"$interpolator.Exprs.Binary.BVOr"
    case Binary.BVXor =>
      q"$interpolator.Exprs.Binary.BVXor"
    case Binary.BVShiftLeft =>
      q"$interpolator.Exprs.Binary.BVShiftLeft"
    case Binary.BVAShiftRight =>
      q"$interpolator.Exprs.Binary.BVAShiftRight"
    case Binary.BVLShiftRight =>
      q"$interpolator.Exprs.Binary.BVLShiftRight"
  }

  implicit lazy val exprNAryLiftable: Liftable[NAry.Operator] = Liftable[NAry.Operator] {
    case NAry.And =>
      q"$interpolator.Exprs.NAry.And"
    case NAry.Or =>
      q"$interpolator.Exprs.NAry.Or"
  }

  implicit lazy val exprPrimitivesLiftable: Liftable[Exprs.Primitive.Function] = Liftable[Exprs.Primitive.Function] {
    case Exprs.Primitive.SetAdd =>
      q"$interpolator.Exprs.Primitive.SetAdd"
    case Exprs.Primitive.ElementOfSet =>
      q"$interpolator.Exprs.Primitive.ElementOfSet"
    case Exprs.Primitive.SetIntersection =>
      q"$interpolator.Exprs.Primitive.SetIntersection"
    case Exprs.Primitive.SetUnion =>
      q"$interpolator.Exprs.Primitive.SetUnion"
    case Exprs.Primitive.SetDifference =>
      q"$interpolator.Exprs.Primitive.SetDifference"
    case Exprs.Primitive.Subset =>
      q"$interpolator.Exprs.Primitive.Subset"
    case Exprs.Primitive.BagAdd =>
      q"$interpolator.Exprs.Primitive.BagAdd"
    case Exprs.Primitive.MultiplicityInBag =>
      q"$interpolator.Exprs.Primitive.MultiplicityInBag"
    case Exprs.Primitive.BagIntersection =>
      q"$interpolator.Exprs.Primitive.BagIntersection"
    case Exprs.Primitive.BagUnion =>
      q"$interpolator.Exprs.Primitive.BagUnion"
    case Exprs.Primitive.BagDifference =>
      q"$interpolator.Exprs.Primitive.BagDifference"
    case Exprs.Primitive.MapApply =>
      q"$interpolator.Exprs.Primitive.MapApply"
    case Exprs.Primitive.MapUpdated =>
      q"$interpolator.Exprs.Primitive.MapUpdated"
    case Exprs.Primitive.StringConcat =>
      q"$interpolator.Exprs.Primitive.StringConcat"
    case Exprs.Primitive.SubString =>
      q"$interpolator.Exprs.Primitive.SubString"
    case Exprs.Primitive.StringLength =>
      q"$interpolator.Exprs.Primitive.StringLength"
  }

  implicit lazy val quantifiersLiftable: Liftable[Quantifier] = Liftable[Quantifier] {
    case Forall =>
      q"$interpolator.Exprs.Forall"
    case Lambda =>
      q"$interpolator.Exprs.Lambda"
  }

  implicit lazy val programLiftable: Liftable[Program] = Liftable[Program] {
    case ir@Program(es) =>
      q"$interpolator.Programs.Program(_root_.scala.collection.Seq(..$es)).setPos(${ir.pos})"
  }

  private def parse[A](p: Parser[A]): A = {
    parseSC(sc)(phrase(p)) match {
      case Right(v) => v
      case Left(e) => c.abort(c.enclosingPosition, "Parsing error in quasiquoted inox expression:\n" + e)
    }
  }

  private lazy val identType = typeOf[inox.Identifier]
  private lazy val exprType = c.typecheck(tq"$targetTrees.Expr", c.TYPEmode).tpe
  private lazy val typeType = c.typecheck(tq"$targetTrees.Type", c.TYPEmode).tpe
  private lazy val valDefType = c.typecheck(tq"$targetTrees.ValDef", c.TYPEmode).tpe
  private lazy val funDefType = c.typecheck(tq"$targetTrees.FunDef", c.TYPEmode).tpe
  private lazy val adtSortType = c.typecheck(tq"$targetTrees.ADTSort", c.TYPEmode).tpe
  private lazy val constructorType = c.typecheck(tq"$targetTrees.ADTConstructor", c.TYPEmode).tpe
  private lazy val defSeqType = c.typecheck(tq"_root_.scala.collection.Seq[$targetTrees.Definition]", c.TYPEmode).tpe

  private def tupleType(types: Seq[c.Type]): c.Tree = tq"(..$types)"

  private def accessAll(types: Seq[c.Type]): c.Tree = {
    val elems = types.zipWithIndex.map {
      case (tpe, i) => q"x($i).asInstanceOf[$tpe]"
    }
    q"(x: Map[Int, Any]) => (..$elems)"
  }

  private def getTypes(holes: Seq[Hole]): Seq[c.Type] = {

    def holeTypeToType(holeType: HoleType): c.Type = holeType match {
      case HoleTypes.Identifier => identType
      case HoleTypes.Expr => exprType
      case HoleTypes.Type => typeType
      case HoleTypes.ValDef => valDefType
      case HoleTypes.Constructor => constructorType
      case HoleTypes.Pair(lhs, rhs) => c.typecheck(tq"(${holeTypeToType(lhs)}, ${holeTypeToType(rhs)})", c.TYPEmode).tpe
      case HoleTypes.Sequence(holeType) => c.typecheck(tq"_root_.scala.collection.Seq[${holeTypeToType(holeType)}]", c.TYPEmode).tpe
    }

    val holeTypes = holes.map(h => h.index -> h.holeType).toMap
    Seq.tabulate(holeTypes.size) { (i: Int) => holeTypeToType(holeTypes(i)) }
  }

  private def verifyArgTypes(args: Seq[c.Expr[Any]], types: Seq[c.Type]) {
    assert(args.size == types.size)

    for ((arg, expectedType) <- args.zip(types)) {
      val actualType = arg.actualType
      if (!(actualType <:< expectedType)) {
        c.error(arg.tree.pos, s"Invalid argument of type $actualType. Expected an argument of type $expectedType.")
      }
    }
  }

  def t_apply(args: c.Expr[Any]*): c.Tree = {

    val ir = parse(typeParser)
    val types = getTypes(ir.getHoles)

    verifyArgTypes(args, types)

    q"""
      {
        val ir = $ir
        val self = $self
        val res: $typeType = $interpolator.TypeE.elaborate(ir)($interpolator.createStore(self.symbols, _root_.scala.collection.Seq(..$args))).get match {
          case _root_.scala.util.Left(err) => throw _root_.inox.parser.InterpolatorException(err)
          case _root_.scala.util.Right(((_, ev), cs)) => $interpolator.solve(cs) match {
            case _root_.scala.util.Left(err) => throw _root_.inox.parser.InterpolatorException(err)
            case _root_.scala.util.Right(u) => ev.get(u)
          }
        }
        res
      }
    """
  }

  def t_unapply(arg: c.Tree): c.Tree = {

    val ir = parse(typeParser)
    val holes = ir.getHoles

    if (holes.size >= 1) {
      val types = getTypes(holes)

      q"""
        new {
          val ir = $ir
          val self = $self

          def unapply(t: $typeType): _root_.scala.Option[${tupleType(types)}] = {
            $interpolator.TypeX.extract(ir, t).getMatches(self.symbols).map(${accessAll(types)})
          }
        }.unapply($arg)
      """
    } else {
      q"""
        new {
          val ir = $ir
          val self = $self

          def unapplySeq(t: $typeType): _root_.scala.Option[_root_.scala.collection.Seq[_root_.scala.Nothing]] = {
            $interpolator.TypeX.extract(ir, t).getMatches(self.symbols).map(_ => _root_.scala.collection.Seq[_root_.scala.Nothing]())
          }
        }.unapplySeq($arg)
      """
    }
  }

  def e_apply(args: c.Expr[Any]*): c.Tree = {

    val ir = parse(exprParser)
    val types = getTypes(ir.getHoles)

    verifyArgTypes(args, types)

    q"""
      {
        val ir = $ir
        val self = $self
        val res: $exprType = $interpolator.ExprE.elaborate(ir)($interpolator.createStore(self.symbols, _root_.scala.collection.Seq(..$args))).get match {
          case _root_.scala.util.Left(err) => throw _root_.inox.parser.InterpolatorException(err)
          case _root_.scala.util.Right(((_, ev), cs)) => $interpolator.solve(cs) match {
            case _root_.scala.util.Left(err) => throw _root_.inox.parser.InterpolatorException(err)
            case _root_.scala.util.Right(u) => ev.get(u)
          }
        }
        res
      }
    """
  }

  def e_unapply(arg: c.Tree): c.Tree = {

    val ir = parse(exprParser)
    val holes = ir.getHoles

    if (holes.size >= 1) {
      val types = getTypes(holes)

      q"""
        new {
          val ir = $ir
          val self = $self

          def unapply(t: $exprType): _root_.scala.Option[${tupleType(types)}] = {
            $interpolator.ExprX.extract(ir, t).getMatches(self.symbols).map(${accessAll(types)})
          }
        }.unapply($arg)
      """
    } else {
      q"""
        new {
          val ir = $ir
          val self = $self

          def unapplySeq(t: $exprType): _root_.scala.Option[_root_.scala.collection.Seq[_root_.scala.Nothing]] = {
            $interpolator.ExprX.extract(ir, t).getMatches(self.symbols).map(_ => _root_.scala.collection.Seq[_root_.scala.Nothing]())
          }
        }.unapplySeq($arg)
      """
    }
  }

  def vd_apply(args: c.Expr[Any]*): c.Tree = {

    val ir = parse(bindingParser(explicitOnly=true))
    val types = getTypes(ir.getHoles)

    verifyArgTypes(args, types)

    q"""
      {
        val ir = $ir
        val self = $self
        val res: $valDefType = $interpolator.BindingE.elaborate(ir)($interpolator.createStore(self.symbols, _root_.scala.collection.Seq(..$args))).get match {
          case _root_.scala.util.Left(err) => throw _root_.inox.parser.InterpolatorException(err)
          case _root_.scala.util.Right((ev, cs)) => $interpolator.solve(cs) match {
            case _root_.scala.util.Left(err) => throw _root_.inox.parser.InterpolatorException(err)
            case _root_.scala.util.Right(u) => ev.evValDef.get(u)
          }
        }
        res
      }
    """
  }

  def vd_unapply(arg: c.Tree): c.Tree = {

    val ir = parse(bindingParser(explicitOnly=true))
    val holes = ir.getHoles

    if (holes.size >= 1) {
      val types = getTypes(holes)

      q"""
        new {
          val ir = $ir
          val self = $self

          def unapply(t: $valDefType): _root_.scala.Option[${tupleType(types)}] = {
            $interpolator.BindingX.extract(ir, t).getMatches(self.symbols).map(${accessAll(types)})
          }
        }.unapply($arg)
      """
    } else {
      q"""
        new {
          val ir = $ir
          val self = $self

          def unapplySeq(t: $valDefType): _root_.scala.Option[_root_.scala.collection.Seq[_root_.scala.Nothing]] = {
            $interpolator.BindingX.extract(ir, t).getMatches(self.symbols).map(_ => _root_.scala.collection.Seq[_root_.scala.Nothing]())
          }
        }.unapplySeq($arg)
      """
    }
  }

  def fd_apply(args: c.Expr[Any]*): c.Tree = {

    val ir = parse(functionDefinitionParser)
    val types = getTypes(ir.getHoles)

    verifyArgTypes(args, types)

    q"""
      {
        val ir = $ir
        val self = $self
        val res: $funDefType = $interpolator.SingleFunctionE.elaborate(ir)($interpolator.createStore(self.symbols, _root_.scala.collection.Seq(..$args))).get match {
          case _root_.scala.util.Left(err) => throw _root_.inox.parser.InterpolatorException(err)
          case _root_.scala.util.Right((ev, cs)) => $interpolator.solve(cs) match {
            case _root_.scala.util.Left(err) => throw _root_.inox.parser.InterpolatorException(err)
            case _root_.scala.util.Right(u) => ev.get(u)
          }
        }
        res
      }
    """
  }

  def fd_unapply(arg: c.Tree): c.Tree = {

    val ir = parse(functionDefinitionParser)
    val holes = ir.getHoles

    if (holes.size >= 1) {
      val types = getTypes(holes)

      q"""
        new {
          val ir = $ir
          val self = $self

          def unapply(t: $funDefType): _root_.scala.Option[${tupleType(types)}] = {
            $interpolator.FunctionX.extract(ir, t).getMatches(self.symbols).map(${accessAll(types)})
          }
        }.unapply($arg)
      """
    } else {
      q"""
        new {
          val ir = $ir
          val self = $self

          def unapplySeq(t: $funDefType): _root_.scala.Option[_root_.scala.collection.Seq[_root_.scala.Nothing]] = {
            $interpolator.FunctionX.extract(ir, t).getMatches(self.symbols).map(_ => _root_.scala.collection.Seq[_root_.scala.Nothing]())
          }
        }.unapplySeq($arg)
      """
    }
  }

  def td_apply(args: c.Expr[Any]*): c.Tree = {

    val ir = parse(adtDefinitionParser)
    val types = getTypes(ir.getHoles)

    verifyArgTypes(args, types)

    q"""
      {
        val ir = $ir
        val self = $self
        val res: $adtSortType = $interpolator.SortE.elaborate(ir)($interpolator.createStore(self.symbols, _root_.scala.collection.Seq(..$args))).get match {
          case _root_.scala.util.Left(err) => throw _root_.inox.parser.InterpolatorException(err)
          case _root_.scala.util.Right(((_, ev), cs)) => $interpolator.solve(cs) match {
            case _root_.scala.util.Left(err) => throw _root_.inox.parser.InterpolatorException(err)
            case _root_.scala.util.Right(u) => ev.get(u)
          }
        }
        res
      }
    """
  }

  def td_unapply(arg: c.Tree): c.Tree = {

    val ir = parse(adtDefinitionParser)
    val holes = ir.getHoles

    if (holes.size >= 1) {
      val types = getTypes(holes)

      q"""
        new {
          val ir = $ir
          val self = $self

          def unapply(t: $adtSortType): _root_.scala.Option[${tupleType(types)}] = {
            $interpolator.SortX.extract(ir, t).getMatches(self.symbols).map(${accessAll(types)})
          }
        }.unapply($arg)
      """
    } else {
      q"""
        new {
          val ir = $ir
          val self = $self

          def unapplySeq(t: $adtSortType): _root_.scala.Option[_root_.scala.collection.Seq[_root_.scala.Nothing]] = {
            $interpolator.SortX.extract(ir, t).getMatches(self.symbols).map(_ => _root_.scala.collection.Seq[_root_.scala.Nothing]())
          }
        }.unapplySeq($arg)
      """
    }
  }

  def p_apply(args: c.Expr[Any]*): c.Tree = {

    val ir = parse(programParser)
    val types = getTypes(ir.getHoles)

    verifyArgTypes(args, types)

    q"""
      {
        val ir = $ir
        val self = $self
        val res: $defSeqType = $interpolator.ProgramE.elaborate(ir)($interpolator.createStore(self.symbols, _root_.scala.collection.Seq(..$args))).get match {
          case _root_.scala.util.Left(err) => throw _root_.inox.parser.InterpolatorException(err)
          case _root_.scala.util.Right((evs, cs)) => $interpolator.solve(cs) match {
            case _root_.scala.util.Left(err) => throw _root_.inox.parser.InterpolatorException(err)
            case _root_.scala.util.Right(u) => evs.map(_.get(u))
          }
        }
        res
      }
    """
  }
}