package inox
package parser
package extraction
package extractors

trait ExprExtractors { self: Extractors =>

  import Exprs._

  object ExprX extends Extractor[Expr, trees.Expr, Unit] {
    override def extract(template: Expr, scrutinee: trees.Expr): Matching[Unit] = template match {
      case ExprHole(index) => Matching(index -> scrutinee)
      case UnitLiteral() => Matching.collect(scrutinee) {
        case trees.UnitLiteral() => Matching.success
      }
      case Variable(id) => Matching.collect(scrutinee) {
        case trees.Variable(sId, _, _) => ExprUseIdX.extract(id, sId)
      }
      case IntegerLiteral(number) => Matching.collect(scrutinee) {
        case trees.BVLiteral(true, value, base) =>
          Matching.conditionally(toBitSet(number, base) == value)
        case trees.IntegerLiteral(value) =>
          Matching.conditionally(value == number)
        case trees.FractionLiteral(numerator, denominator) =>
          Matching.conditionally(numerator == denominator * number)
      }
      case FractionLiteral(numerator, denominator) => Matching.collect(scrutinee) {
        case trees.FractionLiteral(otherNumerator, otherDenominator) =>
          Matching.conditionally(otherNumerator * denominator == numerator * otherDenominator)
      }
      case StringLiteral(string) => Matching.collect(scrutinee) {
        case trees.StringLiteral(otherString) =>
          Matching.conditionally(string == otherString)
      }
      case CharLiteral(character) => Matching.collect(scrutinee) {
        case trees.CharLiteral(otherCharacter) =>
          Matching.conditionally(character == otherCharacter)
      }
      case BooleanLiteral(value) => Matching.collect(scrutinee) {
        case trees.BooleanLiteral(otherValue) =>
          Matching.conditionally(value == otherValue)
      }
      case Abstraction(quantifier, bindings, body) => Matching.collect(scrutinee) {
        case trees.Forall(sBindings, sBody) if quantifier == Forall =>
          BindingSeqX.extract(bindings, sBindings).flatMap { opts =>
            ExprX.extract(body, sBody).extendLocal(opts.flatten)
          }
        case trees.Lambda(sBindings, sBody) if quantifier == Lambda =>
          BindingSeqX.extract(bindings, sBindings).flatMap { opts =>
            ExprX.extract(body, sBody).extendLocal(opts.flatten)
          }
      }
      case Application(callee, args) => Matching.collect(scrutinee) {
        case trees.Application(sCallee, sArgs) =>
          ExprX.extract(callee, sCallee) <> ExprSeqX.extract(args, sArgs)
      }
      case Assume(pred, body) => Matching.collect(scrutinee) {
        case trees.Assume(sPred, sBody) =>
          ExprX.extract(pred, sPred) <> ExprX.extract(body, sBody)
      }
      case SetConstruction(optTypes, elems) => Matching.collect(scrutinee) {
        case trees.FiniteSet(sElems, sType) =>
          Matching.optionally(optTypes.map(TypeSeqX.extract(_, Seq(sType)))) <>
          ExprSeqX.extract(elems, sElems)
      }
      case BagConstruction(optTypes, elems) => Matching.collect(scrutinee) {
        case trees.FiniteBag(sElems, sType) =>
          Matching.optionally(optTypes.map(TypeSeqX.extract(_, Seq(sType)))) <>
          ExprPairSeqX.extract(elems, sElems)
      }
      case MapConstruction(optTypes, elems, default) => Matching.collect(scrutinee) {
        case trees.FiniteMap(sElems, sDefault, sFrom, sTo) =>
          Matching.optionally(optTypes.map(TypeSeqX.extract(_, Seq(sFrom, sTo)))) <>
          ExprPairSeqX.extract(elems, sElems) <> ExprX.extract(default, sDefault)
      }
      case Let(binding, value, body) => Matching.collect(scrutinee) {
        case trees.Let(sBinding, sValue, sBody) =>
          BindingX.extract(binding, sBinding).flatMap { opt =>
            ExprX.extract(value, sValue) <> (ExprX.extract(body, sBody).extendLocal(opt.toSeq))
          }
      }
      case UnaryOperation(operator, expr) => {
        import Unary._

        Matching.collect((operator, scrutinee)) {
          case (Minus, trees.UMinus(sExpr)) =>
            ExprX.extract(expr, sExpr)
          case (Not, trees.Not(sExpr)) =>
            ExprX.extract(expr, sExpr)
          case (BVNot, trees.BVNot(sExpr)) =>
            ExprX.extract(expr, sExpr)
        }
      }
      case BinaryOperation(operator, lhs, rhs) => {
        import Binary._

        Matching.collect((operator, scrutinee)) {
          case (Plus, trees.Plus(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) <> ExprX.extract(rhs, sRhs)
          case (Minus, trees.Minus(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) <> ExprX.extract(rhs, sRhs)
          case (Times, trees.Times(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) <> ExprX.extract(rhs, sRhs)
          case (Division, trees.Division(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) <> ExprX.extract(rhs, sRhs)
          case (Remainder, trees.Remainder(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) <> ExprX.extract(rhs, sRhs)
          case (Modulo, trees.Modulo(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) <> ExprX.extract(rhs, sRhs)
          case (Implies, trees.Implies(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) <> ExprX.extract(rhs, sRhs)
          case (Equals, trees.Equals(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) <> ExprX.extract(rhs, sRhs)
          case (LessEquals, trees.LessEquals(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) <> ExprX.extract(rhs, sRhs)
          case (LessThan, trees.LessThan(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) <> ExprX.extract(rhs, sRhs)
          case (GreaterEquals, trees.GreaterEquals(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) <> ExprX.extract(rhs, sRhs)
          case (GreaterThan, trees.GreaterThan(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) <> ExprX.extract(rhs, sRhs)
          case (BVAnd, trees.BVAnd(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) <> ExprX.extract(rhs, sRhs)
          case (BVOr, trees.BVOr(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) <> ExprX.extract(rhs, sRhs)
          case (BVXor, trees.BVXor(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) <> ExprX.extract(rhs, sRhs)
          case (BVShiftLeft, trees.BVShiftLeft(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) <> ExprX.extract(rhs, sRhs)
          case (BVAShiftRight, trees.BVAShiftRight(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) <> ExprX.extract(rhs, sRhs)
          case (BVLShiftRight, trees.BVLShiftRight(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) <> ExprX.extract(rhs, sRhs)
        }
      }
      case NaryOperation(operator, args) => {
        import NAry._

        Matching.collect((operator, scrutinee)) {
          case (And, trees.And(sArgs)) =>
            ExprSeqX.extract(args, sArgs)
          case (Or, trees.Or(sArgs)) =>
            ExprSeqX.extract(args, sArgs)
        }.withValue(())
      }
      case If(condition, thenn, elze) => Matching.collect(scrutinee) {
        case trees.IfExpr(sCondition, sThenn, sElze) =>
          ExprX.extract(condition, sCondition) <>
          ExprX.extract(thenn, sThenn) <>
          ExprX.extract(elze, sElze)
      }
      case Cast(mode, expr, size) => {
        import Casts._

        Matching.collect((mode, scrutinee)) {
          case (Widen, trees.BVWideningCast(sExpr, trees.BVType(true, sSize))) if size == sSize =>
            ExprX.extract(expr, sExpr)
          case (Narrow, trees.BVNarrowingCast(sExpr, trees.BVType(true, sSize))) if size == sSize =>
            ExprX.extract(expr, sExpr)
        }
      }
      case Choose(binding, body) => Matching.collect(scrutinee) {
        case trees.Choose(sBinding, sBody) =>
          BindingX.extract(binding, sBinding).flatMap { opt =>
            ExprX.extract(body, sBody).extendLocal(opt.toSeq)
          }
      }
      case Invocation(id, optTypeArgs, args) => Matching.collect(scrutinee) {
        case trees.FunctionInvocation(sId, sTypeArgs, sArgs) =>
          ExprUseIdX.extract(id, sId) <>
          Matching.optionally(optTypeArgs.map(TypeSeqX.extract(_, sTypeArgs))) <>
          ExprSeqX.extract(args, sArgs)
        case trees.ADT(sId, sTypeArgs, sArgs) =>
          ExprUseIdX.extract(id, sId) <>
          Matching.optionally(optTypeArgs.map(TypeSeqX.extract(_, sTypeArgs))) <>
          ExprSeqX.extract(args, sArgs)
        case trees.Application(trees.Variable(sId, _, _), sArgs) =>
          ExprUseIdX.extract(id, sId) <>
          Matching.conditionally(optTypeArgs.isEmpty) <>
          ExprSeqX.extract(args, sArgs)
      }
      case PrimitiveInvocation(fun, optTypeArgs, args) => {
        import Primitive._

        Matching.withSymbols { symbols =>
          Matching.collect(scrutinee.getType(symbols)) {
            case trees.SetType(tpe) => Matching.pure(Seq(tpe))
            case trees.BagType(tpe) => Matching.pure(Seq(tpe))
            case trees.MapType(from, to) => Matching.pure(Seq(from, to))
          }
        }.flatMap { (sTypeArgs) =>
          Matching.optionally(optTypeArgs.map(TypeSeqX.extract(_, sTypeArgs))) <>
          Matching.collect((fun, scrutinee)) {
            case (SetAdd, trees.SetAdd(sLhs, sRhs)) =>
              ExprSeqX.extract(args, Seq(sLhs, sRhs))
            case (ElementOfSet, trees.ElementOfSet(sLhs, sRhs)) =>
              ExprSeqX.extract(args, Seq(sLhs, sRhs))
            case (SetIntersection, trees.SetIntersection(sLhs, sRhs)) =>
              ExprSeqX.extract(args, Seq(sLhs, sRhs))
            case (SetUnion, trees.SetUnion(sLhs, sRhs)) =>
              ExprSeqX.extract(args, Seq(sLhs, sRhs))
            case (SetDifference, trees.SetDifference(sLhs, sRhs)) =>
              ExprSeqX.extract(args, Seq(sLhs, sRhs))
            case (BagAdd, trees.BagAdd(sLhs, sRhs)) =>
              ExprSeqX.extract(args, Seq(sLhs, sRhs))
            case (MultiplicityInBag, trees.MultiplicityInBag(sLhs, sRhs)) =>
              ExprSeqX.extract(args, Seq(sLhs, sRhs))
            case (BagIntersection, trees.BagIntersection(sLhs, sRhs)) =>
              ExprSeqX.extract(args, Seq(sLhs, sRhs))
            case (BagUnion, trees.BagUnion(sLhs, sRhs)) =>
              ExprSeqX.extract(args, Seq(sLhs, sRhs))
            case (BagDifference, trees.BagDifference(sLhs, sRhs)) =>
              ExprSeqX.extract(args, Seq(sLhs, sRhs))
            case (MapApply, trees.MapApply(sLhs, sRhs)) =>
              ExprSeqX.extract(args, Seq(sLhs, sRhs))
            case (MapUpdated, trees.MapUpdated(sLhs, sMid, sRhs)) =>
              ExprSeqX.extract(args, Seq(sLhs, sMid, sRhs))
            case (Subset, trees.SubsetOf(sLhs, sRhs)) =>
              ExprSeqX.extract(args, Seq(sLhs, sRhs))
            case (SubString, trees.SubString(sLhs, sMid, sRhs)) =>
              ExprSeqX.extract(args, Seq(sLhs, sMid, sRhs))
            case (StringConcat, trees.StringConcat(sLhs, sRhs)) =>
              ExprSeqX.extract(args, Seq(sLhs, sRhs))
            case (StringLength, trees.StringLength(sExpr)) =>
              ExprSeqX.extract(args, Seq(sExpr))
          }
        }
      }
      case IsConstructor(expr, id) => Matching.collect(scrutinee) {
        case trees.IsConstructor(sExpr, sId) =>
          ExprX.extract(expr, sExpr) <>
          ExprUseIdX.extract(id, sId)
      }
      case Selection(expr, id) => Matching.collect(scrutinee) {
        case trees.ADTSelector(sExpr, sId) =>
          ExprX.extract(expr, sExpr) <> FieldIdX.extract(id, sId)
      }
      case Tuple(exprs) => Matching.collect(scrutinee) {
        case trees.Tuple(sExprs) =>
          ExprSeqX.extract(exprs, sExprs).withValue(())
      }
      case TupleSelection(expr, index) => Matching.collect(scrutinee) {
        case trees.TupleSelect(sExpr, sIndex) if index == sIndex =>
          ExprX.extract(expr, sExpr)
      }
      case TypeAnnotation(expr, tpe) =>
        Matching.withSymbols { implicit s: trees.Symbols =>
          ExprX.extract(expr, scrutinee) <> TypeX.extract(tpe, scrutinee.getType)
        }
    }
  }

  object ExprPairX extends Extractor[ExprPair, (trees.Expr, trees.Expr), Unit] {
    override def extract(template: ExprPair, scrutinee: (trees.Expr, trees.Expr)): Matching[Unit] = template match {
      case PairHole(index) => Matching(index -> scrutinee)
      case Pair(lhs, rhs) => ExprX.extract(lhs, scrutinee._1) <> ExprX.extract(rhs, scrutinee._2)
    }
  }

  object ExprSeqX extends HSeqX[Expr, trees.Expr, Unit](ExprX, ())

  object ExprPairSeqX extends HSeqX[ExprPair, (trees.Expr, trees.Expr), Unit](ExprPairX, ())
}