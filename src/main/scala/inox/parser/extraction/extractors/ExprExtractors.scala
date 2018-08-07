package inox
package parser
package extraction
package extractors

trait ExprExtractors { self: Extractors =>
  import Exprs._
  implicit object ExprX extends Extractor[Expr, trees.Expr, Unit] {
    override def extract(template: Expr, scrutinee: trees.Expr): Matching[Unit] = template match {
      case ExprHole(index) => Matching(index -> scrutinee)
      case UnitLiteral() => Matching.collect(scrutinee) {
        case trees.UnitLiteral() => Matching.success
      }
      case Variable(id) => Matching.collect(scrutinee) {
        case trees.Variable(sId, _, _) => UseIdX.extract(id, sId)
      }
      case IntegerLiteral(number) => Matching.collect(scrutinee) {
        case trees.BVLiteral(value, base) =>
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
          ExprX.extract(callee, sCallee) << ExprSeqX.extract(args, sArgs)
      }
      case Assume(pred, body) => Matching.collect(scrutinee) {
        case trees.Assume(sPred, sBody) =>
          ExprX.extract(pred, sPred) << ExprX.extract(body, sBody)
      }
      case SetConstruction(elems) => Matching.collect(scrutinee) {
        case trees.FiniteSet(sElems, _) =>
          ExprSeqX.extract(elems, sElems).withValue(())
      }
      case BagConstruction(elems) => Matching.collect(scrutinee) {
        case trees.FiniteBag(sElems, _) =>
          ExprPairSeqX.extract(elems, sElems).withValue(())
      }
      case MapConstruction(elems, default) => Matching.collect(scrutinee) {
        case trees.FiniteMap(sElems, sDefault, _, _) =>
          ExprPairSeqX.extract(elems, sElems) >> ExprX.extract(default, sDefault)
      }
      case Let(binding, value, body) => Matching.collect(scrutinee) {
        case trees.Let(sBinding, sValue, sBody) =>
          BindingX.extract(binding, sBinding).flatMap { opt =>
            ExprX.extract(value, sValue) >> (ExprX.extract(body, sBody).extendLocal(opt.toSeq))
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
          case (StringLength, trees.StringLength(sExpr)) =>
            ExprX.extract(expr, sExpr)
        }
      }
      case BinaryOperation(operator, lhs, rhs) => {
        import Binary._

        Matching.collect((operator, scrutinee)) {
          case (Plus, trees.Plus(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (Minus, trees.Minus(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (Times, trees.Times(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (Division, trees.Division(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (Remainder, trees.Remainder(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (Modulo, trees.Modulo(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (Implies, trees.Implies(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (Equals, trees.Equals(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (LessEquals, trees.LessEquals(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (LessThan, trees.LessThan(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (GreaterEquals, trees.GreaterEquals(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (GreaterThan, trees.GreaterThan(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (BVAnd, trees.BVAnd(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (BVOr, trees.BVOr(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (BVXor, trees.BVXor(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (BVShiftLeft, trees.BVShiftLeft(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (BVAShiftRight, trees.BVAShiftRight(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (BVLShiftRight, trees.BVLShiftRight(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (SetAdd, trees.SetAdd(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (ElementOfSet, trees.ElementOfSet(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (SetIntersection, trees.SetIntersection(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (SetUnion, trees.SetUnion(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (SetDifference, trees.SetDifference(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (BagAdd, trees.BagAdd(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (MultiplicityInBag, trees.MultiplicityInBag(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (BagIntersection, trees.BagIntersection(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (BagUnion, trees.BagUnion(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (BagDifference, trees.BagDifference(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (MapApply, trees.MapApply(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
          case (StringConcat, trees.StringConcat(sLhs, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(rhs, sRhs)
        }
      }
      case TernaryOperation(operator, lhs, mid, rhs) => {
        import Ternary._

        Matching.collect((operator, scrutinee)) {
          case (SubString, trees.SubString(sLhs, sMid, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(mid, sMid) >> ExprX.extract(rhs, sRhs)
          case (MapUpdated, trees.MapUpdated(sLhs, sMid, sRhs)) =>
            ExprX.extract(lhs, sLhs) >> ExprX.extract(mid, sMid) >> ExprX.extract(rhs, sRhs)
        }
      }
    }
  }

  object ExprPairX extends Extractor[ExprPair, (trees.Expr, trees.Expr), Unit] {
    override def extract(template: ExprPair, scrutinee: (trees.Expr, trees.Expr)): Matching[Unit] = template match {
      case PairHole(index) => Matching(index -> scrutinee)
      case Pair(lhs, rhs) => ExprX.extract(lhs, scrutinee._1) >> ExprX.extract(rhs, scrutinee._2)
    }
  }

  object ExprSeqX extends HSeqX[Expr, trees.Expr, Unit](ExprX, ())

  object ExprPairSeqX extends HSeqX[ExprPair, (trees.Expr, trees.Expr), Unit](ExprPairX, ())
}