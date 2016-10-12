/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package grammars

import ast.FreshIdentifier

trait ValueGrammars { self: GrammarsUniverse =>
  import program._
  import trees._
  import symbols._

  /** A grammar of values (ground terms) */
  case object ValueGrammar extends SimpleExpressionGrammar {
    def computeProductions(t: Type): Seq[Prod] = t match {
      case BooleanType =>
        List(
          terminal(BooleanLiteral(true), One),
          terminal(BooleanLiteral(false), Zero)
        )
      case Int32Type =>
        List(
          terminal(IntLiteral(0), Zero),
          terminal(IntLiteral(1), One),
          terminal(IntLiteral(5), Constant)
        )
      case IntegerType =>
        List(
          terminal(IntegerLiteral(0), Zero),
          terminal(IntegerLiteral(1), One),
          terminal(IntegerLiteral(5), Constant)
        )
      case CharType =>
        List(
          terminal(CharLiteral('a'), Constant),
          terminal(CharLiteral('b'), Constant),
          terminal(CharLiteral('0'), Constant)
        )
      case RealType =>
        List(
          terminal(FractionLiteral(0, 1), Zero),
          terminal(FractionLiteral(1, 1), One),
          terminal(FractionLiteral(-1, 2), Constant),
          terminal(FractionLiteral(555, 42), Constant)
        )
      case StringType =>
        List(
          terminal(StringLiteral(""), Constant),
          terminal(StringLiteral("a"), Constant),
          terminal(StringLiteral("foo"), Constant),
          terminal(StringLiteral("bar"), Constant)
        )

      case tp: TypeParameter =>
        List(
          terminal(GenericValue(tp, 0))
        )

      case TupleType(stps) =>
        List(
          nonTerminal(stps, Tuple, Constructor(stps.isEmpty))
        )

      case adt: ADTType =>
        adt.getADT match {
          case tcons: TypedADTConstructor =>
            List(
              nonTerminal(tcons.fields.map(_.getType), ADT(adt, _), tagOf(tcons.definition))
            )

          case tsort: TypedADTSort =>
            tsort.constructors.map { tcons =>
              nonTerminal(tcons.fields.map(_.getType), ADT(tcons.toType, _), tagOf(tcons.definition))
            }
        }

      case st @ SetType(base) =>
        List(
          terminal(FiniteSet(Seq(), base), Constant),
          nonTerminal(List(base),       { elems => FiniteSet(elems, base) }, Constructor(isTerminal = false)),
          nonTerminal(List(base, base), { elems => FiniteSet(elems, base) }, Constructor(isTerminal = false))
        )
      
      case UnitType =>
        List(
          terminal(UnitLiteral(), Constant)
        )

      case FunctionType(from, to) =>
        val args = from map (tp => ValDef(FreshIdentifier("x", true), tp))
        List(
          nonTerminal(Seq(to), { case Seq(e) => Lambda(args, e) })
        )

      case _ =>
        Nil
    }
  }
}

