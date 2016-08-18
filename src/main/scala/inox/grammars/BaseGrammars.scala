/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package grammars

trait BaseGrammars { self: GrammarsUniverse =>
  import program._
  import trees._
  import symbols._

  /** The basic grammar for Inox expressions.
    * Generates the most obvious expressions for a given type,
    * without regard of context (variables in scope, current function etc.)
    * Also does some trivial simplifications.
    */
  case object BaseGrammar extends SimpleExpressionGrammar {

    def computeProductions(t: Type): Seq[Prod] = t match {
      case BooleanType =>
        List(
          terminal(BooleanLiteral(false), BooleanC),
          terminal(BooleanLiteral(true),  BooleanC),
          nonTerminal(List(BooleanType), { case Seq(a) => not(a) }, Not),
          nonTerminal(List(BooleanType, BooleanType), { case Seq(a, b) => and(a, b) }, And),
          nonTerminal(List(BooleanType, BooleanType), { case Seq(a, b) => or(a, b)  }, Or ),
          nonTerminal(List(Int32Type,   Int32Type),   { case Seq(a, b) => LessThan(a, b)   }),
          nonTerminal(List(Int32Type,   Int32Type),   { case Seq(a, b) => LessEquals(a, b) }),
          nonTerminal(List(IntegerType, IntegerType), { case Seq(a, b) => LessThan(a, b)   }),
          nonTerminal(List(IntegerType, IntegerType), { case Seq(a, b) => LessEquals(a, b) })
        )
      case Int32Type =>
        List(
          terminal(IntLiteral(0), Zero),
          terminal(IntLiteral(1), One ),
          nonTerminal(List(Int32Type, Int32Type), { case Seq(a,b) => plus(a, b)  }, Plus ),
          nonTerminal(List(Int32Type, Int32Type), { case Seq(a,b) => minus(a, b) }, Minus),
          nonTerminal(List(Int32Type, Int32Type), { case Seq(a,b) => times(a, b) }, Times)
        )

      case IntegerType =>
        List(
          terminal(IntegerLiteral(0), Zero),
          terminal(IntegerLiteral(1), One ),
          nonTerminal(List(IntegerType, IntegerType), { case Seq(a,b) => plus(a, b)  }, Plus ),
          nonTerminal(List(IntegerType, IntegerType), { case Seq(a,b) => minus(a, b) }, Minus),
          nonTerminal(List(IntegerType, IntegerType), { case Seq(a,b) => times(a, b) }, Times)//,
          //nonTerminal(List(IntegerType, IntegerType), { case Seq(a,b) => Modulo(a, b)   }, Mod),
          //nonTerminal(List(IntegerType, IntegerType), { case Seq(a,b) => Division(a, b) }, Div)
        )

      case TupleType(stps) =>
        List(
          nonTerminal(stps, Tuple, Constructor(isTerminal = false))
        )

      case adt: ADTType =>
        adt.getADT match {
          case tcons: TypedADTConstructor =>
            List(
              nonTerminal(tcons.fields.map(_.getType), ADT(adt, _), tagOf(tcons.definition) )
            )

          case tsort: TypedADTSort =>
            tsort.constructors.map { tcons =>
              nonTerminal(tcons.fields.map(_.getType), ADT(tcons.toType, _), tagOf(tcons.definition) )
            }
        }

      case st @ SetType(base) =>
        List(
          terminal(FiniteSet(Seq(), base), Constant),
          nonTerminal(List(base),   { case elems     => FiniteSet(elems, base) }, Constructor(isTerminal = false)),
          nonTerminal(List(st, st), { case Seq(a, b) => SetUnion(a, b) }),
          nonTerminal(List(st, st), { case Seq(a, b) => SetIntersection(a, b) }),
          nonTerminal(List(st, st), { case Seq(a, b) => SetDifference(a, b) })
        )

      case UnitType =>
        List(
          terminal(UnitLiteral(), Constant)
        )

      case _ =>
        Nil
    }
  }
}
