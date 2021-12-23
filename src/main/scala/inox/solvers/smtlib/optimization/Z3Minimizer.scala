/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib
package optimization

trait Z3Minimizer extends Z3Optimizer {
  import program._
  import program.trees._
  import program.symbols._
  import exprOps.variablesOf

  /**
   * Gets the 'zero' literals for the given field,
   * given the types of "parents" of the expr to avoid infinite recursion.
   */
  private def getZeroLiterals(field: ValDef, parentTypes: Set[Type]): Seq[Expr] = field.tpe match {
    case BVType(signed, size) => Seq(BVLiteral(signed, 0, size))
    case adt @ ADTType(_, _) =>
      if (parentTypes.contains(adt)) Seq()
      else adt.lookupSort match {
        case Some(tsort) => tsort.constructors.flatMap(_.fields).distinct.flatMap(f => getZeroLiterals(f, parentTypes + adt))
        case None => Seq()
      }
    case IntegerType() => Seq(IntegerLiteral(0))
    case _ => Seq()
  }

  /**
   * Gets the expressions that should be minimized for the given expr,
   * given the types of "parents" of the expr to avoid an infinite recursion.
   */
  private def sizersOf(e: Expr, parentTypes: Set[Type]): Seq[Expr] = {
    /**
     * Gets the expressions that should be minimized for the given ADT constructors.
     * This is not as simple as it first appears because of the split between the bitvector and integer worlds;
     * one cannot merely return a big "sum of all fields" expression, since adding a bitvector and an integer makes no sense.
     * Furthermore, ADT constructors may themselves include ADTs as fields.
     * For instance, for ADT X with ctors X1(a: BV32) and X2(a: BV32, b: Int) and ADT Y with ctors Y1(a: BV64) and Y2(b: X),
     * the minimizers of y: Y are ["if y is Y1 then y.a else BV64(0)", "if y is Y1 then BV32(0) else y.b.a", "if y is Y1 then Int(0) else if y.b is X1 then Int(0) else y.b.b"],
     * plus one representing the overall size of the ADT to favor "smaller" constructors such as X1 over X2.
     * (The concept of "smaller" is not well-defined either, e.g., one could reasonably argue that P(a: BV16, b: BV16) is either "smaller" or "larger" than Q(c: BV64)
     *  due to the size in bits vs number of fields; we go with the number of fields)
     */
    def adtSizers(ctors: Seq[TypedADTConstructor]): Seq[Expr] = {
      // zeroes must be of the same length as what sizer returns
      def rec(ctors: Seq[TypedADTConstructor], zeroes: Seq[Expr], sizer: TypedADTConstructor => Seq[Expr]): Seq[Expr] = ctors match {
        case Seq() => zeroes
        // not strictly necessary but nice to not have an if whose else branch is unsatisfiable
        case Seq(ctor) => sizer(ctor)
        case Seq(ctor, tl @ _*) => sizer(ctor).zip(rec(tl, zeroes, sizer)).map{case (a,b) => IfExpr(IsConstructor(e, ctor.id), a, b)}
      }
      def fieldSizer(field: ValDef)(ctor: TypedADTConstructor): Seq[Expr] = {
        if (ctor.fields.contains(field)) sizersOf(ADTSelector(e, field.id), parentTypes + field.tpe) else getZeroLiterals(field, parentTypes)
      }
      // BV32 for the size, because the number of fields can't be larger anyway (since fields.length is a Scala int),
      // let's not force the use of integers if it's not necessary
      val adtSize = rec(ctors, Seq(BVLiteral(false, 0, 32)), c => Seq(BVLiteral(false, c.fields.length, 32)))
      val fieldSizes = ctors.flatMap(_.fields).distinct.filter(f => !parentTypes.contains(f.tpe)).flatMap(f => rec(ctors, getZeroLiterals(f, parentTypes), fieldSizer(f)))
      adtSize ++ fieldSizes
    }

    e.getType match {
      case BVType(signed, size) => Seq(if (signed) IfExpr(GreaterEquals(e, BVLiteral(signed, 0, size)), e, UMinus(e)) else e)
      case IntegerType() => Seq(IfExpr(GreaterEquals(e, IntegerLiteral(0)), e, UMinus(e)))
      case adt @ ADTType(_, _) =>
        if (parentTypes.contains(adt)) Seq()
        else adt.lookupSort match {
          case Some(tsort) => adtSizers(tsort.constructors)
          case None => Seq()
        }
      case _ => Seq()
    }
  }

  override def assertCnstr(expr: Expr): Unit = {
    for (freeVar <- variablesOf(expr) ; toMinimize <- sizersOf(freeVar, Set())) {
      minimize(toMinimize)
    }
    super.assertCnstr(expr)
  }
}
