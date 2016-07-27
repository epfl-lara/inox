/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

import scala.language.implicitConversions

trait DSL {
  val program: Program
  import program._
  import trees._
  import symbols._

  trait SimplificationLevel
  case object NoSimplify extends SimplificationLevel
  case object SafeSimplify extends SimplificationLevel

  private def simp(e1: => Expr, e2: => Expr)(implicit simpLvl: SimplificationLevel): Expr = simpLvl match {
    case NoSimplify   => e1
    case SafeSimplify => e2
  }

  implicit class ExprDSL(e: Expr)(implicit simpLvl: SimplificationLevel) {

    private def binOp(
      e1: (Expr, Expr) => Expr,
      e2: (Expr, Expr) => Expr
    ) = {
      (other: Expr) => simp(e1(e, other), e2(e,other))
    }

    private def unOp(
      e1: (Expr) => Expr,
      e2: (Expr) => Expr
    ) = {
      simp(e1(e), e2(e))
    }

    // Arithmetic
    def +   = binOp(Plus, plus)
    def -   = binOp(Minus, minus)
    def === = binOp(Equals, equality)
    def &&  = binOp(And(_, _), and(_, _))
    def ||  = binOp(Or(_, _), or(_, _))
    def ==> = binOp(Implies, implies)
    def %   = binOp(Modulo, Modulo)
    def /   = binOp(Division, Division)

    // Comparisons
    def <  = binOp(LessThan, LessThan)
    def <= = binOp(LessEquals, LessEquals)
    def >  = binOp(GreaterThan, GreaterThan)
    def >= = binOp(GreaterEquals, GreaterEquals)

    // Tuple selections
    def _1 = unOp(TupleSelect(_, 1), tupleSelect(_, 1, true))
    def _2 = unOp(TupleSelect(_, 2), tupleSelect(_, 2, true))
    def _3 = unOp(TupleSelect(_, 3), tupleSelect(_, 3, true))
    def _4 = unOp(TupleSelect(_, 4), tupleSelect(_, 4, true))

    // Sets
    def size      = SetCardinality(e)
    def subsetOf  = binOp(SubsetOf, SubsetOf)
    def ++ = binOp(SetUnion, SetUnion)
    def -- = binOp(SetDifference, SetDifference)
    def &  = binOp(SetIntersection, SetIntersection)

    // Misc.

    def getField(cc: ClassType, selector: String) = {
      val id = for {
        tcd <- cc.lookupClass
        tccd <- scala.util.Try(tcd.toCase).toOption
        field <- tccd.cd.fields.find(_.id.name == selector)
      } yield {
        field.id
      }
      CaseClassSelector(cc, e, id.get)
    }

    def ensures(other: Expr) = Ensuring(e, other)

    def apply(es: Expr*) = Application(e, es.toSeq)

    def isInstOf(tp: ClassType) = unOp(IsInstanceOf(_, tp), symbols.isInstOf(_, tp))
    def asInstOf(tp: ClassType) = unOp(AsInstanceOf(_, tp), symbols.asInstOf(_, tp))
  }

  private def tpl(es: Expr*) = Tuple(es.toSeq)

  // Literals
  def L(i: Int): Expr = IntLiteral(i)
  def L(b: BigInt): Expr = IntegerLiteral(b)
  def L(b: Boolean): Expr = BooleanLiteral(b)
  def L(c: Char): Expr = CharLiteral(c)
  def L(): Expr = UnitLiteral()
  def L(n: BigInt, d: BigInt) = FractionLiteral(n, d)
  def L(s: String): Expr = StringLiteral(s)
  def L(e1: Expr, e2: Expr): Expr = tpl(e1, e2)
  def L(e1: Expr, e2: Expr, e3: Expr): Expr = tpl(e1, e2, e3)
  def L(e1: Expr, e2: Expr, e3: Expr, e4: Expr): Expr = tpl(e1, e2, e3, e4)
  def L(s: Set[Expr]) = {
    require(s.nonEmpty)
    FiniteSet(s.toSeq, leastUpperBound(s.toSeq map (_.getType)).get)
  }

  // if-then-else
  class DanglingElse(cond: Expr, thenn: Expr) {
    def else_ (theElse: Expr) = IfExpr(cond, thenn, theElse)
  }

  def if_ (cond: Expr)(thenn: Expr) = new DanglingElse(cond, thenn)

  implicit class FunctionInv(fd: FunDef) {
    def apply(args: Expr*) = functionInvocation(fd, args.toSeq)
  }

  implicit class CC(ct: ClassType) {
    def apply(args: Expr*) = CaseClass(ct, args)
  }

  implicit class GenValue(tp: TypeParameter) {
    def ## (id: Int) = GenericValue(tp, id)
  }

  // This introduces valdefs
  implicit class TypeToValDef(tp: Type) {
    def :: (nm: String): ValDef = ValDef(FreshIdentifier(nm, true), tp)
  }

  def let(vd: ValDef, v: Expr)(body: Expr => Expr)(implicit simpLvl: SimplificationLevel) = {
    simp(
      Let(vd, v, body(vd.toVariable)),
      symbols.let(vd, v, body(vd.toVariable))
    )
  }

  // Lambdas
  def \(vd: ValDef)(body: Expr => Expr) = {
    Lambda(Seq(vd), body(vd.toVariable))
  }

  def \(vd1: ValDef, vd2: ValDef)(body: (Expr, Expr) => Expr) = {
    Lambda(Seq(vd1, vd2), body(vd1.toVariable, vd2.toVariable))
  }

  def \(vd1: ValDef, vd2: ValDef, vd3: ValDef)(body: (Expr, Expr, Expr) => Expr) = {
    Lambda(Seq(vd1, vd2, vd3), body(vd1.toVariable, vd2.toVariable, vd3.toVariable))
  }

  def \(vd1: ValDef, vd2: ValDef, vd3: ValDef, vd4: ValDef)
       (body: (Expr, Expr, Expr, Expr) => Expr) = {
    Lambda(
      Seq(vd1, vd2, vd3, vd4),
      body(vd1.toVariable, vd2.toVariable, vd3.toVariable, vd4.toVariable)
    )
  }

  // Block-like
  class BlockSuspension(susp: Expr => Expr) {
    def in(e: Expr) = susp(e)
  }

  def prec(e: Expr) = new BlockSuspension(Require(e, _))
  def assertion(e: Expr) = new BlockSuspension(Assert(e, None, _))
  def assertion(e: Expr, msg: String) = new BlockSuspension(Assert(e, Some(msg), _))

  implicit class PatternMatch(scrut: Expr) {
    def matchOn(cases: MatchCase* ) = {
      MatchExpr(scrut, cases.toList)
    }
  }

  implicit class PatternSuspension(pat: Pattern) {
    def ~> (rhs: Expr) = MatchCase(pat, None, rhs)
  }

  // TODO: Remove this at some point
  private def test(e1: Expr, e2: Expr)(implicit simpl: SimplificationLevel) = {
    val pattern = WildcardPattern(None)

    prec(e1) in
      let("i" :: Untyped, e1) { i =>
        if_ (\("j" :: Untyped)(j => e1(j))) {
          e1 + e2 + i + L(42)
        } else_ {
          assertion(L(true), "Weird things") in
            e2 matchOn (
            pattern ~> e1,
            pattern ~> e2
            )
        }
      }
  } ensures e2

}

