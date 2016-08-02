/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

import scala.language.implicitConversions

/** This trait provides a DSL to create Inox trees.
  *
  * The two following principles are followed (hopefully with some consistency):
  * 1) When a fresh identifier needs to be introduced, the API provides constructors
  *    which are passed the fresh identifiers in the form of [[inox.ast.Definitions.ValDef]]s
  *    (construct them with [[inox.ast.DSL.TypeToValDef]]), and then a context
  *    (in the form of a function) to which the newly created identifiers will be passed.
  * 2) No implicit conversions are provided where there would be ambiguity.
  *    This refers mainly to Identifiers, which can be transformed to
  *    [[inox.ast.Types.ClassType]] or [[inox.ast.Expressions.FunctionInvocation]] or ... .
  *    Instead one-letter constructors are provided.
  */
trait DSL {
  val program: Program
  import program._
  import trees._
  import symbols._

  /* Expressions */
  trait SimplificationLevel
  case object NoSimplify extends SimplificationLevel
  case object SafeSimplify extends SimplificationLevel

  private def simp(e1: => Expr, e2: => Expr)(implicit simpLvl: SimplificationLevel): Expr = simpLvl match {
    case NoSimplify   => e1
    case SafeSimplify => e2
  }

  implicit class ExprOps(e: Expr)(implicit simpLvl: SimplificationLevel) {

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
    def + = binOp(Plus, plus)
    def - = binOp(Minus, minus)
    def % = binOp(Modulo, Modulo)
    def / = binOp(Division, Division)

    // Comparisons
    def <   = binOp(LessThan, LessThan)
    def <=  = binOp(LessEquals, LessEquals)
    def >   = binOp(GreaterThan, GreaterThan)
    def >=  = binOp(GreaterEquals, GreaterEquals)
    def === = binOp(Equals, equality)

    // Boolean
    def &&  = binOp(And(_, _), and(_, _))
    def ||  = binOp(Or(_, _), or(_, _))
    def ==> = binOp(Implies, implies)
    def unary_! = unOp(Not, not)

    // Tuple selections
    def _1 = unOp(TupleSelect(_, 1), tupleSelect(_, 1, true))
    def _2 = unOp(TupleSelect(_, 2), tupleSelect(_, 2, true))
    def _3 = unOp(TupleSelect(_, 3), tupleSelect(_, 3, true))
    def _4 = unOp(TupleSelect(_, 4), tupleSelect(_, 4, true))

    // Sets
    def size     = SetCardinality(e)
    def subsetOf = binOp(SubsetOf, SubsetOf)
    def insert   = binOp(SetAdd, SetAdd)
    def ++ = binOp(SetUnion, SetUnion)
    def -- = binOp(SetDifference, SetDifference)
    def &  = binOp(SetIntersection, SetIntersection)

    // Misc.

    def getField(selector: String) = {
      val id = for {
        ct <- scala.util.Try(e.getType.asInstanceOf[ClassType]).toOption
        tcd <- ct.lookupClass
        tccd <- scala.util.Try(tcd.toCase).toOption
        field <- tccd.cd.fields.find(_.id.name == selector)
      } yield {
        field.id
      }
      CaseClassSelector(e, id.get)
    }

    def ensures(other: Expr) = Ensuring(e, other)

    def apply(es: Expr*) = Application(e, es.toSeq)

    def isInstOf(tp: ClassType) = unOp(IsInstanceOf(_, tp), symbols.isInstOf(_, tp))
    def asInstOf(tp: ClassType) = unOp(AsInstanceOf(_, tp), symbols.asInstOf(_, tp))
  }

  // Literals
  def E(i: Int): Expr = IntLiteral(i)
  def E(b: BigInt): Expr = IntegerLiteral(b)
  def E(b: Boolean): Expr = BooleanLiteral(b)
  def E(c: Char): Expr = CharLiteral(c)
  def E(): Expr = UnitLiteral()
  def E(n: BigInt, d: BigInt) = FractionLiteral(n, d)
  def E(s: String): Expr = StringLiteral(s)
  def E(e1: Expr, e2: Expr, es: Expr*): Expr = Tuple(e1 :: e2 :: es.toList)
  def E(s: Set[Expr]) = {
    require(s.nonEmpty)
    FiniteSet(s.toSeq, leastUpperBound(s.toSeq map (_.getType)).get)
  }
  def E(vd: ValDef) = vd.toVariable // TODO: We should be able to remove this
  def E(id: Identifier) = new IdToFunInv(id)
  class IdToFunInv(id: Identifier) {
    def apply(tps: Type*)(args: Expr*) =
      FunctionInvocation(id, tps.toSeq, args.toSeq)
  }

  // if-then-else
  class DanglingElse(cond: Expr, thenn: Expr) {
    def else_ (theElse: Expr) = IfExpr(cond, thenn, theElse)
  }

  def if_ (cond: Expr)(thenn: Expr) = new DanglingElse(cond, thenn)

  def ite(cond: Expr, thenn: Expr, elze: Expr) = IfExpr(cond, thenn, elze)

  implicit class FunctionInv(fd: FunDef) {
    def apply(args: Expr*) = functionInvocation(fd, args.toSeq)
  }

  implicit class CaseClassToExpr(ct: ClassType) {
    def apply(args: Expr*) = CaseClass(ct, args)
  }

  implicit class GenValue(tp: TypeParameter) {
    def ## (id: Int) = GenericValue(tp, id)
  }

  // Syntax to make ValDefs, e.g. ("i" :: Integer)
  implicit class TypeToValDef(tp: Type) {
    def :: (nm: String): ValDef = ValDef(FreshIdentifier(nm, true), tp)
  }

  /** Creates a [[Let]]. A [[ValDef]] and a context is given; the identifier of the ValDef
    * is passed to the context.
    *
    * @param vd The ValDef which will be bound in the body (see [[TypeToValDef.::]])
    * @param v The value bound to the let-variable
    * @param body The context which will be filled with the let-variable
    */
  def let(vd: ValDef, v: Expr)(body: Variable => Expr)(implicit simpLvl: SimplificationLevel) = {
    simp(
      Let(vd, v, body(vd.toVariable)),
      symbols.let(vd, v, body(vd.toVariable))
    )
  }

  // Lambdas
  def \(vd: ValDef)(body: Variable => Expr) = {
    Lambda(Seq(vd), body(vd.toVariable))
  }

  def \(vd1: ValDef, vd2: ValDef)
       (body: (Variable, Variable) => Expr) = {
    Lambda(Seq(vd1, vd2), body(vd1.toVariable, vd2.toVariable))
  }

  def \(vd1: ValDef, vd2: ValDef, vd3: ValDef)
       (body: (Variable, Variable, Variable) => Expr) = {
    Lambda(Seq(vd1, vd2, vd3), body(vd1.toVariable, vd2.toVariable, vd3.toVariable))
  }

  def \(vd1: ValDef, vd2: ValDef, vd3: ValDef, vd4: ValDef)
       (body: (Variable, Variable, Variable, Variable) => Expr) = {
    Lambda(
      Seq(vd1, vd2, vd3, vd4),
      body(vd1.toVariable, vd2.toVariable, vd3.toVariable, vd4.toVariable)
    )
  }

  // Block-like
  class BlockSuspension(susp: Expr => Expr) {
    def in(e: Expr) = susp(e)
  }

  /* Types */
  def T(tp1: Type, tp2: Type, tps: Type*) = TupleType(tp1 :: tp2 :: tps.toList)
  def T(id: Identifier) = new IdToClassType(id)
  class IdToClassType(id: Identifier) {
    def apply(tps: Type*) = ClassType(id, tps.toSeq)
  }
  implicit class FunctionTypeBuilder(to: Type) {
    def =>: (from: Type) =
      FunctionType(Seq(from), to)
    def =>: (from: (Type, Type)) =
      FunctionType(Seq(from._1, from._2), to)
    def =>: (from: (Type, Type, Type)) =
      FunctionType(Seq(from._1, from._2, from._3), to)
    def =>: (from: (Type, Type, Type, Type)) =
      FunctionType(Seq(from._1, from._2, from._3, from._4), to)
  }

  // TODO remove this at some point
  private def testTypes: Unit = {
    val ct1 = FreshIdentifier("ct1")
    val ct2 = FreshIdentifier("ct2")
    T(
      T(ct1)(),
      T(ct1)(T(ct2)(), IntegerType),
      (T(ct1)(), T(ct2)()) =>: T(ct1)()
    )
  }

  /* Definitions */

  /** Creates a [[FunDef]] given only an [[Identifier]] for the name;
    * the (type) parameter [[Identifier]]s will be created fresh by this function.
    *
    * @param id The [[Identifier]] referring to this function.
    * @param tParamNames The names of the type parameters for this function.
    * @param builder A function from a Seq of type parameters (which should correspond
    *                to tParamNames) which, given these type parameters,
    *                should return
    *                (1) The sequence of parameters as [[ValDef]]s (see [[TypeToValDef.::]])
    *                (2) The return type of the function
    *                (3) A context which, given the parameters, will return the body of the function.
    * @return A fresh and juicy [[FunDef]]
    */
  def mkFunDef(id: Identifier)
              (tParamNames: String*)
              (builder: Seq[TypeParameter] => (Seq[ValDef], Type, Seq[Variable] => Expr)) = {
    val tParams = tParamNames map TypeParameter.fresh
    val tParamDefs = tParams map TypeParameterDef
    val (params, retType, bodyBuilder) = builder(tParams)
    val fullBody = bodyBuilder(params map (_.toVariable))

    new FunDef(id, tParamDefs, params, retType, fullBody, Set())
  }

  def mkAbstractClass(id: Identifier)
                     (tParamNames: String*)
                     (children: Seq[Identifier]) = {
    val tParams = tParamNames map TypeParameter.fresh
    val tParamDefs = tParams map TypeParameterDef
    new AbstractClassDef(id, tParamDefs, children, Set())
  }

  def mkCaseClass(id: Identifier)
                 (tParamNames: String*)
                 (parent: Option[Identifier])
                 (fieldBuilder: Seq[TypeParameter] => Seq[ValDef]) = {
    val tParams = tParamNames map TypeParameter.fresh
    val tParamDefs = tParams map TypeParameterDef
    val fields = fieldBuilder(tParams)
    new CaseClassDef(id, tParamDefs, parent, fields, Set())
  }

  // TODO: Remove this at some point
  /* This defines
    def f[A, B](i: BigInt, j: C[A], a: A): (BigInt, C[A]) = {
      (42, C[A](a))
    }
  */
  private def testDefs = {
    val c = T(FreshIdentifier("c"))
    val f = FreshIdentifier("f")
    mkFunDef(f)("A", "B"){ case Seq(aT, bT) => (
      Seq("i" :: IntegerType, "j" :: c(aT), "a" :: aT),
      T(IntegerType, c(aT)),
      { case Seq(i, j, a) => E(E(42), c(aT)(a)) }
    )}
  }

}

