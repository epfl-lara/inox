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
  protected val trees: Trees
  import trees._

  /* Expressions */

  implicit class ExpressionWrapper(e: Expr) {

    // Arithmetic
    def + = Plus(e, _: Expr)
    def - = Minus(e, _: Expr)
    def % = Modulo(e, _: Expr)
    def / = Division(e, _: Expr)

    // Comparisons
    def <   = LessThan(e, _: Expr)
    def <=  = LessEquals(e, _: Expr)
    def >   = GreaterThan(e, _: Expr)
    def >=  = GreaterEquals(e, _: Expr)
    def === = Equals(e, _: Expr)

    // Boolean
    def &&  = And(e, _: Expr)
    def ||  = Or(e, _: Expr)
    def ==> = Implies(e, _: Expr)
    def unary_! = Not(e)

    // Tuple selections
    def _1 = TupleSelect(e, 1)
    def _2 = TupleSelect(e, 2)
    def _3 = TupleSelect(e, 3)
    def _4 = TupleSelect(e, 4)

    // Sets
    def size     = SetCardinality(e)
    def subsetOf = SubsetOf(e, _: Expr)
    def insert   = SetAdd(e, _: Expr)
    def ++ = SetUnion(e, _: Expr)
    def -- = SetDifference(e, _: Expr)
    def &  = SetIntersection(e, _: Expr)

    // Misc.

    def getField(selector: Identifier) = CaseClassSelector(e, selector)

    def apply(es: Expr*) = Application(e, es.toSeq)

    def isInstOf(tp: ClassType) = IsInstanceOf(e, tp)
    def asInstOf(tp: ClassType) = AsInstanceOf(e, tp)
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
  /*
  def E(s: Set[Expr]) = {
    require(s.nonEmpty)
    FiniteSet(s.toSeq, leastUpperBound(s.toSeq map (_.getType)).get)
  }
  */
  def E(vd: ValDef) = vd.toVariable // TODO: We should be able to remove this
  def E(id: Identifier) = new IdToFunInv(id)
  class IdToFunInv(id: Identifier) {
    def apply(tp1: Type, tps: Type*)(args: Expr*) =
      FunctionInvocation(id, tp1 +: tps.toSeq, args.toSeq)
    def apply(args: Expr*) =
      FunctionInvocation(id, Seq.empty, args.toSeq)
  }

  // if-then-else
  class DanglingElse private[DSL] (condThens: Seq[(Expr, Expr)]) {
    def else_if (cond2: Expr)(thenn2: Expr) = new DanglingElse(condThens :+ (cond2 -> thenn2))
    def else_ (theElse: Expr) = condThens.foldRight(theElse) {
      case ((cond, thenn), elze) =>IfExpr(cond, thenn, elze)
    }
  }

  def if_ (cond: Expr)(thenn: Expr) = new DanglingElse(Seq(cond -> thenn))

  def ite(cond: Expr, thenn: Expr, elze: Expr) = IfExpr(cond, thenn, elze)

  implicit class FunctionInv(fd: FunDef) {
    def apply(tp1: Type, tps: Type*)(args: Expr*) =
      FunctionInvocation(fd.id, tp1 +: tps.toSeq, args.toSeq)
    def apply(args: Expr*) =
      FunctionInvocation(fd.id, Seq.empty, args.toSeq)
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
  def let(vd: ValDef, v: Expr)(body: Variable => Expr) = {
    Let(vd, v, body(vd.toVariable))
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

  // Foralls
  def forall(vd: ValDef)(body: Variable => Expr) = {
    Forall(Seq(vd), body(vd.toVariable))
  }

  def forall(vd1: ValDef, vd2: ValDef)
            (body: (Variable, Variable) => Expr) = {
    Forall(Seq(vd1, vd2), body(vd1.toVariable, vd2.toVariable))
  }

  def forall(vd1: ValDef, vd2: ValDef, vd3: ValDef)
            (body: (Variable, Variable, Variable) => Expr) = {
    Forall(Seq(vd1, vd2, vd3), body(vd1.toVariable, vd2.toVariable, vd3.toVariable))
  }

  def forall(vd1: ValDef, vd2: ValDef, vd3: ValDef, vd4: ValDef)
            (body: (Variable, Variable, Variable, Variable) => Expr) = {
    Forall(
      Seq(vd1, vd2, vd3, vd4),
      body(vd1.toVariable, vd2.toVariable, vd3.toVariable, vd4.toVariable))
  }

  // Choose
  def choose(res: ValDef)(pred: Variable => Expr) = Choose(res, pred(res.toVariable))

  // Block-like
  class BlockSuspension(susp: Expr => Expr) {
    def in(e: Expr) = susp(e)
  }

  /* Types */
  def T(tp1: Type, tp2: Type, tps: Type*) = TupleType(tp1 :: tp2 :: tps.toList)
  def T(id: Identifier) = new IdToClassType(id)
  def T(str: String) = TypeParameter.fresh(str)

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
    val body = bodyBuilder(params map (_.toVariable))

    new FunDef(id, tParamDefs, params, retType, Some(body), Set())
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

