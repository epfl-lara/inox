/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

import scala.language.implicitConversions

/** This trait provides a DSL to create Inox trees.
  *
  * The two following principles are followed (hopefully with some consistency):
  * 1) When a fresh identifier needs to be introduced, the API provides constructors
  *    which are passed the fresh identifiers in the form of [[Definitions.ValDef ValDef]]s
  *    (construct them with [[TypeToValDef]]), and then a context
  *    (in the form of a function) to which the newly created identifiers will be passed.
  * 2) No implicit conversions are provided where there would be ambiguity.
  *    This refers mainly to Identifiers, which can be transformed to
  *    [[Types.ADTType ADTType]] or [[Expressions.FunctionInvocation FunctionInvocation]] or ... .
  *    Instead one-letter constructors are provided.
  */
trait DSL {
  protected val trees: Trees
  import trees._

  /* Expressions */

  extension (e: Expr) {

    // Arithmetic
    def + = Plus(e, _: Expr)
    def - = Minus(e, _: Expr)
    def * = Times(e, _: Expr)
    def % = Modulo(e, _: Expr)
    def / = Division(e, _: Expr)
    def unary_- = UMinus(e)

    // Comparisons
    def <   = LessThan(e, _: Expr)
    def <=  = LessEquals(e, _: Expr)
    def >   = GreaterThan(e, _: Expr)
    def >=  = GreaterEquals(e, _: Expr)
    def === = Equals(e, _: Expr)
    def !== = (e2: Expr) => Not(Equals(e, e2))

    // Boolean
    def &&  = And(e, _: Expr)
    def ||  = Or(e, _: Expr)
    def ==> = Implies(e, _: Expr)
    def unary_! = Not(e)

    // Tuple selections
    // Note: we do not name these _1, _2 etc. as it interferes with the compiler-generated _1, _2 etc. of case classes
    def _ts1 = TupleSelect(e, 1)
    def _ts2 = TupleSelect(e, 2)
    def _ts3 = TupleSelect(e, 3)
    def _ts4 = TupleSelect(e, 4)

    // Sets
    def subsetOf = SubsetOf(e, _: Expr)
    def insert   = SetAdd(e, _: Expr)
    def ++ = SetUnion(e, _: Expr)
    def -- = SetDifference(e, _: Expr)
    def &  = SetIntersection(e, _: Expr)
    def contains = ElementOfSet(_: Expr, e)

    // Misc.

    def getField(selector: Identifier) = ADTSelector(e, selector)

    def apply(es: Expr*) = Application(e, es.toSeq)

    def is(id: Identifier) = IsConstructor(e, id)
    def is(cons: ADTConstructor) = IsConstructor(e, cons.id)
  }

  // Literals
  def E(b: Byte): Expr = Int8Literal(b)
  def E(s: Short): Expr = Int16Literal(s)
  def E(i: Int): Expr = Int32Literal(i)
  def E(l: Long): Expr = Int64Literal(l)
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
  class DanglingElse private[DSL] (theCond: Expr, theThen: Expr) {
    def else_ (theElse: Expr) = IfExpr(theCond, theThen, theElse)
  }

  def if_ (cond: Expr)(thenn: Expr) = new DanglingElse(cond, thenn)

  def ite(cond: Expr, thenn: Expr, elze: Expr) = IfExpr(cond, thenn, elze)

  extension (fd: FunDef) {
    def apply(tp1: Type, tps: Type*)(args: Expr*) =
      FunctionInvocation(fd.id, tp1 +: tps.toSeq, args.toSeq)
    def apply(args: Expr*) =
      FunctionInvocation(fd.id, Seq.empty, args.toSeq)
  }

  extension (tp: TypeParameter) {
    def ## (id: Int) = GenericValue(tp, id)
  }

  // Syntax to make ValDefs, e.g. ("i" :: Integer)
  extension (nm: String) {
    def :: (tp: Type): ValDef = ValDef(FreshIdentifier(nm), tp)
  }

  /** Creates a [[Expressions.Let Let]]. A [[Definitions.ValDef ValDef]] and a
    * context is given; the identifier of the ValDef is passed to the context.
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
  def T(id: Identifier) = new IdToADTType(id)
  def T(str: String) = TypeParameter.fresh(str)

  class IdToADTType(id: Identifier) {
    def apply(tps: Type*) = ADTType(id, tps.toSeq)
  }

  extension (adt: ADTSort) {
    def apply(tps: Type*) = ADTType(adt.id, tps.toSeq)
  }

  class ADTCons(id: Identifier, tps: Seq[Type]) extends Tree {
    def apply(args: Expr*) = ADT(id, tps, args).copiedFrom(this)
  }

  class ADTConsIdentifier(id: Identifier) extends Tree {
    def apply(tps: Type*) = new ADTCons(id, tps).copiedFrom(this)
    def apply(args: Expr*) = new ADTCons(id, Seq.empty).copiedFrom(this).apply(args*)
  }

  extension (adt: ADTConstructor) {
    def apply(tp: Type, tps: Type*) = new ADTCons(adt.id, tp +: tps)
    def apply(args: Expr*) = new ADTCons(adt.id, Seq.empty).apply(args*)
  }

  extension (from: Type) {
    def =>: (to: Type) =
      FunctionType(Seq(from), to)
  }
  extension (from: (Type, Type)) {
    def =>: (to: Type) =
      FunctionType(Seq(from._1, from._2), to)
  }
  extension (from: (Type, Type, Type)) {
    def =>: (to: Type) =
      FunctionType(Seq(from._1, from._2, from._3), to)
  }
  extension (from: (Type, Type, Type, Type)) {
    def =>: (to: Type) =
      FunctionType(Seq(from._1, from._2, from._3, from._4), to)
  }

  def pi(vd: ValDef)(body: Variable => Type) = PiType(Seq(vd), body(vd.toVariable))

  def pi(vd1: ValDef, vd2: ValDef)
        (body: (Variable, Variable) => Type) = {
    PiType(Seq(vd1, vd2), body(vd1.toVariable, vd2.toVariable))
  }

  def pi(vd1: ValDef, vd2: ValDef, vd3: ValDef)
        (body: (Variable, Variable, Variable) => Type) = {
    PiType(Seq(vd1, vd2, vd3), body(vd1.toVariable, vd2.toVariable, vd3.toVariable))
  }

  def pi(vd1: ValDef, vd2: ValDef, vd3: ValDef, vd4: ValDef)
        (body: (Variable, Variable, Variable, Variable) => Type) = {
    PiType(
      Seq(vd1, vd2, vd3, vd4),
      body(vd1.toVariable, vd2.toVariable, vd3.toVariable, vd4.toVariable))
  }

  def sigma(vd: ValDef)(body: Variable => Type) = SigmaType(Seq(vd), body(vd.toVariable))

  def sigma(vd1: ValDef, vd2: ValDef)
           (body: (Variable, Variable) => Type) = {
    SigmaType(Seq(vd1, vd2), body(vd1.toVariable, vd2.toVariable))
  }

  def sigma(vd1: ValDef, vd2: ValDef, vd3: ValDef)
           (body: (Variable, Variable, Variable) => Type) = {
    SigmaType(Seq(vd1, vd2, vd3), body(vd1.toVariable, vd2.toVariable, vd3.toVariable))
  }

  def sigma(vd1: ValDef, vd2: ValDef, vd3: ValDef, vd4: ValDef)
           (body: (Variable, Variable, Variable, Variable) => Type) = {
    SigmaType(
      Seq(vd1, vd2, vd3, vd4),
      body(vd1.toVariable, vd2.toVariable, vd3.toVariable, vd4.toVariable))
  }

  def refinement(vd: ValDef)(body: Variable => Expr) = RefinementType(vd, body(vd.toVariable))

  /* Patterns */
  object C {
    def apply(id: Identifier): ADTConsIdentifier = new ADTConsIdentifier(id)
    def apply(id: Identifier, tps: Seq[Type]): ADTCons = new ADTCons(id, tps)
    def unapplySeq(expr: Expr): Option[(Identifier, Seq[Type], Seq[Expr])] = expr match {
      case ADT(id, tps, exprs) => Some((id, tps, exprs))
      case _ => None
    }
  }

  /* Definitions */

  /** Creates a [[Definitions.FunDef FunDef]] given only an [[Identifier]] for the name;
    * the (type) parameter [[Identifier]]s will be created fresh by this function.
    *
    * @param id The [[Identifier]] referring to this function.
    * @param tParamNames The names of the type parameters for this function.
    * @param builder A function from a Seq of type parameters (which should correspond
    *                to tParamNames) which, given these type parameters,
    *                should return
    *                (1) The sequence of parameters as [[Definitions.ValDef ValDef]]s (see [[TypeToValDef.::]])
    *                (2) The return type of the function
    *                (3) A context which, given the parameters, will return the body of the function.
    * @return A fresh and juicy [[Definitions.FunDef FunDef]]
    */
  def mkFunDef(id: Identifier, flags: Flag*)
              (tParamNames: String*)
              (builder: Seq[TypeParameter] => (Seq[ValDef], Type, Seq[Variable] => Expr)): FunDef = {
    val tParams = tParamNames map (TypeParameter.fresh(_))
    val tParamDefs = tParams map (TypeParameterDef(_))
    val (params, retType, bodyBuilder) = builder(tParams)
    val body = bodyBuilder(params map (_.toVariable))

    new FunDef(id, tParamDefs, params, retType, body, flags)
  }

  def mkSort(id: Identifier, flags: Flag*)
            (tParamNames: String*)
            (consBuilder: Seq[TypeParameter] => Seq[(Identifier, Seq[ValDef])]) = {
    val tParams = tParamNames map (TypeParameter.fresh(_))
    val tParamDefs = tParams map (TypeParameterDef(_))
    new ADTSort(id, tParamDefs, consBuilder(tParams).map(p => new ADTConstructor(p._1, id, p._2)), flags)
  }
}

