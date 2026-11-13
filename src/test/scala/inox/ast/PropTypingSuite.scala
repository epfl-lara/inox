/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package ast

import org.scalatest.funsuite.AnyFunSuite

/** The typing of propositions (see [[Types.PropType]]): which expressions are propositions,
  * where they are accepted, and how the [[QuantifierMode]] of the symbols types quantifiers. */
class PropTypingSuite extends AnyFunSuite {
  import inox.trees._
  import dsl._

  val fT = FunctionType(Seq(IntegerType()), IntegerType())
  val f = Variable.fresh("f", fT)
  val b = Variable.fresh("b", BooleanType())
  val i = IntegerLiteral(1)

  // forall x. f(x) > 0
  val positive: Expr = forall("x" :: IntegerType())(x => f(x) > E(BigInt(0)))

  // def pos(f: BigInt => BigInt): Prop = forall x. f(x) > 0
  val posID = FreshIdentifier("pos")
  val pos = mkFunDef(posID)() { _ =>
    (Seq("f" :: fT), PropType(), { case Seq(f) => forall("x" :: IntegerType())(x => f(x) > E(BigInt(0))) })
  }

  val boxID = FreshIdentifier("Box")
  val boxConsID = FreshIdentifier("BoxCons")
  val box = mkSort(boxID)("A") { case Seq(a) => Seq((boxConsID, Seq(ValDef(FreshIdentifier("v"), a)))) }

  val idID = FreshIdentifier("id")
  val id = mkFunDef(idID)("A") { case Seq(a) => (Seq("x" :: a), a, { case Seq(x) => x }) }

  val boolean = NoSymbols.withFunctions(Seq(pos, id)).withSorts(Seq(box))
  val propositional = boolean.withQuantifiers(QuantifierMode.Propositional)

  private def typed(tpe: Type, es: Expr*)(using Symbols): Unit =
    for (e <- es) assert(e.getType == tpe, s"for $e")

  test("Quantifiers are booleans by default") {
    assert(NoSymbols.modes.quantifiers == QuantifierMode.Boolean)
    given Symbols = boolean
    typed(BooleanType(), positive, Not(positive), And(positive, b), IfExpr(positive, b, b))
    // a boolean quantifier is a value
    typed(IntegerType(), IfExpr(positive, i, i), Let("p" :: BooleanType(), positive, i))
    typed(TupleType(Seq(BooleanType(), IntegerType())), Tuple(Seq(positive, i)))
  }

  test("Quantifiers are propositions under propositional quantifiers") {
    given Symbols = propositional
    typed(PropType(), positive, forall("y" :: IntegerType())(_ => positive))
    typed(Untyped, Forall(Seq("x" :: IntegerType()), i), Forall(Seq("p" :: PropType()), b))
  }

  test("Connectives over propositions are propositions") {
    given Symbols = propositional
    typed(BooleanType(), Not(b), And(b, b), Or(b, b), Implies(b, b), Equals(b, b))
    typed(PropType(),
      Not(positive), And(positive, b), And(b, positive), Or(b, positive), Implies(positive, b),
      Implies(b, positive), Equals(positive, b), Equals(positive, positive),
      IfExpr(b, positive, b), IfExpr(positive, b, b), IfExpr(positive, positive, positive),
      Let("y" :: IntegerType(), i, positive), Assume(b, positive))
    // a proposition can be named
    val p = "p" :: PropType()
    typed(PropType(), Let(p, positive, p.toVariable), Let(p, b, Not(p.toVariable)),
      Let(p, positive, Equals(p.toVariable, positive)))
    typed(IntegerType(), Let(p, positive, i), Let(p, positive, Assume(p.toVariable, i)))
    typed(Untyped, Let(p, positive, IfExpr(p.toVariable, i, i)), Let(p, i, i))
    typed(Untyped, And(positive, i), Not(i), Implies(i, positive), Equals(positive, i))
  }

  test("The value of a term can't depend on a proposition") {
    given Symbols = propositional
    typed(Untyped,
      IfExpr(positive, i, i),
      Let("p" :: BooleanType(), positive, i),
      Tuple(Seq(positive, i)),
      Lambda(Seq("y" :: IntegerType()), positive),
      Lambda(Seq("p" :: PropType()), i),
      FiniteSet(Seq(positive), BooleanType()),
      ADT(boxConsID, Seq(BooleanType()), Seq(positive)),
      ADT(boxConsID, Seq(PropType()), Seq(positive)),
      FunctionInvocation(idID, Seq(BooleanType()), Seq(positive)),
      FunctionInvocation(idID, Seq(PropType()), Seq(positive)),
      Application(Lambda(Seq("p" :: BooleanType()), i), Seq(positive)))
  }

  test("Variables bound to propositions are inferred") {
    given Symbols = propositional
    val p = "p" :: BooleanType()
    val q = "q" :: BooleanType()
    val e = Let(p, positive, Let(q, Not(p.toVariable), And(q.toVariable, b)))
    assert(e.getType == Untyped)
    val inference = transformers.PropositionInference(inox.trees)
    val inferred = inference.transform(e)
    assert(inferred.getType == PropType())
    val Let(p2, _, Let(q2, _, _)) = inferred: @unchecked
    assert(p2.id == p.id && p2.tpe == PropType() && q2.id == q.id && q2.tpe == PropType())
    // booleans stay booleans
    val same = Let(p, b, p.toVariable)
    assert(inference.transform(same) == same)
  }

  test("Predicate definitions are inferred") {
    // def all(f) = forall x. f(x) > 0, and def both(f) = all(f) && all(f), declared as booleans
    val allID = FreshIdentifier("all")
    val all = mkFunDef(allID)() { _ =>
      (Seq("f" :: fT), BooleanType(), { case Seq(f) => forall("x" :: IntegerType())(x => f(x) > E(BigInt(0))) })
    }
    val bothID = FreshIdentifier("both")
    val both = mkFunDef(bothID)() { _ =>
      (Seq("f" :: fT), BooleanType(), { case Seq(f) =>
        And(FunctionInvocation(allID, Seq(), Seq(f)), FunctionInvocation(allID, Seq(), Seq(f))) })
    }
    val inference = transformers.PropositionInference(inox.trees)
    val syms = NoSymbols.withFunctions(Seq(all, both, id))
    assert(inference.transform(syms) eq syms)
    val inferred = inference.transform(syms.withQuantifiers(QuantifierMode.Propositional))
    inferred.ensureWellFormed
    assert(inferred.modes.quantifiers == QuantifierMode.Propositional)
    assert(inferred.getFunction(allID).returnType == PropType())
    assert(inferred.getFunction(bothID).returnType == PropType())
    assert(inferred.getFunction(idID).returnType == syms.getFunction(idID).returnType)
  }

  test("Propositions are not data") {
    given Symbols = propositional
    for (tpe <- Seq[Type](
      TupleType(Seq(PropType(), IntegerType())), SetType(PropType()), BagType(PropType()),
      MapType(IntegerType(), PropType()), FunctionType(Seq(IntegerType()), PropType()),
      FunctionType(Seq(PropType()), IntegerType()), ADTType(boxID, Seq(PropType())),
      PiType(Seq("x" :: IntegerType()), PropType()),
      SigmaType(Seq("x" :: IntegerType()), PropType()),
      SetType(RefinementType("p" :: PropType(), b))
    )) assert(tpe.getType == Untyped, s"for $tpe")
    assert(PropType().getType == PropType())
  }

  test("Propositions can be refined") {
    given Symbols = propositional
    // { p: Prop | p ==> b }
    val p = "p" :: PropType()
    val refined = RefinementType(p, Implies(p.toVariable, b))
    assert(refined.getType == PropType())
    val q = "q" :: refined
    typed(PropType(), Let(q, positive, Not(q.toVariable)))
    // a refined proposition is not a boolean
    typed(Untyped, Let(q, positive, IfExpr(q.toVariable, i, i)))

    // def all(f): { r: Prop | r ==> f(0) > 0 } = forall x. f(x) > 0
    val allID = FreshIdentifier("all")
    val all = mkFunDef(allID)() { _ =>
      val f = "f" :: fT
      val r = "r" :: PropType()
      (Seq(f), RefinementType(r, Implies(r.toVariable, f.toVariable(E(BigInt(0))) > E(BigInt(0)))),
        { case Seq(f) => forall("x" :: IntegerType())(x => f(x) > E(BigInt(0))) })
    }
    val syms = propositional.withFunctions(Seq(all))
    syms.ensureWellFormed
    assert(FunctionInvocation(allID, Seq(), Seq(f)).getType(using syms) == PropType())
  }

  test("Refined propositions are inferred") {
    val inference = transformers.PropositionInference(inox.trees)
    def refined(name: String)(pred: Variable => Expr): RefinementType = {
      val vd = name :: BooleanType()
      RefinementType(vd, pred(vd.toVariable))
    }

    // val p: { p: Boolean | p ==> b } = forall x. f(x) > 0; !p
    val pT = refined("p")(p => Implies(p, b))
    val pVd = "q" :: pT
    val e = Let(pVd, positive, Not(pVd.toVariable))
    locally {
      given Symbols = propositional
      assert(e.getType == Untyped)
      val inferred = inference.transform(e)
      assert(inferred.getType == PropType())
      val Let(q, _, _) = inferred: @unchecked
      val RefinementType(p, Implies(v, `b`)) = q.tpe: @unchecked
      assert(q.id == pVd.id && p.tpe == PropType() && v == p.toVariable)
      // booleans stay refined booleans
      val same = Let(pVd, b, pVd.toVariable)
      assert(inference.transform(same) == same)
    }

    // def all(f): { r: Boolean | r ==> f(0) > 0 } = forall x. f(x) > 0
    val allID = FreshIdentifier("all")
    val all = mkFunDef(allID)() { _ =>
      val f = "f" :: fT
      (Seq(f), refined("r")(r => Implies(r, f.toVariable(E(BigInt(0))) > E(BigInt(0)))),
        { case Seq(f) => forall("x" :: IntegerType())(x => f(x) > E(BigInt(0))) })
    }
    val inferred = inference.transform(propositional.withFunctions(Seq(all)))
    inferred.ensureWellFormed
    val RefinementType(r, _) = inferred.getFunction(allID).returnType: @unchecked
    assert(r.tpe == PropType())
    assert(inferred.getFunction(allID).returnType.getType(using inferred) == PropType())
  }

  test("Specifications accept propositions") {
    given Symbols = propositional
    val g = "g" :: fT
    val refined = RefinementType(g, forall("x" :: IntegerType())(x => g.toVariable(x) > E(BigInt(0))))
    assert(refined.getType == fT)
    typed(IntegerType(), Assume(positive, i), Assume(b, i))
    typed(PropType(), pos(f), And(pos(f), b))
    typed(Untyped, IfExpr(pos(f), i, i))
    propositional.ensureWellFormed
    propositional.typeCheck(positive, PropType())
    intercept[propositional.TypeErrorException](propositional.typeCheck(positive, BooleanType()))
  }

  test("Booleans are propositions") {
    given Symbols = propositional
    import propositional._
    assert(isSubtypeOf(BooleanType(), PropType()))
    assert(!isSubtypeOf(PropType(), BooleanType()))
    assert(leastUpperBound(BooleanType(), PropType()) == PropType())
    assert(leastUpperBound(PropType(), BooleanType()) == PropType())
    assert(greatestLowerBound(BooleanType(), PropType()) == BooleanType())
    assert(leastUpperBound(IntegerType(), PropType()) == Untyped)
  }

  test("Propositions can't be parameters or fields") {
    val param = mkFunDef(FreshIdentifier("param"))() { _ =>
      (Seq("p" :: PropType()), PropType(), { case Seq(p) => p })
    }
    intercept[NotWellFormedException](NoSymbols.withFunctions(Seq(param)).ensureWellFormed)

    val field = mkSort(FreshIdentifier("S"))() { _ =>
      Seq((FreshIdentifier("C"), Seq(ValDef(FreshIdentifier("p"), PropType()))))
    }
    intercept[NotWellFormedException](NoSymbols.withSorts(Seq(field)).ensureWellFormed)
  }

  test("A function that returns a boolean can't return a proposition") {
    // under propositional quantifiers, a function that returns a boolean can't be a quantifier
    val bool = mkFunDef(FreshIdentifier("bool"))() { _ =>
      (Seq("f" :: fT), BooleanType(), { case Seq(f) => forall("x" :: IntegerType())(x => f(x) > E(BigInt(0))) })
    }
    NoSymbols.withFunctions(Seq(bool)).ensureWellFormed
    val syms = NoSymbols.withFunctions(Seq(bool)).withQuantifiers(QuantifierMode.Propositional)
    intercept[syms.TypeErrorException](syms.ensureWellFormed)
  }

  test("Derived symbols keep their modes") {
    assert(propositional.modes.quantifiers == QuantifierMode.Propositional)
    assert(propositional.withFunctions(Seq(id)).modes == propositional.modes)
    assert(propositional.withSorts(Seq(box)).modes == propositional.modes)
    assert(propositional.transform(new ConcreteIdentityTreeTransformer).modes == propositional.modes)
    assert(propositional != boolean)
    assert(propositional.withQuantifiers(QuantifierMode.Boolean) == boolean)
  }

  test("Types are cached per quantifier mode") {
    val e = And(positive, b)
    assert(e.getType(using boolean) == BooleanType())
    assert(e.getType(using propositional) == PropType())
    assert(e.getType(using boolean) == BooleanType())
  }

  test("Solvers see propositions as booleans") {
    val p = InoxProgram(propositional)
    val enc = solvers.theories.PropEncoder(p)
    given Symbols = enc.targetProgram.symbols
    assert(enc.targetProgram.symbols.modes.quantifiers == QuantifierMode.Boolean)
    assert(enc.targetProgram.symbols.getFunction(posID).returnType == BooleanType())
    typed(BooleanType(), enc.encode(positive), enc.encode(And(pos(f), b)))
    val named = "p" :: PropType()
    typed(BooleanType(), enc.encode(Let(named, positive, named.toVariable)))
    val refined = "q" :: RefinementType(named, Implies(named.toVariable, b))
    val encoded = enc.encode(Let(refined, positive, refined.toVariable))
    typed(BooleanType(), encoded)
    assert(!exprOps.exists { case Let(vd, _, _) => typeOps.exists(_ == PropType())(vd.tpe); case _ => false } (encoded))
    enc.targetProgram.symbols.ensureWellFormed

    // programs without propositions are left as they are
    val q = InoxProgram(NoSymbols.withFunctions(Seq(id)))
    assert(solvers.theories.PropEncoder(q).targetProgram.symbols == q.symbols)
  }

  test("The Prop type is printed and parsed") {
    assert(PropType().asString(using PrinterOptions()) == "Prop")
  }

  test("Trees that don't know of typing modes keep their symbols and their subtyping") {
    import PropTypingSuite.legacy
    import legacy._
    val syms = legacy.NoSymbols
    assert(syms.modes == TypingModes())
    assert(syms.withFunctions(Seq()).modes == TypingModes())
    assert(syms.withModes(TypingModes()) eq syms)
    assert(syms.withQuantifiers(QuantifierMode.Boolean) eq syms)
    intercept[UnsupportedOperationException](syms.withQuantifiers(QuantifierMode.Propositional))
    intercept[UnsupportedOperationException] {
      legacy.mkSymbols(Map.empty, Map.empty, TypingModes(QuantifierMode.Propositional))
    }

    // booleans are accepted where propositions are, under a subtyping without propositions
    given legacy.Symbols = syms
    val b = legacy.Variable.fresh("b", legacy.BooleanType())
    val x = legacy.ValDef.fresh("x", legacy.IntegerType())
    assert(!syms.isSubtypeOf(legacy.BooleanType(), legacy.PropType()))
    assert(legacy.Assume(b, legacy.IntegerLiteral(1)).getType == legacy.IntegerType())
    assert(legacy.RefinementType(x, b).getType == legacy.IntegerType())
    assert(legacy.And(b, legacy.Not(b)).getType == legacy.BooleanType())
    assert(legacy.Forall(Seq(x), b).getType == legacy.BooleanType())
  }
}

object PropTypingSuite {
  /** Trees as they were defined before symbols had typing modes, with their own subtyping. */
  object legacy extends Trees with SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort]
    ) extends SimpleSymbols {
      override val symbols: this.type = this
      override def isSubtypeOf(t1: Type, t2: Type): Boolean = t1.getType == t2.getType
    }

    override def mkSymbols(functions: Map[Identifier, FunDef], sorts: Map[Identifier, ADTSort]): Symbols =
      Symbols(functions, sorts)

    object printer extends Printer { val trees: legacy.type = legacy }
  }
}
