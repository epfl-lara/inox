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

  // case class Claim(holds: Prop, n: BigInt), and case class Wrap(claim: Claim)
  val claimID = FreshIdentifier("Claim")
  val claimConsID = FreshIdentifier("ClaimCons")
  val holdsID = FreshIdentifier("holds")
  val claim = mkSort(claimID)() { _ =>
    Seq((claimConsID, Seq(ValDef(holdsID, PropType()), ValDef(FreshIdentifier("n"), IntegerType()))))
  }
  val wrapID = FreshIdentifier("Wrap")
  val wrap = mkSort(wrapID)() { _ =>
    Seq((FreshIdentifier("WrapCons"), Seq(ValDef(FreshIdentifier("claim"), ADTType(claimID, Seq())))))
  }

  val idID = FreshIdentifier("id")
  val id = mkFunDef(idID)("A") { case Seq(a) => (Seq("x" :: a), a, { case Seq(x) => x }) }

  val boolean = NoSymbols.withFunctions(Seq(pos, id)).withSorts(Seq(box, claim, wrap))
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
    val pred = Lambda(Seq("y" :: IntegerType()), positive)
    typed(Untyped,
      IfExpr(positive, i, i),
      Let("p" :: BooleanType(), positive, i),
      // nor can data that holds propositions
      IfExpr(positive, Tuple(Seq(positive, i)), Tuple(Seq(positive, i))),
      // sets and bags would tell propositions apart by their equality
      FiniteSet(Seq(positive), BooleanType()),
      FiniteSet(Seq(pred), FunctionType(Seq(IntegerType()), PropType())),
      ADT(boxConsID, Seq(BooleanType()), Seq(positive)),
      ADT(boxConsID, Seq(PropType()), Seq(positive)),
      // and so would a type parameter
      FunctionInvocation(idID, Seq(BooleanType()), Seq(positive)),
      FunctionInvocation(idID, Seq(PropType()), Seq(positive)),
      FunctionInvocation(idID, Seq(pred.getType), Seq(pred)),
      // a boolean parameter can't be given a proposition
      Application(Lambda(Seq("p" :: BooleanType()), i), Seq(positive)),
      Application(Lambda(Seq("p" :: BooleanType()), IfExpr(b, i, i)), Seq(positive)))
  }

  test("Propositions are values") {
    given Symbols = propositional
    val predT = FunctionType(Seq(IntegerType()), PropType())
    val pred = Lambda(Seq("y" :: IntegerType()), positive)
    val p = "p" :: PropType()
    val q = "q" :: predT
    // predicates
    typed(predT, pred, Let(q, pred, q.toVariable))
    typed(PropType(), Application(pred, Seq(i)), Let(q, pred, Application(q.toVariable, Seq(i))))
    typed(FunctionType(Seq(IntegerType()), predT), Lambda(Seq("z" :: IntegerType()), pred))
    // parameters that are propositions
    typed(FunctionType(Seq(PropType()), IntegerType()), Lambda(Seq(p), i))
    typed(FunctionType(Seq(PropType()), PropType()), Lambda(Seq(p), Not(p.toVariable)))
    typed(IntegerType(), Application(Lambda(Seq(p), i), Seq(positive)), Application(Lambda(Seq(p), i), Seq(b)))
    typed(PropType(), Application(Lambda(Seq(p), Not(p.toVariable)), Seq(b)))
    typed(Untyped, Lambda(Seq(p), IfExpr(p.toVariable, i, i)))
    // a boolean function is a predicate
    val boolean = Lambda(Seq("y" :: IntegerType()), b)
    typed(PropType(), Application(Lambda(Seq(q), Application(q.toVariable, Seq(i))), Seq(boolean)))
    // an equality between predicates is a proposition, and so is a choice between them
    typed(PropType(), Equals(pred, pred), Equals(pred, boolean))
    typed(BooleanType(), Equals(boolean, boolean))
    typed(predT, IfExpr(positive, pred, pred))
    typed(Untyped, IfExpr(Equals(pred, pred), i, i))
    // one can't quantify over propositions or predicates
    typed(Untyped, Forall(Seq(p), p.toVariable), Forall(Seq(q), Application(q.toVariable, Seq(i))))

    // def holds(p: Prop, q: BigInt => Prop): Prop = p && q(1)
    val holdsID = FreshIdentifier("holds")
    val holds = mkFunDef(holdsID)() { _ =>
      (Seq(p, q), PropType(), { case Seq(p, q) => And(p, Application(q, Seq(i))) })
    }
    val syms = propositional.withFunctions(Seq(holds))
    syms.ensureWellFormed
    locally {
      given Symbols = syms
      typed(PropType(),
        FunctionInvocation(holdsID, Seq(), Seq(positive, pred)),
        FunctionInvocation(holdsID, Seq(), Seq(b, boolean)))
      typed(Untyped, FunctionInvocation(holdsID, Seq(), Seq(pred, pred)))
    }
  }

  test("Parameters that are given propositions are inferred") {
    // def exists(p: BigInt => Boolean): Boolean = !forall x. !p(x)
    // def nested(f): Boolean = exists(y => forall x. f(x) > y)
    // def decide(p: BigInt => Boolean): BigInt = if (p(0)) 0 else 1
    val predT = FunctionType(Seq(IntegerType()), BooleanType())
    val existsID = FreshIdentifier("exists")
    val exists = mkFunDef(existsID)() { _ =>
      (Seq("p" :: predT), BooleanType(), { case Seq(p) =>
        Not(forall("x" :: IntegerType())(x => Not(Application(p, Seq(x))))) })
    }
    def above(f: Expr): Expr =
      Lambda(Seq("y" :: IntegerType()), forall("x" :: IntegerType())(x => f(x) > E(BigInt(0))))
    val nestedID = FreshIdentifier("nested")
    val nested = mkFunDef(nestedID)() { _ =>
      (Seq("f" :: fT), BooleanType(), { case Seq(f) => FunctionInvocation(existsID, Seq(), Seq(above(f))) })
    }
    val decideID = FreshIdentifier("decide")
    val decide = mkFunDef(decideID)() { _ =>
      (Seq("p" :: predT), IntegerType(), { case Seq(p) => IfExpr(Application(p, Seq(E(BigInt(0)))), i, i) })
    }

    val inference = transformers.PropositionInference(inox.trees)
    val syms = NoSymbols.withFunctions(Seq(exists, nested, decide)).withQuantifiers(QuantifierMode.Propositional)
    val inferred = inference.transform(syms)
    inferred.ensureWellFormed
    val propT = FunctionType(Seq(IntegerType()), PropType())
    assert(inferred.getFunction(existsID).params.map(_.tpe) == Seq(propT))
    assert(inferred.getFunction(existsID).returnType == PropType())
    assert(inferred.getFunction(nestedID).returnType == PropType())
    // a parameter that isn't given a proposition stays a boolean function
    assert(inferred.getFunction(decideID) == decide)

    // def misuse(f): BigInt = decide(y => forall x. f(x) > y)
    val misuse = mkFunDef(FreshIdentifier("misuse"))() { _ =>
      (Seq("f" :: fT), IntegerType(), { case Seq(f) => FunctionInvocation(decideID, Seq(), Seq(above(f))) })
    }
    val misused = inference.transform(syms.withFunctions(Seq(misuse)))
    assert(misused.getFunction(decideID).params.map(_.tpe) == Seq(propT))
    intercept[misused.TypeErrorException](misused.ensureWellFormed)
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

  test("Sets, bags, map keys and type arguments can't hold propositions") {
    given Symbols = propositional
    val predT = FunctionType(Seq(IntegerType()), PropType())
    val claimT = ADTType(claimID, Seq())
    for (tpe <- Seq[Type](
      SetType(PropType()), BagType(PropType()), MapType(PropType(), IntegerType()),
      ADTType(boxID, Seq(PropType())), SetType(RefinementType("p" :: PropType(), b)),
      SetType(predT), ADTType(boxID, Seq(predT)), SetType(TupleType(Seq(PropType(), IntegerType()))),
      SetType(claimT), BagType(ADTType(wrapID, Seq())), MapType(claimT, IntegerType()),
      ADTType(boxID, Seq(claimT))
    )) assert(tpe.getType == Untyped, s"for $tpe")
    for (tpe <- Seq[Type](
      PropType(), predT, FunctionType(Seq(PropType()), IntegerType()),
      FunctionType(Seq(predT), predT), PiType(Seq("x" :: IntegerType()), PropType()),
      TupleType(Seq(PropType(), IntegerType())), TupleType(Seq(predT, IntegerType())),
      SigmaType(Seq("x" :: IntegerType()), PropType()), MapType(IntegerType(), PropType()),
      claimT, MapType(IntegerType(), claimT),
      // a function that takes a proposition can't depend on it, so it is data
      SetType(FunctionType(Seq(PropType()), IntegerType()))
    )) assert(tpe.getType != Untyped, s"for $tpe")
    assert(carriesProposition(predT) && carriesProposition(FunctionType(Seq(IntegerType()), predT)))
    assert(!carriesProposition(FunctionType(Seq(PropType()), IntegerType())))
    assert(!carriesProposition(claimT) && containsProposition(claimT))
    assert(containsProposition(ADTType(wrapID, Seq())) && containsProposition(TupleType(Seq(i.getType, predT))))
    assert(!containsProposition(FunctionType(Seq(PropType()), IntegerType())))
    assert(!containsProposition(ADTType(boxID, Seq(IntegerType()))))
  }

  test("Data can hold propositions") {
    given Symbols = propositional
    val claimT = ADTType(claimID, Seq())
    val c = ADT(claimConsID, Seq(), Seq(positive, i))
    val pair = Tuple(Seq(positive, i))
    typed(claimT, c, ADT(claimConsID, Seq(), Seq(b, i)))
    typed(PropType(), ADTSelector(c, holdsID), TupleSelect(pair, 1))
    typed(TupleType(Seq(PropType(), IntegerType())), pair)
    assert(summon[Symbols].isSubtypeOf(Tuple(Seq(b, i)).getType, pair.getType))
    typed(IntegerType(), TupleSelect(pair, 2))
    // equality would observe the propositions, so it is a proposition
    typed(PropType(),
      Equals(c, ADT(claimConsID, Seq(), Seq(b, i))),
      Equals(pair, Tuple(Seq(b, i))),
      Equals(FiniteMap(Seq(), positive, IntegerType(), PropType()), FiniteMap(Seq(), b, IntegerType(), PropType())))
    typed(Untyped, IfExpr(Equals(c, c), i, i), IfExpr(Equals(pair, pair), i, i))
    // but not the equality of the data in it
    typed(BooleanType(), Equals(TupleSelect(pair, 2), i))
    // a term can't choose between data that holds propositions
    typed(Untyped, IfExpr(positive, c, c))
    // nor quantify over it
    typed(Untyped, Forall(Seq("c" :: claimT), b))
    propositional.ensureWellFormed
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
    // also as the results of functions
    val boolT = FunctionType(Seq(IntegerType()), BooleanType())
    val predT = FunctionType(Seq(IntegerType()), PropType())
    assert(isSubtypeOf(boolT, predT) && !isSubtypeOf(predT, boolT))
    assert(isSubtypeOf(FunctionType(Seq(predT), boolT), FunctionType(Seq(boolT), predT)))
    assert(!isSubtypeOf(FunctionType(Seq(boolT), boolT), FunctionType(Seq(predT), predT)))
    assert(!isSubtypeOf(FunctionType(Seq(BooleanType()), IntegerType()), FunctionType(Seq(PropType()), IntegerType())))
  }

  test("Propositions can be parameters and fields") {
    val param = mkFunDef(FreshIdentifier("param"))() { _ =>
      (Seq("p" :: PropType()), PropType(), { case Seq(p) => p })
    }
    NoSymbols.withFunctions(Seq(param)).ensureWellFormed
    NoSymbols.withSorts(Seq(claim, wrap)).ensureWellFormed
  }

  test("Fields and tuples that are given propositions are inferred") {
    // case class Pos(holds: Boolean, at: BigInt)
    // def mk(f): Pos = Pos(forall x. f(x) > 0, 0)
    // def pair(f): (Boolean, BigInt) = (forall x. f(x) > 0, 0)
    // def boxed(f): Box[Boolean] = Box(forall x. f(x) > 0)
    val posSortID = FreshIdentifier("Pos")
    val posConsID = FreshIdentifier("PosCons")
    val posHoldsID = FreshIdentifier("holds")
    val posSort = mkSort(posSortID)() { _ =>
      Seq((posConsID, Seq(ValDef(posHoldsID, BooleanType()), ValDef(FreshIdentifier("at"), IntegerType()))))
    }
    val zero = E(BigInt(0))
    def stated(f: Expr) = forall("x" :: IntegerType())(x => f(x) > zero)
    val mkID = FreshIdentifier("mk")
    val mk = mkFunDef(mkID)() { _ =>
      (Seq("f" :: fT), ADTType(posSortID, Seq()), { case Seq(f) => ADT(posConsID, Seq(), Seq(stated(f), zero)) })
    }
    val pairID = FreshIdentifier("pair")
    val pair = mkFunDef(pairID)() { _ =>
      (Seq("f" :: fT), TupleType(Seq(BooleanType(), IntegerType())), { case Seq(f) => Tuple(Seq(stated(f), zero)) })
    }
    val boxedID = FreshIdentifier("boxed")
    val boxed = mkFunDef(boxedID)() { _ =>
      (Seq("f" :: fT), ADTType(boxID, Seq(BooleanType())), { case Seq(f) =>
        ADT(boxConsID, Seq(BooleanType()), Seq(stated(f))) })
    }

    val inference = transformers.PropositionInference(inox.trees)
    val syms = NoSymbols.withSorts(Seq(posSort, box)).withFunctions(Seq(mk, pair))
      .withQuantifiers(QuantifierMode.Propositional)
    val inferred = inference.transform(syms)
    inferred.ensureWellFormed
    assert(inferred.getSort(posSortID).constructors.head.fields.map(_.tpe) == Seq(PropType(), IntegerType()))
    assert(inferred.getFunction(pairID).returnType == TupleType(Seq(PropType(), IntegerType())))
    assert(containsProposition(ADTType(posSortID, Seq()))(using inferred))
    assert(!containsProposition(ADTType(posSortID, Seq()))(using syms))

    // a generic field would make the proposition a type argument
    val generic = inference.transform(syms.withFunctions(Seq(boxed)))
    assert(generic.getSort(boxID) == box)
    intercept[generic.TypeErrorException](generic.ensureWellFormed)
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
