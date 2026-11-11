/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package ast

import org.scalatest.funsuite.AnyFunSuite

/** Operations of [[SymbolOps]] that the solvers and the simplifier don't reach. */
class SymbolOpsSuite extends AnyFunSuite with DatastructureUtils {
  import inox.trees._
  import inox.trees.dsl._

  val fid = FreshIdentifier("inc")
  val p = ValDef.fresh("p", IntegerType())
  val inc = new FunDef(fid, Seq(), Seq(p), IntegerType(), Plus(p.toVariable, IntegerLiteral(1)), Seq())
  val badId = FreshIdentifier("bad")
  val bad = new FunDef(badId, Seq(), Seq(p), IntegerType(), Division(IntegerLiteral(1), p.toVariable), Seq())

  given symbols: Symbols = baseSymbols.withFunctions(Seq(inc, bad))
  import symbols._

  val x = Variable.fresh("x", IntegerType())
  val b = Variable.fresh("b", BooleanType())
  given PrinterOptions = PrinterOptions(symbols = Some(symbols))

  test("Interpretations used by an expression") {
    val y = ValDef.fresh("y", IntegerType())
    def call(id: Identifier, arg: Expr) = UninterpretedCall(id, Seq(), Seq(arg), PiType(Seq(y), IntegerType()))
    val f = FreshIdentifier("f")
    val g = FreshIdentifier("g")
    val h = FreshIdentifier("h")
    // f calls g in its interpretation, and h isn't called
    val interpretations = Map(
      (f, Seq.empty[Type]) -> Lambda(Seq(y), call(g, y.toVariable)),
      (g, Seq.empty[Type]) -> Lambda(Seq(y), y.toVariable),
      (h, Seq.empty[Type]) -> Lambda(Seq(y), y.toVariable))
    assert(interpretationsUsedBy(call(f, x), interpretations).keySet == Set(f -> Seq(), g -> Seq()))
    assert(interpretationsUsedBy(FunctionInvocation(fid, Seq(), Seq(x)), interpretations).isEmpty)
    assert(interpretationsUsedBy(call(h, x), Map.empty).isEmpty)
  }

  test("Transformations and searches with path conditions") {
    val e = IfExpr(b, Plus(x, IntegerLiteral(1)), x)
    val swapped = transformWithOps(e)(
      (e, path, op) => e match {
        case IntegerLiteral(i) if path.conditions == Seq(b) => IntegerLiteral(i + 1)
        case _ => op.sup(e, path)
      },
      (tpe, path, op) => op.sup(tpe, path))
    assert(swapped == IfExpr(b, Plus(x, IntegerLiteral(2)), x))

    val replaced = transformWithPC(e, Path.empty) { (e, path, op) =>
      if (e == x && path.conditions.nonEmpty) IntegerLiteral(0) else op.sup(e, path)
    }
    assert(replaced == IfExpr(b, Plus(IntegerLiteral(0), IntegerLiteral(1)), IntegerLiteral(0)))
    assert(transformWithPC(e)((e, path, op) => op.sup(e, path)) == e)

    assert(existsWithPC(e, Path.empty)((e, path) => e == x && path.conditions == Seq(Not(b))))
    assert(!existsWithPC(e, Path.empty)((e, path) => e == x && path.conditions.isEmpty))
  }

  test("Simplifications by constructors") {
    val l = Variable.fresh("l", T(listID)(IntegerType()))
    val cons = ADT(consID, Seq(IntegerType()), Seq(x, ADT(nilID, Seq(IntegerType()), Seq())))
    assert(simplifyByConstructors(UMinus(IntegerLiteral(-2))) == IntegerLiteral(2))
    assert(simplifyByConstructors(ADTSelector(cons, head)) == x)
    assert(simplifyByConstructors(IsConstructor(cons, consID)) == isCons(cons, consID))
    assert(simplifyByConstructors(Implies(BooleanLiteral(false), b)) == BooleanLiteral(true))
    assert(simplifyByConstructors(Plus(IntegerLiteral(0), x)) == x)
    assert(simplifyByConstructors(Minus(x, IntegerLiteral(0))) == x)
    assert(simplifyByConstructors(Times(IntegerLiteral(1), x)) == x)
    val y = ValDef.fresh("y", IntegerType())
    assert(simplifyByConstructors(Application(Lambda(Seq(y), y.toVariable), Seq(x))) == x)
    assert(simplifyByConstructors(ADTSelector(l, head)) == ADTSelector(l, head))
  }

  test("Applications of assumed lambdas and tuple selections") {
    val y = ValDef.fresh("y", IntegerType())
    assert(application(Assume(b, Lambda(Seq(y), y.toVariable)), Seq(x)) == Assume(b, x))
    assert(tupleSelect(Tuple(Seq(x, b)), 2, 2) == b)
    assert(tupleSelect(x, 1, 1) == x)
    intercept[RuntimeException](tupleSelect(x, 2, true))
  }

  test("Inlining uninterpreted calls") {
    val uid = FreshIdentifier("u")
    val y = ValDef.fresh("y", IntegerType())
    val call = UninterpretedCall(uid, Seq(), Seq(x), IntegerType())
    val inlined = inlineUninterpreted(Plus(call, IntegerLiteral(1)),
      Map((uid, Seq()) -> Lambda(Seq(y), Times(y.toVariable, IntegerLiteral(2)))))
    inlined match {
      case Plus(Let(vd, `x`, Times(v, IntegerLiteral(two))), IntegerLiteral(one)) =>
        assert(v == vd.toVariable && two == 2 && one == 1)
      case e => fail(s"Unexpected inlining $e")
    }
    assert(inlineUninterpreted(call, Map.empty) == call)
  }

  test("Explanations of typing errors") {
    val badCall = FunctionInvocation(fid, Seq(), Seq(BooleanLiteral(true)))
    assert(explainTyping(badCall).contains("because inc was instantiated with"))
    val unknownCall = FunctionInvocation(FreshIdentifier("unknown"), Seq(), Seq(x))
    assert(explainTyping(unknownCall).contains("is of type"))
    val badCons = ADT(consID, Seq(IntegerType()), Seq(BooleanLiteral(true), ADT(nilID, Seq(IntegerType()), Seq())))
    assert(explainTyping(badCons).contains("because Cons was instantiated with"))
    val unknownCons = ADT(FreshIdentifier("Unknown"), Seq(), Seq())
    assert(explainTyping(unknownCons).contains("is of type"))
    assert(explainTyping(Plus(x, b)).contains("is of type"))
  }

  test("Ground simplifications") {
    val reporter = new TestSilentReporter
    given ctx: Context = Context(reporter, new utils.InterruptManager(reporter), Options.empty)
    given sem: symbols.Semantics = InoxProgram(symbols).getSemantics.asInstanceOf[symbols.Semantics]
    val e = Plus(FunctionInvocation(badId, Seq(), Seq(IntegerLiteral(0))), x)
    assert(simplifyGround(e, reportErrors = true) == e)
    assert(simplifyGround(Plus(FunctionInvocation(fid, Seq(), Seq(IntegerLiteral(1))), x)) == Plus(IntegerLiteral(2), x))
  }
}
