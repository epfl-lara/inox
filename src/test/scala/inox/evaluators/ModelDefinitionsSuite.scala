/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package evaluators

import org.scalatest.funsuite.AnyFunSuite

/** Models whose values call functions that only the model defines. */
class ModelDefinitionsSuite extends AnyFunSuite {
  import inox.trees._
  import inox.trees.dsl._

  given ctx: Context = TestContext.empty
  val program = InoxProgram(NoSymbols)
  def eval(p: Program { val trees: inox.trees.type })(e: Expr, m: p.Model): EvaluationResults.Result[Expr] = {
    p.getSemantics.withFunctions(m.functions).getEvaluator.eval(e, m)
  }

  // def f(x: BigInt): BigInt = if (x == 1) 2 else if (x == 2) 3 else error
  val f = mkFunDef(FreshIdentifier("f"), ModelFunction)()(_ => (
    Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) =>
      if_ (x === E(BigInt(1))) {
        E(BigInt(2))
      } else_ {
        if_ (x === E(BigInt(2))) {
          E(BigInt(3))
        } else_ {
          Error(IntegerType(), "unconstrained by the model")
        }
      }
    }))

  // def g(): BigInt = 5
  val g = mkFunDef(FreshIdentifier("g"), ModelFunction)()(_ => (Seq(), IntegerType(), { case Seq() => E(BigInt(5)) }))

  val fv = Variable.fresh("fv", FunctionType(Seq(IntegerType()), IntegerType()))
  val gv = Variable.fresh("gv", FunctionType(Seq(), IntegerType()))

  val x = ValDef.fresh("x", IntegerType())
  val model = inox.Model(program)(
    Map(
      fv.toVal -> Lambda(Seq(x), FunctionInvocation(f.id, Seq(), Seq(x.toVariable))),
      gv.toVal -> Lambda(Seq(), FunctionInvocation(g.id, Seq(), Seq()))
    ),
    Map.empty,
    Seq(f, g)
  )

  test("model symbols include the definitions") {
    assert(model.symbols.lookupFunction(f.id) == Some(f))
    assert(model.symbols.lookupFunction(g.id) == Some(g))
    assert(program.symbols.lookupFunction(f.id).isEmpty)
    assert(!model.isEmpty)
  }

  test("values call the model's definitions") {
    assert(eval(program)(Application(fv, Seq(IntegerLiteral(1))), model).result == Some(IntegerLiteral(2)))
    assert(eval(program)(Application(fv, Seq(IntegerLiteral(2))), model).result == Some(IntegerLiteral(3)))
    assert(eval(program)(Application(gv, Seq()), model).result == Some(IntegerLiteral(5)))
  }

  test("formulas over the model's values") {
    val formula = Application(fv, Seq(Application(fv, Seq(IntegerLiteral(1))))) === IntegerLiteral(3) &&
      Application(gv, Seq()) > IntegerLiteral(4)
    assert(eval(program)(formula, model).result == Some(BooleanLiteral(true)))
  }

  test("the error default fails evaluation") {
    val res = eval(program)(Application(fv, Seq(IntegerLiteral(3))), model)
    assert(res.isInstanceOf[EvaluationResults.RuntimeError], res)
  }

  test("nullary closures that call definitions are kept") {
    // `() => g()` must not be evaluated to `() => 5`: the definition, not its result, identifies the closure
    val closure = Lambda(Seq(), FunctionInvocation(g.id, Seq(), Seq()))
    assert(eval(program)(gv, model).result == Some(closure))
    val res = eval(program)(closure, model).result
    assert(res == Some(closure), res)
  }

  test("encoded models keep their definitions") {
    val encoder = transformers.ProgramEncoder.empty(program)
    val encoded = model.encode(encoder)
    assert(encoded.functions == Seq(f, g))
    val res = eval(encoder.targetProgram)(Application(fv, Seq(IntegerLiteral(2))), encoded).result
    assert(res == Some(IntegerLiteral(3)))
  }

  test("models print their definitions") {
    val str = model.asString(using PrinterOptions(symbols = Some(model.symbols)))
    assert(str.contains(f.id.asString(using PrinterOptions())), str)
    assert(str.contains(g.id.asString(using PrinterOptions())), str)
  }
}
