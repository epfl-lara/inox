/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package ast

import org.scalatest.funsuite.AnyFunSuite

/** The type of an uninterpreted call is the result type of its function, with the parameters of the
  * function bound to the arguments of the call. */
class UninterpretedCallTypingSuite extends AnyFunSuite {
  import inox.trees.{given, _}
  import dsl._

  val symbols = NoSymbols
  given Symbols = symbols
  import symbols._

  val f = FreshIdentifier("f")
  val x = Variable.fresh("x", IntegerType())
  val y = Variable.fresh("y", IntegerType())

  /** `(p: Int) => {r: Int | r > p}` */
  val greaterT = {
    val p = ValDef.fresh("p", IntegerType())
    val r = ValDef.fresh("r", IntegerType())
    (p, r, PiType(Seq(p), RefinementType(r, r.toVariable > p.toVariable)))
  }

  test("the result type binds the parameters to variable arguments") {
    val (_, r, pi) = greaterT
    val call = UninterpretedCall(f, Seq(), Seq(x), pi)
    assert(call.getType == IntegerType())
    assert(call.getTpe(stripRefinements = false) == RefinementType(r, r.toVariable > x))
  }

  test("the result type binds the parameters to arguments that aren't variables") {
    val (_, r, pi) = greaterT
    val arg = x + E(BigInt(1))
    val call = UninterpretedCall(f, Seq(), Seq(arg), pi)
    assert(call.getType == IntegerType())
    assert(call.getTpe(stripRefinements = false) == RefinementType(r, r.toVariable > arg))
  }

  test("calls to the same function with distinct arguments have distinct refinements") {
    val (_, r, pi) = greaterT
    val c1 = UninterpretedCall(f, Seq(), Seq(x), pi)
    val c2 = UninterpretedCall(f, Seq(), Seq(y), pi)
    assert(c1.getTpe(stripRefinements = false) == RefinementType(r, r.toVariable > x))
    assert(c2.getTpe(stripRefinements = false) == RefinementType(r, r.toVariable > y))
  }

  test("the result type may depend on several parameters") {
    val a = ValDef.fresh("a", IntegerType())
    val b = ValDef.fresh("b", IntegerType())
    val r = ValDef.fresh("r", IntegerType())
    val pi = PiType(Seq(a, b), RefinementType(r, r.toVariable > a.toVariable + b.toVariable))
    val call = UninterpretedCall(f, Seq(), Seq(x, E(BigInt(2))), pi)
    assert(call.getTpe(stripRefinements = false) == RefinementType(r, r.toVariable > x + E(BigInt(2))))
  }

  test("parameter types may depend on earlier parameters") {
    val a = ValDef.fresh("a", IntegerType())
    val v = ValDef.fresh("v", IntegerType())
    val b = "b" :: RefinementType(v, v.toVariable > a.toVariable)
    val r = ValDef.fresh("r", IntegerType())
    val pi = PiType(Seq(a, b), RefinementType(r, r.toVariable > b.toVariable))
    val call = UninterpretedCall(f, Seq(), Seq(x, y), pi)
    assert(call.getType == IntegerType())
    assert(call.getTpe(stripRefinements = false) == RefinementType(r, r.toVariable > y))
  }

  test("calls with a function type have its result type") {
    val v = ValDef.fresh("v", IntegerType())
    val positive = RefinementType(v, v.toVariable > E(BigInt(0)))
    val call = UninterpretedCall(f, Seq(), Seq(x), FunctionType(Seq(IntegerType()), positive))
    assert(call.getType == IntegerType())
    assert(call.getTpe(stripRefinements = false) == positive)
    val nullary = UninterpretedCall(f, Seq(), Seq(), FunctionType(Seq(), positive))
    assert(nullary.getType == IntegerType())
    assert(nullary.getTpe(stripRefinements = false) == positive)
  }

  test("calls whose arguments don't match the parameters are untyped") {
    val (_, _, pi) = greaterT
    assert(UninterpretedCall(f, Seq(), Seq(), pi).getType == Untyped)
    assert(UninterpretedCall(f, Seq(), Seq(x, y), pi).getType == Untyped)
    assert(UninterpretedCall(f, Seq(), Seq(E(true)), pi).getType == Untyped)
    assert(UninterpretedCall(f, Seq(), Seq(E(true)), FunctionType(Seq(IntegerType()), IntegerType())).getType == Untyped)
  }

  test("arguments of subtypes of the parameter types are accepted") {
    val (_, r, pi) = greaterT
    val v = ValDef.fresh("v", IntegerType())
    val z = Variable.fresh("z", RefinementType(v, v.toVariable > E(BigInt(0))))
    val call = UninterpretedCall(f, Seq(), Seq(z), pi)
    assert(call.getType == IntegerType())
    assert(call.getTpe(stripRefinements = false) == RefinementType(r, r.toVariable > z))
  }

  test("calls whose type isn't a function type are untyped") {
    assert(UninterpretedCall(f, Seq(), Seq(x), IntegerType()).getType == Untyped)
    assert(UninterpretedCall(f, Seq(), Seq(), IntegerType()).getType == Untyped)
  }

  test("instantiating the type parameters instantiates the function type") {
    val tp = TypeParameter.fresh("T")
    val p = ValDef.fresh("p", tp)
    val r = ValDef.fresh("r", tp)
    val pi = PiType(Seq(p), RefinementType(r, r.toVariable === p.toVariable))
    val a = Variable.fresh("a", tp)
    val call = UninterpretedCall(f, Seq(tp), Seq(a), pi)
    assert(call.getType == tp)

    val inst = typeOps.instantiateType(UninterpretedCall(f, Seq(tp), Seq(x), pi), Map(tp -> IntegerType()))
      .asInstanceOf[UninterpretedCall]
    assert(inst.tps == Seq(IntegerType()))
    assert(inst.getType == IntegerType())
    val RefinementType(ir, pred) = inst.getTpe(stripRefinements = false): @unchecked
    assert(ir.getType == IntegerType())
    assert(pred == (ir.toVariable === x))
  }

  test("deconstructing and rebuilding a call keeps its function type") {
    val (_, _, pi) = greaterT
    val call = UninterpretedCall(f, Seq(), Seq(x + E(BigInt(1))), pi)
    val Operator(es, recons) = call: @unchecked
    assert(recons(es) == call)
    val (ids, vs, args, tps, flags, builder) = deconstructor.deconstruct(call)
    assert(builder(ids, vs, args, tps, flags) == call)
  }

  test("calls are pure when their result type has values") {
    val (_, _, pi) = greaterT
    // Whether a type refined over the arguments has values isn't known
    assert(isImpureExpr(UninterpretedCall(f, Seq(), Seq(x), pi)))
    assert(!isImpureExpr(UninterpretedCall(f, Seq(), Seq(x), FunctionType(Seq(IntegerType()), IntegerType()))))
    val v = ValDef.fresh("v", IntegerType())
    val empty = RefinementType(v, E(false))
    assert(isImpureExpr(UninterpretedCall(f, Seq(), Seq(x), FunctionType(Seq(IntegerType()), empty))))
  }

  test("calls are printed like function invocations") {
    val (_, _, pi) = greaterT
    val opts = PrinterOptions(printUniqueIds = false)
    val tp = TypeParameter.fresh("T")
    for ((tps, args) <- Seq((Seq(), Seq(x)), (Seq(tp), Seq(x, y)), (Seq(), Seq()))) {
      assert(UninterpretedCall(f, tps, args, pi).asString(using opts) == FunctionInvocation(f, tps, args).asString(using opts))
    }
  }
}
