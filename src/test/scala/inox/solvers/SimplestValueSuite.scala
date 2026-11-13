/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import Feature._

import scala.concurrent.{Await, Future, TimeoutException}
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration._

/** Checks that `simplestValue` terminates on sorts with invariants, which it solves for. */
class SimplestValueSuite extends SolverTestSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl.{given, _}

  // case class Box(f: BigInt => Boolean) { require(forall((x: BigInt) => f(x))) }
  val boxID = FreshIdentifier("Box")
  val boxConsID = FreshIdentifier("Box")
  val boxF = FreshIdentifier("f")
  val boxInvID = FreshIdentifier("boxInv")
  val boxInv = mkFunDef(boxInvID)() { _ => (
    Seq("b" :: T(boxID)()), BooleanType(), { case Seq(b) =>
      forall("x" :: IntegerType())(x => b.getField(boxF)(x))
    })
  }
  val boxSort = mkSort(boxID, HasADTInvariant(boxInvID))() { _ =>
    Seq((boxConsID, Seq(ValDef(boxF, IntegerType() =>: BooleanType()))))
  }

  // sealed abstract class Forest { require(this.isInstanceOf[Cons]) }
  // case class Cons(head: BigInt, tail: Forest) extends Forest
  // case class Leaf(t: BigInt) extends Forest
  //
  // The invariant only holds for infinite forests, as in Stainless's ForestNothing2.
  val forestID = FreshIdentifier("Forest")
  val consID = FreshIdentifier("Cons")
  val leafID = FreshIdentifier("Leaf")
  val forestInvID = FreshIdentifier("forestInv")
  val forestInv = mkFunDef(forestInvID)() { _ => (
    Seq("f" :: T(forestID)()), BooleanType(), { case Seq(f) => f.is(consID) })
  }
  val forestSort = mkSort(forestID, HasADTInvariant(forestInvID))() { _ => Seq(
    (consID, Seq("head" :: IntegerType(), "tail" :: T(forestID)())),
    (leafID, Seq("t" :: IntegerType()))
  )}

  // sealed abstract class Nat
  // case class Succ(pred: Nat) extends Nat
  // case object Zero extends Nat
  // case class Deep(n: Nat) { require(depth(n) >= 3) }
  //
  // The simplest value of Deep holds a Nat three successors deep, which the solver finds by unrolling `depth`.
  val natID = FreshIdentifier("Nat")
  val succID = FreshIdentifier("Succ")
  val zeroID = FreshIdentifier("Zero")
  val predID = FreshIdentifier("pred")
  val natSort = mkSort(natID)() { _ => Seq(
    (succID, Seq(ValDef(predID, T(natID)()))),
    (zeroID, Seq())
  )}
  val depthID = FreshIdentifier("depth")
  val depth = mkFunDef(depthID)() { _ => (
    Seq("n" :: T(natID)()), IntegerType(), { case Seq(n) =>
      if_ (n.is(succID)) { E(BigInt(1)) + E(depthID)(n.getField(predID)) } else_ { E(BigInt(0)) }
    })
  }
  val deepID = FreshIdentifier("Deep")
  val deepConsID = FreshIdentifier("Deep")
  val deepN = FreshIdentifier("n")
  val deepInvID = FreshIdentifier("deepInv")
  val deepInv = mkFunDef(deepInvID)() { _ => (
    Seq("d" :: T(deepID)()), BooleanType(), { case Seq(d) => E(depthID)(d.getField(deepN)) >= E(BigInt(3)) })
  }
  val deepSort = mkSort(deepID, HasADTInvariant(deepInvID))() { _ => Seq(
    (deepConsID, Seq(ValDef(deepN, T(natID)())))
  )}

  override protected def symbols: Symbols = NoSymbols
    .withFunctions(Seq(boxInv, forestInv, depth, deepInv))
    .withSorts(Seq(boxSort, forestSort, natSort, deepSort))

  test("Simplest value of a sort whose invariant constrains a function", Integers, Functions, Quantifiers) { ctx =>
    given Context = ctx
    given program.Semantics = program.getSemantics
    // Extracting the model of the solver that looks for a value may itself need a value of the
    // sort, which used to start another solver, and so on without end
    try {
      val v = program.symbols.simplestValue(T(boxID)())
      assert(v.getType(using program.symbols) == T(boxID)())
    } catch {
      case _: program.symbols.NoSimpleValue => // a sound answer when no value is found
    }
  }

  test("No simplest value of a sort whose invariant only holds for infinite values", Integers) { ctx =>
    given Context = ctx
    given program.Semantics = program.getSemantics
    // The solver that looks for a value used to unroll forever. The search is bounded, so it ends
    // in seconds, but it can take ten times longer when the other suites load the machine: the
    // deadline only has to tell a slow search from one that doesn't end.
    val result = Future(scala.util.Try(program.symbols.simplestValue(T(forestID)())))
    try {
      Await.result(result, 5.minutes) match {
        case scala.util.Failure(_: program.symbols.NoSimpleValue) =>
        case res => fail(s"Expected no simple value, got $res")
      }
    } catch {
      case _: TimeoutException =>
        ctx.interruptManager.interrupt()
        fail("The search for a simplest value did not end")
    }
  }

  test("Simplest value of a sort whose invariant needs unrolling", Integers) { ctx =>
    given Context = ctx
    given program.Semantics = program.getSemantics
    val v = program.symbols.simplestValue(T(deepID)())
    assert(v.getType(using program.symbols) == T(deepID)())
  }
}
