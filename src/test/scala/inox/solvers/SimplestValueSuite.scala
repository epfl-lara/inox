/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import Feature._

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

  override protected def symbols: Symbols = NoSymbols.withFunctions(Seq(boxInv)).withSorts(Seq(boxSort))

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
}
