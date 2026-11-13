/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers

import Feature._

/** Type parameters may be instantiated with empty types (Voirol, EPFL thesis 9479, Chapter 3),
  * so the unrolling solver must not prove that a type parameter is inhabited.
  */
class EmptyTypeParameterSuite extends SolverTestSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl.{given, _}
  import SolverResponses.{given, _}

  override protected def symbols: Symbols = NoSymbols.withSorts(Seq(listSort))
  given Symbols = symbols

  private val tp = TypeParameter.fresh("T")

  private lazy val listID = FreshIdentifier("List")
  private lazy val consID = FreshIdentifier("Cons")
  private lazy val nilID = FreshIdentifier("Nil")
  private lazy val head = FreshIdentifier("head")
  private lazy val tail = FreshIdentifier("tail")
  private lazy val listSort = mkSort(listID)("A") { case Seq(a) => Seq(
    (consID, Seq(ValDef(head, a), ValDef(tail, T(listID)(a)))),
    (nilID, Seq())
  )}

  private val xs = Variable.fresh("xs", T(listID)(tp))
  // `xs` holds a value of type T, two constructors deep
  private val holdsValue = IsConstructor(xs, consID) && IsConstructor(xs.getField(tail), consID)
  private val empty = forall("x" :: tp)(_ => E(false))

  private def withSolver(ctx: Context)(body: Solver { val program: InoxProgram } => Unit): Unit = {
    val factory = program.getSolver(ctx)
    val s = factory.getNewSolver()
    try body(s) finally factory.reclaim(s)
  }

  test("type parameters are not proven inhabited", TypeParameters, Quantifiers) { ctx =>
    val s = solver(ctx)
    // Satisfiable when T is empty
    val res = s.solveSAT(forall("x" :: tp)(_ => E(false)))
    assert(!res.isUNSAT, s"expected SAT or unknown, got $res")
  }

  test("inhabited type parameters are still refuted", TypeParameters, Quantifiers) { ctx =>
    val s = solver(ctx)
    val y = Variable.fresh("y", tp)
    val res = s.solveSAT(Equals(y, y) && forall("x" :: tp)(_ => E(false)))
    assert(res.isUNSAT, s"expected UNSAT, got $res")
  }

  test("free values hold no value of an empty type parameter", TypeParameters, Quantifiers) { ctx =>
    val s = solver(ctx)
    val res = s.solveSAT(holdsValue && empty)
    assert(res.isUNSAT, s"expected UNSAT, got $res")
  }

  test("free values without values of an empty type parameter remain", TypeParameters, Quantifiers) { ctx =>
    val s = solver(ctx)
    val res = s.solveSAT(IsConstructor(xs, nilID) && empty)
    assert(!res.isUNSAT, s"expected SAT or unknown, got $res")
  }

  test("free values are checked once their type parameter may be empty", TypeParameters, Quantifiers) { ctx =>
    withSolver(ctx) { s =>
      // nothing lets T be empty yet, so `xs` isn't unrolled down to its values of type T
      s.assertCnstr(holdsValue)
      assert(s.check(Simple).isSAT)
      s.push()
      s.assertCnstr(empty)
      assert(s.check(Simple).isUNSAT)
      s.pop()
      assert(s.check(Simple).isSAT)
      s.assertCnstr(empty)
      assert(s.check(Simple).isUNSAT)
    }
  }

  test("free values of a type parameter are checked once it may be empty", TypeParameters, Quantifiers) { ctx =>
    withSolver(ctx) { s =>
      val y = Variable.fresh("y", tp)
      s.assertCnstr(Equals(y, y))
      assert(s.check(Simple).isSAT)
      s.assertCnstr(empty)
      assert(s.check(Simple).isUNSAT)
    }
  }

  test("generic properties are still proven", TypeParameters, Quantifiers) { ctx =>
    val s = solver(ctx)
    val res = s.solveSAT(Not(forall("x" :: tp, "z" :: tp)((x, z) => (x === z) ==> (z === x))))
    assert(res.isUNSAT, s"expected UNSAT, got $res")
  }
}
