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

  override protected def symbols: Symbols = NoSymbols
  given Symbols = symbols

  private val tp = TypeParameter.fresh("T")

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

  test("generic properties are still proven", TypeParameters, Quantifiers) { ctx =>
    val s = solver(ctx)
    val res = s.solveSAT(Not(forall("x" :: tp, "z" :: tp)((x, z) => (x === z) ==> (z === x))))
    assert(res.isUNSAT, s"expected UNSAT, got $res")
  }
}
