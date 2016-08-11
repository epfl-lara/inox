/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package regression

import solvers._

class SimpleQuantifiersSuite extends SolvingTestSuite {
  import inox.trees._
  import dsl._

  val isAssociativeID = FreshIdentifier("isAssociative")
  val isAssociative = mkFunDef(isAssociativeID)("A") { case Seq(aT) => (
    Seq("f" :: (T(aT, aT) =>: aT)), BooleanType, { case Seq(f) =>
      forall("x" :: aT, "y" :: aT, "z" :: aT)((x,y,z) => f(f(x,y),z) === f(x,f(y,z)))
    })
  }

  val isCommutativeID = FreshIdentifier("isCommutative")
  val isCommutative = mkFunDef(isCommutativeID)("A") { case Seq(aT) => (
    Seq("f" :: (T(aT, aT) =>: aT)), BooleanType, { case Seq(f) =>
      forall("x" :: aT, "y" :: aT)((x,y) => f(x,y) === f(y,x))
    })
  }

  val isRotateID = FreshIdentifier("isRotate")
  val isRotate = mkFunDef(isRotateID)("A") { case Seq(aT) => (
    Seq("f" :: (T(aT, aT) =>: aT)), BooleanType, { case Seq(f) =>
      forall("x" :: aT, "y" :: aT, "z" :: aT)((x,y,z) => f(f(x,y),z) === f(f(y,z),x))
    })
  }

  val symbols = new Symbols(Map(
    isAssociativeID -> isAssociative,
    isCommutativeID -> isCommutative,
    isRotateID      -> isRotate
  ), Map.empty)

  test("Pair of associative ==> associative pair") { ctx => 
    val program = InoxProgram(ctx, symbols)

    val (aT,bT) = (T("A"), T("B"))
    val Seq(f1,f2) = Seq("f1" :: (T(aT, aT) =>: aT), "f2" :: (T(bT, bT) =>: bT)).map(_.toVariable)
    val clause = isAssociative(aT)(f1) && isAssociative(bT)(f2) && !isAssociative(T(aT,bT)) {
      \("p1" :: T(aT,bT), "p2" :: T(aT, bT))((p1,p2) => E(f1(p1._1,p2._1), f2(p1._2,p2._2)))
    }

    val sf = SolverFactory.default(program)
    val api = SimpleSolverAPI(sf)
    api.solveVALID(clause) should be (Some(false))
  }

  test("Commutative and rotate ==> associative") { ctx =>
    val program = InoxProgram(ctx, symbols)

    val aT = T("A")
    val f = ("f" :: (T(aT, aT) =>: aT)).toVariable
    val clause = isCommutative(aT)(f) && isRotate(aT)(f) && !isAssociative(aT)(f)

    val sf = SolverFactory.default(program)
    val api = SimpleSolverAPI(sf)
    api.solveVALID(clause) should be (Some(false))
  }

  test("Commutative and rotate ==> associative (integer type)") { ctx =>
    val program = InoxProgram(ctx, symbols)

    val f = ("f" :: (T(IntegerType, IntegerType) =>: IntegerType)).toVariable
    val clause = isCommutative(IntegerType)(f) && isRotate(IntegerType)(f) && !isAssociative(IntegerType)(f)

    val sf = SolverFactory.default(program)
    val api = SimpleSolverAPI(sf)
    api.solveVALID(clause) should be (Some(false))
  }

  test("Associatve =!=> commutative") { ctx =>
    val program = InoxProgram(ctx, symbols)

    val aT = T("A")
    val f = ("f" :: (T(aT, aT) =>: aT)).toVariable
    val clause = isAssociative(aT)(f) && !isCommutative(aT)(f)

    val sf = SolverFactory.default(program)
    val api = SimpleSolverAPI(sf)
    api.solveVALID(clause) should be (Some(true))
  }

  test("Commutative =!=> associative") { ctx =>
    val program = InoxProgram(ctx, symbols)

    val aT = T("A")
    val f = ("f" :: (T(aT, aT) =>: aT)).toVariable
    val clause = isCommutative(aT)(f) && !isAssociative(aT)(f)

    val sf = SolverFactory.default(program)
    val api = SimpleSolverAPI(sf)
    api.solveVALID(clause) should be (Some(true))
  }
}
