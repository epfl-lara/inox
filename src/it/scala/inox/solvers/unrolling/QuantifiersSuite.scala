/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

class QuantifiersSuite extends TestSuite {
  import inox.trees.{forall => _, _}
  import dsl._

  override def configurations = List(
    ("nativez3",     false, false, false),
    ("nativez3-opt", false, false, false),
    ("princess",     false, false, false),
    ("smt-z3",       false, false, false),
    ("smt-z3-opt",   false, false, false),
    ("smt-cvc4",     false, false, false),
    ("nativez3",     true,  true,  false),
    ("nativez3",     false, false, true ),
    ("princess",     true,  true,  false),
    ("smt-cvc4",     false, false, true )
  ).map { case (solverName, checkModels, feelingLucky, unrollAssumptions) => Seq(
    optSelectedSolvers(Set(solverName)),
    optCheckModels(checkModels),
    optFeelingLucky(feelingLucky),
    optUnrollAssumptions(unrollAssumptions),
    optTimeout(300),
    ast.optPrintUniqueIds(true)
  )}

  val isAssociativeID = FreshIdentifier("isAssociative")
  val isAssociative = mkFunDef(isAssociativeID)("A") { case Seq(aT) => (
    Seq("f" :: ((aT, aT) =>: aT)), BooleanType, { case Seq(f) =>
      forall("x" :: aT, "y" :: aT, "z" :: aT)((x,y,z) => f(f(x,y),z) === f(x,f(y,z)))
    })
  }

  val isCommutativeID = FreshIdentifier("isCommutative")
  val isCommutative = mkFunDef(isCommutativeID)("A") { case Seq(aT) => (
    Seq("f" :: ((aT, aT) =>: aT)), BooleanType, { case Seq(f) =>
      forall("x" :: aT, "y" :: aT)((x,y) => f(x,y) === f(y,x))
    })
  }

  val isRotateID = FreshIdentifier("isRotate")
  val isRotate = mkFunDef(isRotateID)("A") { case Seq(aT) => (
    Seq("f" :: ((aT, aT) =>: aT)), BooleanType, { case Seq(f) =>
      forall("x" :: aT, "y" :: aT, "z" :: aT)((x,y,z) => f(f(x,y),z) === f(f(y,z),x))
    })
  }

  val isIdempotentID = FreshIdentifier("isIdempotent")
  val isIdempotent = mkFunDef(isIdempotentID)("A") { case Seq(aT) => (
    Seq("f" :: ((aT, aT) =>: aT)), BooleanType, { case Seq(f) =>
      forall("x" :: aT, "y" :: aT)((x,y) => f(x,y) === f(x,f(x,y)))
    })
  }

  val symbols = new Symbols(Map(
    isAssociativeID -> isAssociative,
    isCommutativeID -> isCommutative,
    isRotateID      -> isRotate,
    isIdempotentID  -> isIdempotent
  ), Map.empty)

  test("Pair of associative ==> associative pair") { ctx => 
    val program = InoxProgram(ctx, symbols)

    val (aT,bT) = (T("A"), T("B"))
    val Seq(f1,f2) = Seq("f1" :: ((aT, aT) =>: aT), "f2" :: ((bT, bT) =>: bT)).map(_.toVariable)
    val clause = isAssociative(aT)(f1) && isAssociative(bT)(f2) && !isAssociative(T(aT,bT)) {
      \("p1" :: T(aT,bT), "p2" :: T(aT, bT))((p1,p2) => E(f1(p1._1,p2._1), f2(p1._2,p2._2)))
    }

    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isUNSAT)
  }

  test("Commutative and rotate ==> associative") { ctx =>
    val program = InoxProgram(ctx, symbols)

    val aT = T("A")
    val f = ("f" :: ((aT, aT) =>: aT)).toVariable
    val clause = isCommutative(aT)(f) && isRotate(aT)(f) && !isAssociative(aT)(f)

    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isUNSAT)
  }

  test("Commutative and rotate ==> associative (integer type)") { ctx =>
    val program = InoxProgram(ctx, symbols)

    val f = ("f" :: ((IntegerType, IntegerType) =>: IntegerType)).toVariable
    val clause = isCommutative(IntegerType)(f) && isRotate(IntegerType)(f) && !isAssociative(IntegerType)(f)

    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isUNSAT)
  }

  test("Associatve =!=> commutative") { ctx =>
    val program = InoxProgram(ctx, symbols)

    val aT = T("A")
    val f = ("f" :: ((aT, aT) =>: aT)).toVariable
    val clause = isAssociative(aT)(f) && !isCommutative(aT)(f)

    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("Commutative =!=> associative") { ctx =>
    val program = InoxProgram(ctx, symbols)

    val aT = T("A")
    val f = ("f" :: ((aT, aT) =>: aT)).toVariable
    val clause = isCommutative(aT)(f) && !isAssociative(aT)(f)

    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("Commutative + idempotent satisfiable") { ctx =>
    val program = InoxProgram(ctx, symbols)

    val f = ("f" :: ((IntegerType, IntegerType) =>: IntegerType)).toVariable
    val clause = isCommutative(IntegerType)(f) && isIdempotent(IntegerType)(f) &&
      !(f(E(BigInt(1)), E(BigInt(2))) ===
        f(f(E(BigInt(2)), E(BigInt(1))), E(BigInt(3))))

    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("Unification is unsatisfiable") { ctx =>
    val program = InoxProgram(ctx, symbols)

    val aT = T("A")
    val f = ("f" :: ((aT, aT) =>: aT)).toVariable
    val clause = forall("x" :: aT, "y" :: aT)((x,y) => !(f(x,y) === f(y,x)))

    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isUNSAT)
  }
}
