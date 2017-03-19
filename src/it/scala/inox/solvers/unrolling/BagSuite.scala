/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

class BagSuite extends SolvingTestSuite with DatastructureUtils {
  import trees._
  import dsl._

  override def configurations = for {
    solverName   <- Seq("nativez3", "unrollz3", "smt-z3", "smt-cvc4")
    feelingLucky <- Seq(false, true)
  } yield Seq(
    optSelectedSolvers(Set(solverName)),
    optCheckModels(true),
    optFeelingLucky(feelingLucky),
    optTimeout(300),
    ast.optPrintUniqueIds(true)
  )

  override def optionsString(options: Options): String = {
    "solvr=" + options.findOptionOrDefault(optSelectedSolvers).head + " " +
    "lucky=" + options.findOptionOrDefault(optFeelingLucky)
  }

  val bagID = FreshIdentifier("bag")
  val bag = mkFunDef(bagID)("A") { case Seq(aT) => (
    Seq("l" :: List(aT)), BagType(aT), { case Seq(l) =>
      if_ (l.isInstOf(Cons(aT))) {
        let("c" :: Cons(aT), l.asInstOf(Cons(aT))) { c =>
          BagAdd(E(bagID)(aT)(c.getField(tail)), c.getField(head))
        }
      } else_ {
        FiniteBag(Seq.empty, aT)
      }
    })
  }

  val splitID = FreshIdentifier("split")
  val split = mkFunDef(splitID)("A") { case Seq(aT) => (
    Seq("l" :: List(aT)), T(List(aT), List(aT)), { case Seq(l) =>
      let(
        "res" :: T(List(aT), List(aT)),
        if_ (l.isInstOf(Cons(aT)) && l.asInstOf(Cons(aT)).getField(tail).isInstOf(Cons(aT))) {
          let(
            "tuple" :: T(List(aT), List(aT)),
            E(splitID)(aT)(l.asInstOf(Cons(aT)).getField(tail).asInstOf(Cons(aT)).getField(tail))
          ) { tuple => E(
            Cons(aT)(l.asInstOf(Cons(aT)).getField(head), tuple._1),
            Cons(aT)(l.asInstOf(Cons(aT)).getField(tail).asInstOf(Cons(aT)).getField(head), tuple._2)
          )}
        } else_ {
          E(l, Nil(aT)())
        }
      ) { res => Assume(bag(aT)(l) === BagUnion(bag(aT)(res._1), bag(aT)(res._2)), res) }
    })
  }

  val split2ID = FreshIdentifier("split2")
  val split2 = mkFunDef(split2ID)("A") { case Seq(aT) => (
    Seq("l" :: List(aT)), T(List(aT), List(aT)), { case Seq(l) =>
      let(
        "res" :: T(List(aT), List(aT)),
        if_ (l.isInstOf(Cons(aT)) && l.asInstOf(Cons(aT)).getField(tail).isInstOf(Cons(aT))) {
          let(
            "tuple" :: T(List(aT), List(aT)),
            E(splitID)(aT)(l.asInstOf(Cons(aT)).getField(tail).asInstOf(Cons(aT)).getField(tail))
          ) { tuple => E(
            Cons(aT)(l.asInstOf(Cons(aT)).getField(head), tuple._1),
            Cons(aT)(l.asInstOf(Cons(aT)).getField(tail).asInstOf(Cons(aT)).getField(head), tuple._2)
          )}
        } else_ {
          E(Nil(aT)(), Nil(aT)())
        }
      ) { res => Assume(bag(aT)(l) === BagUnion(bag(aT)(res._1), bag(aT)(res._2)), res) }
    })
  }

  val symbols = baseSymbols.withFunctions(Seq(bag, split, split2))

  test("Finite model finding 1") { ctx =>
    val program = InoxProgram(ctx, symbols)

    val aT = TypeParameter.fresh("A")
    val b = ("bag" :: BagType(aT)).toVariable
    val clause = Not(Equals(b, FiniteBag(Seq.empty, aT)))

    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("Finite model finding 2") { ctx =>
    val program = InoxProgram(ctx, symbols)

    val aT = TypeParameter.fresh("A")
    val b = ("bag" :: BagType(aT)).toVariable
    val elem = ("elem" :: aT).toVariable
    val clause = Not(Equals(b, FiniteBag(Seq(elem -> IntegerLiteral(1)), aT)))

    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("Finite model finding 3") { ctx =>
    val program = InoxProgram(ctx, symbols)

    val aT = TypeParameter.fresh("A")
    val b = ("bag" :: BagType(aT)).toVariable
    val Seq(e1, v1, e2, v2) = Seq("e1" :: aT, "v1" :: IntegerType, "e2" :: aT, "v2" :: IntegerType).map(_.toVariable)
    val clause = And(Seq(
      Not(Equals(b, FiniteBag(Seq(e1 -> v1, e2 -> v2), aT))),
      Not(Equals(MultiplicityInBag(e1, b), IntegerLiteral(0))),
      Not(Equals(MultiplicityInBag(e2, b), IntegerLiteral(0)))
    ))

    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("split preserves content") { ctx =>
    val program = InoxProgram(ctx, symbols)
    val Let(vd, body, Assume(pred, _)) = split.fullBody
    val clause = Let(vd, body, pred)

    assert(SimpleSolverAPI(program.getSolver).solveVALID(clause) contains true)
  }

  def filter(ctx: Context): FilterStatus = {
    val solvers = ctx.options.findOptionOrDefault(optSelectedSolvers)
    // @nv: these tests are unstable due to bugs in z3
    if (solvers == Set("unrollz3") || solvers == Set("smt-z3")) Skip
    else Test
  }

  test("split2 doesn't preserve content", filter(_)) { ctx =>
    val program = InoxProgram(ctx, symbols)
    val Let(vd, body, Assume(pred, _)) = split2.fullBody
    val clause = Let(vd, body, pred)

    assert(SimpleSolverAPI(program.getSolver).solveSAT(Not(clause)).isSAT)
  }
}
