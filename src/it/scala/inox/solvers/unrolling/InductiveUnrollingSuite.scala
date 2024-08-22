/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

class InductiveUnrollingSuite extends SolvingTestSuite with DatastructureUtils {
  import trees._
  import dsl._

  val sizeID = FreshIdentifier("size")
  val appendID = FreshIdentifier("append")
  val appendNoSpecID = FreshIdentifier("appendNoSpec")
  val flatMapID = FreshIdentifier("flatMap")
  val assocID = FreshIdentifier("associative_lemma")

  val forallID = FreshIdentifier("forall")
  val contentID = FreshIdentifier("content")
  val partitionID = FreshIdentifier("partition")
  val sortID = FreshIdentifier("sort")

  val sizeFd = mkFunDef(sizeID)("A") { case Seq(aT) => (
    Seq("l" :: T(listID)(aT)), IntegerType(), { case Seq(l) =>
      if_ (l `is` consID) {
        E(BigInt(1)) + let("res" :: IntegerType(), E(sizeID)(aT)(l.getField(tail))) {
          res => Assume(res >= E(BigInt(0)), res)
        }
      } else_ {
        E(BigInt(0))
      }
    })
  }

  val append = mkFunDef(appendID)("A") { case Seq(aT) => (
    Seq("l1" :: T(listID)(aT), "l2" :: T(listID)(aT)), T(listID)(aT), { case Seq(l1, l2) =>
      let("res" :: T(listID)(aT), if_ (l1 `is` consID) {
        C(consID)(aT)(l1.getField(head), E(appendID)(aT)(l1.getField(tail), l2))
      } else_ {
        l2
      }) { res => Assume(E(contentID)(aT)(res) === E(contentID)(aT)(l1) ++ E(contentID)(aT)(l2), res) }
    })
  }

  // @nv: we define flatMap using this append to make sure the princess solver doesn't get
  //      bogged down in quantifier instantiations due to [[SetEncoder]]
  val appendNoSpec = mkFunDef(appendNoSpecID)("A") { case Seq(aT) => (
    Seq("l1" :: T(listID)(aT), "l2" :: T(listID)(aT)), T(listID)(aT), { case Seq(l1, l2) =>
      if_ (l1 `is` consID) {
        C(consID)(aT)(l1.getField(head), E(appendNoSpecID)(aT)(l1.getField(tail), l2))
      } else_ {
        l2
      }
    })
  }

  val flatMap = mkFunDef(flatMapID)("A","B") { case Seq(aT, bT) => (
    Seq("l" :: T(listID)(aT), "f" :: (aT =>: T(listID)(bT))), T(listID)(bT), { case Seq(l, f) =>
      if_ (l `is` consID) {
        appendNoSpec(bT)(f(l.getField(head)), E(flatMapID)(aT,bT)(l.getField(tail), f))
      } else_ {
        C(nilID)(bT)()
      }
    })
  }

  val associative = mkFunDef(assocID)("A","B","C") { case Seq(aT, bT, cT) => (
    Seq("l1" :: T(listID)(aT), "l2" :: T(listID)(bT), "l3" :: T(listID)(cT),
      "f" :: (aT =>: T(listID)(bT)), "g" :: (bT =>: T(listID)(cT))), BooleanType(),
      { case Seq(l1, l2, l3, f, g) =>
        (if_ (l3 `is` consID) {
          Assume(E(assocID)(aT, bT, cT)(l1, l2, l3.getField(tail), f, g), E(true))
        } else_ {
          if_ (l2 `is` consID) {
            Assume(E(assocID)(aT, bT, cT)(l1, l2.getField(tail), g(l2.getField(head)), f, g), E(true))
          } else_ {
            if_ (l1 `is` consID) {
              Assume(E(assocID)(aT, bT, cT)(l1.getField(tail), f(l1.getField(head)), C(nilID)(cT)(), f, g), E(true))
            } else_ {
              E(true)
            }
          }
        }) && appendNoSpec(cT)(l3, flatMap(bT,cT)(appendNoSpec(bT)(l2, flatMap(aT,bT)(l1, f)), g)) ===
          appendNoSpec(cT)(appendNoSpec(cT)(l3, flatMap(bT,cT)(l2, g)), flatMap(aT,cT)(l1, \("x" :: aT) { x =>
            flatMap(bT,cT)(f(x), g)
          }))
      })
  }

  val forall = mkFunDef(forallID)("A") { case Seq(aT) => (
    Seq("l" :: T(listID)(aT), "p" :: (aT =>: BooleanType())), BooleanType(), { case Seq(l, p) =>
      if_ (l `is` consID) {
        p(l.getField(head)) && E(forallID)(aT)(l.getField(tail), p)
      } else_ {
        E(true)
      }
    })
  }

  val content = mkFunDef(contentID)("A") { case Seq(aT) => (
    Seq("l" :: T(listID)(aT)), SetType(aT), { case Seq(l) =>
      if_ (l `is` consID) {
        E(contentID)(aT)(l.getField(tail)).insert(l.getField(head))
      } else_ {
        FiniteSet(Seq.empty, aT)
      }
    })
  }

  val partition = mkFunDef(partitionID)("A") { case Seq(aT) => (
    Seq("l" :: T(listID)(aT), "p" :: (aT =>: BooleanType())), T(T(listID)(aT), T(listID)(aT)), { case Seq(l, p) =>
      let("res" :: T(T(listID)(aT), T(listID)(aT)), if_ (l `is` consID) {
        let("ptl" :: T(T(listID)(aT), T(listID)(aT)), E(partitionID)(aT)(l.getField(tail), p)) { ptl =>
          if_ (p(l.getField(head))) {
            E(C(consID)(aT)(l.getField(head), ptl._ts1), ptl._ts2)
          } else_ {
            E(ptl._ts1, C(consID)(aT)(l.getField(head), ptl._ts2))
          }
        }
      } else_ {
        E(l, l)
      }) { res =>
        Assume(
          E(forallID)(aT)(res._ts1, p) &&
          E(forallID)(aT)(res._ts2, \("x" :: aT)(x => !p(x))) &&
          E(contentID)(aT)(l) === E(contentID)(aT)(res._ts1) ++ E(contentID)(aT)(res._ts2),
          res)
      }
    })
  }

  val sort = mkFunDef(sortID)("A") { case Seq(aT) => (
    Seq("l" :: T(listID)(aT), "lt" :: ((aT, aT) =>: BooleanType())), T(listID)(aT), { case Seq(l, lt) =>
      let("res" :: T(listID)(aT), if_ (l `is` consID) {
        let("part" :: T(T(listID)(aT), T(listID)(aT)),
          E(partitionID)(aT)(l.getField(tail), \("x" :: aT)(x => lt(x, l.getField(head))))) { part =>
        let("less" :: T(listID)(aT), E(sortID)(aT)(part._ts1, lt)) { less =>
        let("more" :: T(listID)(aT), E(sortID)(aT)(part._ts2, lt)) { more =>
          Assume(E(forallID)(aT)(part._ts1, \("x" :: aT)(x => lt(x, l.getField(head)))),
          Assume(E(contentID)(aT)(part._ts1) === E(contentID)(aT)(less),
          Assume(E(forallID)(aT)(less, \("x" :: aT)(x => lt(x, l.getField(head)))),
            E(appendID)(aT)(less, C(consID)(aT)(l.getField(head), more))
          )))
        }}}
      } else_ {
        l
      }) { res =>
        Assume(E(contentID)(aT)(l) === E(contentID)(aT)(res), res)
      }
    })
  }

  val symbols = baseSymbols
    .withFunctions(Seq(sizeFd, append, appendNoSpec, flatMap, associative, forall, content, partition, sort))

  val program = InoxProgram(symbols)

  test("size(x) == 0 is satisfiable") {
    val vd = "x" :: T(listID)(IntegerType())
    val clause = sizeFd(IntegerType())(vd.toVariable) === E(BigInt(0))

    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("size(x) < 0 is unsatisfiable") {
    val vd = "x" :: T(listID)(IntegerType())
    val clause = sizeFd(IntegerType())(vd.toVariable) < E(BigInt(0))

    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isUNSAT)
  }

  def filter(ctx: Context, allowSelect: Boolean = true, allowOpt: Boolean = false): FilterStatus = {
    val solvers = ctx.options.findOptionOrDefault(optSelectedSolvers)
    val feelingLucky = ctx.options.findOptionOrDefault(optFeelingLucky)
    val checkModels = ctx.options.findOptionOrDefault(optCheckModels)
    val unrollAssume = ctx.options.findOptionOrDefault(optUnrollAssumptions)
    if (solvers == Set("princess") &&
      (!allowSelect || feelingLucky != checkModels || checkModels != unrollAssume)) Skip
    else if (solvers == Set("nativez3-opt") && !allowOpt) Skip
    else Test
  }

  test("flatMap is associative", filter(_, allowOpt = true)) {
    assert(SimpleSolverAPI(program.getSolver).solveSAT(Not(associative.fullBody)).isUNSAT)
  }

  test("sort preserves content 1", filter(_)) {
    val (l,p) = ("l" :: T(listID)(IntegerType()), "p" :: ((IntegerType(), IntegerType()) =>: BooleanType()))
    val clause = E(contentID)(IntegerType())(E(sortID)(IntegerType())(l.toVariable, p.toVariable)) ===
      E(contentID)(IntegerType())(l.toVariable)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(Not(clause)).isUNSAT)
  }

  test("sort preserves content 2", filter(_, allowSelect = false)) {
    import program._
    val clause = sort.fullBody match {
      case Let(res, body, Assume(pred, resVar)) if res.toVariable == resVar =>
        Let(res, body, pred)
      case e => fail("Unexpected fullBody of `sort`: " + e.asString)
    }
    assert(SimpleSolverAPI(program.getSolver).solveSAT(Not(clause)).isUNSAT)
  }

}
