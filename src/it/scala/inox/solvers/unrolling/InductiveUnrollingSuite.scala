/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

class InductiveUnrollingSuite extends SolvingTestSuite {
  import trees._
  import dsl._

  val listID = FreshIdentifier("List")
  val consID = FreshIdentifier("Cons")
  val nilID  = FreshIdentifier("Nil")

  val head = FreshIdentifier("head")
  val tail = FreshIdentifier("tail")

  val List = mkSort(listID)("A")(Seq(consID, nilID))
  val Nil  = mkConstructor(nilID)("A")(Some(listID))(_ => Seq.empty)
  val Cons = mkConstructor(consID)("A")(Some(listID)) {
    case Seq(aT) => Seq(ValDef(head, aT), ValDef(tail, T(listID)(aT)))
  }

  val sizeID = FreshIdentifier("size")
  val sizeFd = mkFunDef(sizeID)("A") { case Seq(aT) => (
    Seq("l" :: T(listID)(aT)), IntegerType, { case Seq(l) =>
      if_ (l.isInstOf(T(consID)(aT))) {
        E(BigInt(1)) + let("res" :: IntegerType, E(sizeID)(aT)(l.asInstOf(T(consID)(aT)).getField(tail))) {
          res => Assume(res >= E(BigInt(0)), res)
        }
      } else_ {
        E(BigInt(0))
      }
    })
  }

  val appendID = FreshIdentifier("append")
  val append = mkFunDef(appendID)("A") { case Seq(aT) => (
    Seq("l1" :: T(listID)(aT), "l2" :: T(listID)(aT)), T(listID)(aT), { case Seq(l1, l2) =>
      if_ (l1.isInstOf(T(consID)(aT))) {
        let("c" :: T(consID)(aT), l1.asInstOf(T(consID)(aT))) { c =>
          T(consID)(aT)(c.getField(head), E(appendID)(aT)(c.getField(tail), l2))
        }
      } else_ {
        l2
      }
    })
  }

  val flatMapID = FreshIdentifier("flatMap")
  val flatMap = mkFunDef(flatMapID)("A","B") { case Seq(aT, bT) => (
    Seq("l" :: T(listID)(aT), "f" :: (aT =>: T(listID)(bT))), T(listID)(bT), { case Seq(l, f) =>
      if_ (l.isInstOf(T(consID)(aT))) {
        let("c" :: T(consID)(aT), l.asInstOf(T(consID)(aT))) { c =>
          append(bT)(f(c.getField(head)), E(flatMapID)(aT,bT)(c.getField(tail), f))
        }
      } else_ {
        T(nilID)(bT)()
      }
    })
  }

  val assocID = FreshIdentifier("associative_lemma")
  val associative = mkFunDef(assocID)("A","B","C") { case Seq(aT, bT, cT) => (
    Seq("l1" :: T(listID)(aT), "l2" :: T(listID)(bT), "l3" :: T(listID)(cT),
      "f" :: (aT =>: T(listID)(bT)), "g" :: (bT =>: T(listID)(cT))), BooleanType,
      { case Seq(l1, l2, l3, f, g) =>
        (if_ (l3.isInstOf(T(consID)(cT))) {
          Assume(E(assocID)(aT, bT, cT)(l1, l2, l3.asInstOf(T(consID)(cT)).getField(tail), f, g), E(true))
        } else_ {
          if_ (l2.isInstOf(T(consID)(bT))) {
            let("c" :: T(consID)(bT), l2.asInstOf(T(consID)(bT))) { c =>
              Assume(E(assocID)(aT, bT, cT)(l1, c.getField(tail), g(c.getField(head)), f, g), E(true))
            }
          } else_ {
            if_ (l1.isInstOf(T(consID)(aT))) {
              let("c" :: T(consID)(aT), l1.asInstOf(T(consID)(aT))) { c =>
                Assume(E(assocID)(aT, bT, cT)(c.getField(tail), f(c.getField(head)), T(nilID)(cT)(), f, g), E(true))
              }
            } else_ {
              E(true)
            }
          }
        }) && append(cT)(l3, flatMap(bT,cT)(append(bT)(l2, flatMap(aT,bT)(l1, f)), g)) ===
          append(cT)(append(cT)(l3, flatMap(bT,cT)(l2, g)), flatMap(aT,cT)(l1, \("x" :: aT) { x =>
            flatMap(bT,cT)(f(x), g)
          }))
      })
  }

  val forallID = FreshIdentifier("forall")
  val forall = mkFunDef(forallID)("A") { case Seq(aT) => (
    Seq("l" :: T(listID)(aT), "p" :: (aT =>: BooleanType)), BooleanType, { case Seq(l, p) =>
      if_ (l.isInstOf(T(consID)(aT))) {
        let("cons" :: T(consID)(aT), l.asInstOf(T(consID)(aT))) { cons =>
          p(cons.getField(head)) && E(forallID)(aT)(cons.getField(tail), p)
        }
      } else_ {
        E(true)
      }
    })
  }

  val contentID = FreshIdentifier("content")
  val content = mkFunDef(contentID)("A") { case Seq(aT) => (
    Seq("l" :: T(listID)(aT)), SetType(aT), { case Seq(l) =>
      if_ (l.isInstOf(T(consID)(aT))) {
        let("cons" :: T(consID)(aT), l.asInstOf(T(consID)(aT))) { cons =>
          E(contentID)(aT)(cons.getField(tail)).insert(cons.getField(head))
        }
      } else_ {
        FiniteSet(Seq.empty, aT)
      }
    })
  }

  val partitionID = FreshIdentifier("partition")
  val partition = mkFunDef(partitionID)("A") { case Seq(aT) => (
    Seq("l" :: T(listID)(aT), "p" :: (aT =>: BooleanType)), T(T(listID)(aT), T(listID)(aT)), { case Seq(l, p) =>
      let("res" :: T(T(listID)(aT), T(listID)(aT)), if_ (l.isInstOf(T(consID)(aT))) {
        let("cons" :: T(consID)(aT), l.asInstOf(T(consID)(aT))) { cons =>
          let("ptl" :: T(T(listID)(aT), T(listID)(aT)), E(partitionID)(aT)(cons.getField(tail), p)) { ptl =>
            if_ (p(cons.getField(head))) {
              E(T(consID)(aT)(cons.getField(head), ptl._1), ptl._2)
            } else_ {
              E(ptl._1, T(consID)(aT)(cons.getField(head), ptl._2))
            }
          }
        }
      } else_ {
        E(l, l)
      }) { res =>
        Assume(
          E(forallID)(aT)(res._1, p) &&
          E(forallID)(aT)(res._2, \("x" :: aT)(x => !p(x))) &&
          E(contentID)(aT)(l) === E(contentID)(aT)(res._1) ++ E(contentID)(aT)(res._2),
          res)
      }
    })
  }

  val sortID = FreshIdentifier("sort")
  val sort = mkFunDef(sortID)("A") { case Seq(aT) => (
    Seq("l" :: T(listID)(aT), "lt" :: ((aT, aT) =>: BooleanType)), T(listID)(aT), { case Seq(l, lt) =>
      let("res" :: T(listID)(aT), if_ (l.isInstOf(T(consID)(aT))) {
        let("cons" :: T(consID)(aT), l.asInstOf(T(consID)(aT))) { cons =>
        let("part" :: T(T(listID)(aT), T(listID)(aT)),
          E(partitionID)(aT)(cons.getField(tail), \("x" :: aT)(x => lt(x, cons.getField(head))))) { part =>
        let("less" :: T(listID)(aT), E(sortID)(aT)(part._1, lt)) { less =>
        let("more" :: T(listID)(aT), E(sortID)(aT)(part._2, lt)) { more =>
        let("res" :: T(listID)(aT), E(appendID)(aT)(less, T(consID)(aT)(cons.getField(head), more))) { res =>
          Assume(E(forallID)(aT)(part._1, \("x" :: aT)(x => lt(x, cons.getField(head)))),
          Assume(E(contentID)(aT)(less) === E(contentID)(aT)(part._1),
          Assume(E(forallID)(aT)(less, \("x" :: aT)(x => lt(x, cons.getField(head)))),
            res
          )))
        }}}}}
      } else_ {
        l
      }) { res =>
        Assume(E(contentID)(aT)(l) === E(contentID)(aT)(res), res)
      }
    })
  }

  val symbols = new Symbols(
    Map(sizeID -> sizeFd, appendID -> append, flatMapID -> flatMap, assocID -> associative,
        forallID -> forall, contentID -> content, partitionID -> partition, sortID -> sort),
    Map(listID -> List, consID -> Cons, nilID -> Nil)
  )

  test("size(x) == 0 is satisfiable") { ctx =>
    val program = InoxProgram(ctx, symbols)
    val vd = "x" :: T(listID)(IntegerType)
    val clause = sizeFd(IntegerType)(vd.toVariable) === E(BigInt(0))

    assert(SimpleSolverAPI(SolverFactory.default(program)).solveSAT(clause).isSAT)
  }

  test("size(x) < 0 is unsatisfiable") { ctx =>
    val program = InoxProgram(ctx, symbols)
    val vd = "x" :: T(listID)(IntegerType)
    val clause = sizeFd(IntegerType)(vd.toVariable) < E(BigInt(0))

    assert(SimpleSolverAPI(SolverFactory.default(program)).solveSAT(clause).isUNSAT)
  }

  test("flatMap is associative") { ctx =>
    val program = InoxProgram(ctx, symbols)
    assert(SimpleSolverAPI(SolverFactory.default(program)).solveSAT(Not(associative.fullBody)).isUNSAT)
  }

  test("sort preserves content") { ctx =>
    val program = InoxProgram(ctx, symbols)
    val (l,p) = ("l" :: T(listID)(IntegerType), "p" :: ((IntegerType, IntegerType) =>: BooleanType))
    val clause = E(contentID)(IntegerType)(E(sortID)(IntegerType)(l.toVariable, p.toVariable)) ===
      E(contentID)(IntegerType)(l.toVariable)
    assert(SimpleSolverAPI(SolverFactory.default(program)).solveSAT(Not(clause)).isUNSAT)
  }

}
