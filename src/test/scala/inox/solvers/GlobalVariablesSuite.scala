/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

import org.scalatest._

class GlobalVariablesSuite extends FunSuite {
  import inox.trees._
  import dsl._

  val ctx = TestContext.empty

  val freeVariable = Variable(FreshIdentifier("b"), BooleanType)

  val testFd = mkFunDef(FreshIdentifier("test"))()(_ => (
    Seq("i" :: IntegerType), IntegerType, { case Seq(i) =>
      if_ (freeVariable) {
        i
      } else_ {
        E(BigInt(-1))
      }
    }))

  val program = InoxProgram(ctx, NoSymbols.withFunctions(Seq(testFd)))

  val solverNames: Seq[String] = {
    (if (SolverFactory.hasNativeZ3) Seq("nativez3", "unrollz3") else Nil) ++
    (if (SolverFactory.hasZ3)       Seq("smt-z3") else Nil) ++
    (if (SolverFactory.hasCVC4)     Seq("smt-cvc4") else Nil) ++
    Seq("princess")
  }

  for (sname <- solverNames) {
    test(s"Global Variables in $sname") {
      val cnstr = freeVariable && testFd(E(BigInt(42))) < E(BigInt(0))
      assert(SimpleSolverAPI(SolverFactory(sname, program, program.ctx.options)).solveSAT(cnstr).isUNSAT)
    }
  }
}
