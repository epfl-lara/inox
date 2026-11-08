/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package smtlib

import org.scalatest.funsuite.AnyFunSuite

import _root_.smtlib.trees.Commands.{FunDef => SMTFunDef, _}
import _root_.smtlib.trees.CommandsResponses._
import _root_.smtlib.trees.Terms.{Identifier => _, _}

/** Models whose definitions call the functions of the model, as cvc5 can return them
  * (see epfl-lara/stainless#1549). */
class ModelFunctionCallsSuite extends AnyFunSuite {
  import inox.trees._
  import inox.trees.dsl._
  import SolverResponses._

  val ctx = TestContext.empty

  val fID = FreshIdentifier("f")
  val f = mkFunDef(fID)()(_ => (Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) => x + E(BigInt(1)) }))
  val cID = FreshIdentifier("c")
  val c = mkFunDef(cID)()(_ => (Seq(), IntegerType(), { case _ => E(BigInt(2)) }))

  val program = InoxProgram(NoSymbols.withFunctions(Seq(f, c)))
  import program.symbols.given
  import program.getSemantics

  /** A cvc5 solver whose model defines `v` as `(f 0)` and `w` as `c`, i.e. through the
    * definitions of the (uninterpreted) functions `f` and `c`. */
  def solver(v: Variable, w: Variable) = new SMTLIBSolver(program, ctx) with CVC5Solver {
    override def emit(cmd: SExpr, rawOut: Boolean = false): SExpr = (cmd, super.emit(cmd, rawOut)) match {
      case (_: GetModel, GetModelResponseSuccess(model)) =>
        val fSym = functions.toB(symbols.getFunction(fID, Seq.empty))
        val cSym = functions.toB(symbols.getFunction(cID, Seq.empty))
        GetModelResponseSuccess(model.map {
          case DefineFun(SMTFunDef(s, Seq(), sort, _)) if variables.getA(s).exists(_.id == v.id) =>
            DefineFun(SMTFunDef(s, Seq(), sort, FunctionApplication(SimpleSymbol(fSym), Seq(SNumeral(0)))))
          case DefineFun(SMTFunDef(s, Seq(), sort, _)) if variables.getA(s).exists(_.id == w.id) =>
            DefineFun(SMTFunDef(s, Seq(), sort, SimpleSymbol(cSym)))
          case d => d
        })
      case (_, res) => res
    }
  }

  test("Model definitions that call the functions of the model") {
    val v = Variable.fresh("v", IntegerType())
    val w = Variable.fresh("w", IntegerType())
    val s = solver(v, w)
    try {
      val fCall = FunctionInvocation(fID, Seq(), Seq(E(BigInt(0))))
      val cCall = FunctionInvocation(cID, Seq(), Seq())
      val cnstr = Equals(v, fCall) && Equals(fCall, E(BigInt(5))) && Equals(w, cCall) && Equals(cCall, E(BigInt(7)))
      // The solver's program is `program`, but its type doesn't say so
      s.assertCnstr(cnstr.asInstanceOf[s.program.trees.Expr])
      s.check(Model) match {
        case SatWithModel(model) =>
          def value(x: Variable) = model.vars.toSeq.collect { case (vd, model.program.trees.IntegerLiteral(n)) if vd.id == x.id => n }
          assert(value(v) == Seq(BigInt(5)))
          assert(value(w) == Seq(BigInt(7)))
        case res => fail(s"Expected a model, got $res")
      }
    } finally {
      s.free()
    }
  }
}
