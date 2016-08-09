/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers.z3

import utils._
import solvers.{z3 => _, _}
import unrolling._
import theories._

import z3.scala._

trait NativeZ3Solver
  extends AbstractUnrollingSolver {

  import program._
  import program.trees._
  import program.symbols._

  override val name = "NativeZ3"

  type Encoded = Z3AST

  object theories extends {
    val sourceProgram: program.type = program
  } with StringEncoder

  protected object underlying extends {
    val program: theories.targetProgram.type = theories.targetProgram
    val options = NativeZ3Solver.this.options
  } with AbstractZ3Solver

  private lazy val z3 = underlying.z3

  object templates extends {
    val program: theories.targetProgram.type = theories.targetProgram
  } with Templates {
    type Encoded = NativeZ3Solver.this.Encoded

    def asString(ast: Z3AST): String = ast.toString

    def encodeSymbol(v: Variable): Z3AST = underlying.symbolToFreshZ3Symbol(v)

    def mkEncoder(bindings: Map[Variable, Z3AST])(e: Expr): Z3AST = {
      underlying.toZ3Formula(e, bindings)
    }

    def mkSubstituter(substMap: Map[Z3AST, Z3AST]): Z3AST => Z3AST = {
      val (from, to) = substMap.unzip
      val (fromArray, toArray) = (from.toArray, to.toArray)

      (c: Z3AST) => z3.substitute(c, fromArray, toArray)
    }

    def mkNot(e: Z3AST) = z3.mkNot(e)
    def mkOr(es: Z3AST*) = z3.mkOr(es : _*)
    def mkAnd(es: Z3AST*) = z3.mkAnd(es : _*)
    def mkEquals(l: Z3AST, r: Z3AST) = z3.mkEq(l, r)
    def mkImplies(l: Z3AST, r: Z3AST) = z3.mkImplies(l, r)

    def extractNot(l: Z3AST): Option[Z3AST] = z3.getASTKind(l) match {
      case Z3AppAST(decl, args) => z3.getDeclKind(decl) match {
        case OpNot => Some(args.head)
        case _ => None
      }
      case ast => None
    }
  }

  override def reset(): Unit = {
    super.reset()
    underlying.reset()
  }

  def free(): Unit = underlying.free()

  protected def declareVariable(v: Variable): Z3AST = underlying.declareVariable(v)

  protected def wrapModel(model: Z3Model): super.ModelWrapper = ModelWrapper(model)

  private case class ModelWrapper(model: Z3Model) extends super.ModelWrapper {
    def modelEval(elem: Z3AST, tpe: Type): Option[Expr] = {
      val timer = ctx.timers.solvers.z3.eval.start()
      val res = tpe match {
        case BooleanType => model.evalAs[Boolean](elem).map(BooleanLiteral)
        case Int32Type => model.evalAs[Int](elem).map(IntLiteral(_)).orElse {
          model.eval(elem).flatMap(t => underlying.softFromZ3Formula(model, t, Int32Type))
        }
        case IntegerType => model.evalAs[Int](elem).map(IntegerLiteral(_))
        case other => model.eval(elem) match {
          case None => None
          case Some(t) => underlying.softFromZ3Formula(model, t, other)
        }
      }
      timer.stop()
      res
    }

    override def toString = model.toString
  }

  override def push(): Unit = {
    super.push()
    underlying.push()
  }

  override def pop(): Unit = {
    super.pop()
    underlying.pop()
  }

  override def interrupt(): Unit = {
    underlying.interrupt()
    super.interrupt()
  }
}
