/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers.z3

import solvers.{z3 => _, _}
import unrolling._

import z3.scala._

trait Z3Unrolling extends AbstractUnrollingSolver { self =>

  import program._
  import program.trees._
  import program.symbols._

  type Encoded = Z3AST

  protected lazy val theories = solvers.theories.Z3(fullEncoder.targetProgram)

  protected val underlying: AbstractSolver with Z3Native {
    val program: targetProgram.type
    type Trees = Encoded
  }

  protected lazy val z3 = underlying.z3

  object templates extends {
    val program: targetProgram.type = targetProgram
  } with Templates {
    import program.trees._

    type Encoded = self.Encoded

    def asString(ast: Z3AST): String = ast.toString
    def abort: Boolean = self.abort
    def pause: Boolean = self.pause

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

    def extractNot(e: Z3AST): Option[Z3AST] = underlying.extractNot(e)
  }

  protected def declareVariable(v: t.Variable): Z3AST = underlying.declareVariable(v)

  protected def wrapModel(model: Z3Model): super.ModelWrapper = ModelWrapper(model)

  private case class ModelWrapper(model: Z3Model) extends super.ModelWrapper {
    private val ex = new underlying.ModelExtractor(model)

    def extractConstructor(v: Z3AST, tpe: t.ADTType): Option[Identifier] = model.eval(v).flatMap {
      elem => z3.getASTKind(elem) match {
        case Z3AppAST(decl, args) if underlying.constructors containsB decl =>
          underlying.constructors.toA(decl) match {
            case t.ADTType(id, _) => Some(id)
            case _ => None
          }
        case _ => None
      }
    }

    def extractSet(v: Z3AST, tpe: t.SetType): Option[Seq[Z3AST]] = model.eval(v).flatMap {
      elem => model.getSetValue(elem) collect { case (set, true) => set.toSeq }
    }

    def extractBag(v: Z3AST, tpe: t.BagType): Option[Seq[(Z3AST, Z3AST)]] = model.eval(v).flatMap {
      elem => model.getArrayValue(elem) flatMap { case (z3Map, z3Default) =>
        z3.getASTKind(z3Default) match {
          case Z3NumeralIntAST(Some(0)) => Some(z3Map.toSeq)
          case _ => None
        }
      }
    }

    def extractMap(v: Z3AST, tpe: t.MapType): Option[(Seq[(Z3AST, Z3AST)], Z3AST)] = model.eval(v).flatMap {
      elem => model.getArrayValue(elem).map(p => p._1.toSeq -> p._2)
    }

    def modelEval(elem: Z3AST, tpe: t.Type): Option[t.Expr] = {
      val timer = ctx.timers.solvers.z3.eval.start()
      val res = tpe match {
        case t.BooleanType => model.evalAs[Boolean](elem).map(t.BooleanLiteral)
        case t.Int32Type => model.evalAs[Int](elem).map(t.IntLiteral(_)).orElse {
          model.eval(elem).flatMap(term => ex.get(term, t.Int32Type))
        }
        case t.IntegerType => model.evalAs[Int](elem).map(t.IntegerLiteral(_))
        case other => model.eval(elem).flatMap(ex.get(_, other))
      }
      timer.stop()
      res
    }

    def getChoose(id: Identifier): Option[t.Expr] = ex.chooses.get(id)

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

  override def reset(): Unit = {
    super.reset()
    underlying.reset()
  }

  override def interrupt(): Unit = {
    underlying.interrupt()
    super.interrupt()
  }

  override def free(): Unit = {
    super.free()
    underlying.free()
  }
}
