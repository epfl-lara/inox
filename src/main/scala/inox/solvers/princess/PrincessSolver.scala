/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package princess

import ap._
import ap.parser._

import unrolling._

import scala.collection.mutable.{Map => MutableMap}

trait PrincessSolver extends AbstractUnrollingSolver { self =>
  import context._
  import program._
  import program.trees._
  import program.symbols._

  override val name = "Princess"

  protected lazy val theories: ast.ProgramTransformer {
    val sourceProgram: fullEncoder.targetProgram.type
    val targetProgram: Program { val trees: fullEncoder.targetProgram.trees.type }
  } = solvers.theories.Princess(fullEncoder)(semantics.getEvaluator)

  protected object underlying extends {
    val program: targetProgram.type = targetProgram
    val context = self.context
  } with AbstractPrincessSolver {
    lazy val semantics = targetSemantics
  }

  type Encoded = IExpression

  object templates extends {
    val program: targetProgram.type = targetProgram
    val context = self.context
  } with Templates {
    import program.trees._

    type Encoded = self.Encoded

    def asString(ast: IExpression): String = ast.toString
    def abort: Boolean = self.abort
    def pause: Boolean = self.pause

    def encodeSymbol(v: Variable): IExpression = underlying.freshSymbol(v)

    def mkEncoder(bindings: Map[Variable, IExpression])(e: Expr): IExpression = {
      underlying.inoxToPrincess(e)(bindings)
    }

    def mkSubstituter(substMap: Map[IExpression, IExpression]): IExpression => IExpression = {
      val visitor = new CollectingVisitor[Unit, IExpression] {
        override def preVisit(t: IExpression, unit: Unit): PreVisitResult = substMap.get(t) match {
          case Some(nt) => ShortCutResult(nt)
          case _ => KeepArg
        }

        def postVisit(t: IExpression, unit: Unit, subs: Seq[IExpression]): IExpression = t update subs
      }

      (iexpr: IExpression) => visitor.visit(iexpr, ())
    }

    import scala.language.implicitConversions
    private implicit def exprToFormula(iexpr: IExpression): IFormula = iexpr.asInstanceOf[IFormula]

    def mkNot(e: IExpression) = ! e
    def mkAnd(es: IExpression*) = (es.head /: es.tail)((p,q) => p & q)
    def mkOr(es: IExpression*) = (es.head /: es.tail)((p,q) => p | q)
    def mkImplies(e1: IExpression, e2: IExpression) = e1 ==> e2
    def mkEquals(e1: IExpression, e2: IExpression) = (e1, e2) match {
      case (f1: IFormula, f2: IFormula) => f1 <=> f2
      case (t1: ITerm, t2: ITerm) => t1 === t2
      case _ => throw underlying.PrincessSolverException(s"Unhandled equality between $e1 and $e2")
    }

    def extractNot(e: IExpression) = e match {
      case INot(e2) => Some(e2)
      case _ => None
    }
  }

  protected def declareVariable(v: t.Variable): IExpression = underlying.declareVariable(v)

  protected def wrapModel(model: underlying.Model): super.ModelWrapper = ModelWrapper(model)

  private case class ModelWrapper(model: underlying.Model) extends super.ModelWrapper {
    private val chooses: MutableMap[Identifier, t.Expr] = MutableMap.empty
    import IExpression._

    def extractConstructor(v: IExpression, tpe: t.ADTType): Option[Identifier] =
      model.eval(v.asInstanceOf[ITerm]).flatMap { elem =>
        val realType = underlying.program.symbols.bestRealType(tpe).asInstanceOf[t.ADTType]
        val (sort, adts) = underlying.typeToSort(tpe)
        (adts.map(_._1) zip sort.ctorIds).collectFirst {
          case (`realType`, fun) => model.eval(fun(v.asInstanceOf[ITerm])).map { i =>
            val index = i.intValue
            val constructors = adts.flatMap(_._2.cases)
            constructors(index).tpe.asInstanceOf[t.ADTType].id
          }
        }.flatten
      }

    def extractSet(v: IExpression, tpe: t.SetType) = scala.sys.error("Should never happen")
    def extractBag(v: IExpression, tpe: t.BagType) = scala.sys.error("Should never happen")
    def extractMap(v: IExpression, tpe: t.MapType) = scala.sys.error("Should never happen")

    def modelEval(elem: IExpression, tpe: t.Type): Option[t.Expr] = {
      val timer = timers.solvers.princess.eval.start()
      val (res, cs) = underlying.princessToInox(elem, tpe)(model)
      chooses ++= cs.map(p => p._1.res.id -> p._2)
      timer.stop()
      res
    }

    def getChoose(id: Identifier): Option[t.Expr] = chooses.get(id)

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
