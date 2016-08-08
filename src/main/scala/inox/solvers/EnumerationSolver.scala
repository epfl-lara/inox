/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

import evaluators._
import SolverResponses._
import grammars.GrammarsUniverse
import utils._
import datagen._

trait EnumerationSolver extends Solver { self =>

  val grammars: GrammarsUniverse { val program: self.program.type }

  val evaluator: DeterministicEvaluator { val program: self.program.type }

  import program._
  import trees._
  import symbols._
  import exprOps._

  def name = "Enum"

  val maxTried = 10000

  var datagen: Option[DataGenerator { val program: self.program.type }] = None

  private var interrupted = false

  val freeVars    = new IncrementalSet[ValDef]()
  val constraints = new IncrementalSeq[Expr]()

  def assertCnstr(expression: Expr): Unit = {
    constraints += expression
    freeVars ++= variablesOf(expression).map(_.toVal)
  }

  def push() = {
    freeVars.push()
    constraints.push()
  }

  def pop() = {
    freeVars.pop()
    constraints.pop()
  }

  def reset() = {
    freeVars.clear()
    constraints.clear()
    interrupted = false
    datagen     = None
  }

  def check(config: Configuration): config.Response[Model, Cores] = config.cast {
    val res: SolverResponse[Model, Cores] = try {
      datagen = Some(new GrammarDataGen {
        val grammars: self.grammars.type = self.grammars
        val evaluator: DeterministicEvaluator { val program: self.program.type } = self.evaluator
        val grammar: grammars.ExpressionGrammar = grammars.ValueGrammar
        val program: self.program.type = self.program
        def functionsAvailable(p: Program): Set[FunDef] = Set()
      })
      if (interrupted) {
        Unknown
      } else {
        val allFreeVars = freeVars.toSeq.sortBy(_.id.name)
        val allConstraints = constraints.toSeq

        val it: Iterator[Seq[Expr]] = datagen.get.generateFor(allFreeVars, andJoin(allConstraints), 1, maxTried)

        if (it.hasNext) {
          config match {
            case All | Model =>
              val varModels = it.next
              SatWithModel(allFreeVars.zip(varModels).toMap)
            case _ =>
              Sat
          }
        } else {
          config match {
            case All | Cores =>
              ??? // TODO
            case _ =>
              Unsat
          }
        }
      }
    } catch {
      case e: Throwable =>
        Unknown
    }
    datagen = None
    res
  }

  def checkAssumptions(config: Configuration)(assumptions: Set[Trees]): config.Response[Model, Cores] = ??? // TODO

  def free() = {
    constraints.clear()
  }

  def interrupt(): Unit = {
    interrupted = true
    datagen.foreach(_.interrupt())
  }

  def recoverInterrupt(): Unit = {
    interrupted = false
    datagen.foreach(_.recoverInterrupt())
  }
}
