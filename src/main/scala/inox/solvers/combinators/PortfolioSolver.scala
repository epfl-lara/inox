/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package combinators

import inox.solvers.SolverResponses._

import scala.concurrent._
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

trait PortfolioSolver extends Solver { self =>
  import context._
  import program._
  import program.trees._

  final type SubSolver = Solver { val program: self.program.type }

  val solvers: Seq[SubSolver]
  val name = "Pfolio"

  protected var resultSolver: Option[Solver] = None

  private[this] var tasks: Future[Unit] = Future(())

  private[combinators] def perform(task: => Unit): Unit = tasks = tasks map (_ => task)

  override def getResultSolver = resultSolver

  def declare(vd: ValDef): Unit = {
    perform { solvers.foreach(_.declare(vd)) }
  }

  def assertCnstr(expression: Expr): Unit = {
    perform { solvers.foreach(_.assertCnstr(expression)) }
  }

  override def dbg(msg: => Any) = solvers foreach (_.dbg(msg))

  private def genericCheck(config: Configuration)
                          (f: SubSolver => config.Response[Model, Assumptions]):
                           config.Response[Model, Assumptions] = {
    Await.result(tasks, Duration.Inf)
    reporter.debug("Running portfolio check")

    // solving
    val fs: Seq[Future[(SubSolver, config.Response[Model, Assumptions])]] = solvers.map { s =>
      Future {
        try {
          val result = f(s)
          (s, result)
        } catch {
          case _: StackOverflowError =>
            reporter.warning("Stack Overflow while running solver.check()!")
            (s, config.cast(Unknown))
        }
      }
    }

    tasks = Future.sequence(fs).map(_ => ())

    val result = Future.find(fs.toList)(_._2 != Unknown)

    val res = Await.result(result, Duration.Inf) match {
      case Some((s, r)) =>
        resultSolver = s.getResultSolver
        resultSolver.foreach { solv =>
          reporter.debug("Solved with "+solv)
        }
        solvers.foreach(_.interrupt())
        r
      case None =>
        reporter.debug("No solver succeeded")
        //fs.foreach(f => println(f.value))
        config.cast(Unknown)
    }

    // TODO: Decide if we really want to wait for all the solvers.
    // I understand we interrupt them, but what if one gets stuck
    // fs foreach { Await.ready(_, Duration.Inf) }
    res
  }


  def check(config: CheckConfiguration): config.Response[Model, Assumptions] = {
    genericCheck(config)(subSolver => subSolver.check(config))
  }

  def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[Model, Assumptions] = {
    genericCheck(config)(subSolver => subSolver.checkAssumptions(config)(assumptions))
  }

  def push(): Unit = {
    perform { solvers.foreach(_.push()) }
  }

  def pop(): Unit = {
    perform { solvers.foreach(_.pop()) }
  }

  def free() = {
    perform { solvers.foreach(_.free()) }
  }

  def interrupt(): Unit = {
    solvers.foreach(_.interrupt())
  }

  def reset() = {
    perform { solvers.foreach(_.reset()) }
  }
}
