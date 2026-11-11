/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package combinators

import inox.solvers.SolverResponses._

import scala.concurrent._
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

trait PortfolioSolver extends Solver { self =>
  import context.{given, _}
  import program._
  import program.trees._

  final type SubSolver = Solver { val program: self.program.type }

  val solvers: Seq[SubSolver]
  val name = "Pfolio"

  // Used to report SMT Lib files <-> VCs correspondence
  override def getSmtLibFileId: Option[Int] = if solvers.isEmpty then None else solvers.head.getSmtLibFileId

  override def resourceLimitReached: Boolean = solvers.exists(_.resourceLimitReached)

  protected var resultSolver: Option[Solver] = None

  private var tasks: Future[Unit] = Future(())

  private[combinators] def perform(task: => Unit): Unit = tasks = tasks map (_ => task)

  override def getResultSolver = resultSolver

  /** How long a solver gets to stop once another one has answered, see `genericCheck`. */
  protected val stopTimeout: FiniteDuration = 10.seconds

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
    val solverThreads = new java.util.concurrent.ConcurrentHashMap[Solver, Thread]()
    val fs: Seq[Future[(SubSolver, config.Response[Model, Assumptions])]] = solvers.map { s =>
      Future {
        solverThreads.put(s, Thread.currentThread())
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

    val res =
      inox.utils.FutureUtils.findFirst(fs)(_._2 != Unknown) match {
        case Some((s, r)) =>
          resultSolver = s.getResultSolver
          resultSolver.foreach { solv =>
            reporter.debug("Solved with "+solv)
          }
          solvers.foreach(_.interrupt())
          r
        case None =>
          reporter.debug("No solver succeeded")
          config.cast(Unknown)
      }

    // Wait for all the solvers to stop: a solver that is still running when its next check or its
    // free starts could be left in an invalid state (a Princess check would get stuck). The
    // interrupt kills the external solver processes at once, and the solvers check it in their
    // own code, including in their evaluators, so a solver stops within about the time its
    // process takes to release its memory (a second for 16 GB).
    fs.zip(solvers).foreach { case (fut, solver) =>
      try Await.ready(fut, stopTimeout)
      catch {
        case _: TimeoutException =>
          val where = Option(solverThreads.get(solver)) match {
            case Some(thread) =>
              val state = thread.getState
              val trace = thread.getStackTrace.map("    at " + _).mkString("\n")
              // The check may have returned between the timeout and the snapshot, after which the
              // thread moves on to other work and the trace says nothing about the solver. A future
              // that is still incomplete after the snapshot was incomplete during it.
              if (fut.isCompleted) "It stopped just after the timeout."
              else s"Its thread ${thread.getName} is $state at:\n$trace"
            case None =>
              "Its check has not started."
          }
          reporter.fatalError(
            s"Solver ${solver.name} in portfolio did not stop within $stopTimeout after being interrupted." +
            " Continuing could leave the solver in an invalid state, so the verification stops." +
            s" Please report this at https://github.com/epfl-lara/inox/issues with the trace below.\n$where")
      }
    }
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
