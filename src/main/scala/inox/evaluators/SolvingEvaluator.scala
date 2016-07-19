/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package evaluators

import scala.collection.mutable.{Map => MutableMap}

trait SolvingEvaluator extends Evaluator {

  object bankOption extends InoxOptionDef[EvaluationBank] {
    val parser = { (_: String) => throw FatalError("Unparsable option \"bankOption\"") }
    val name = "bank-option"
    val description = "Evaluation bank shared between solver and evaluator"
    val usageRhs = ""
    def default = new EvaluationBank {
      val program: SolvingEvaluator.this.program.type = SolvingEvaluator.this.program
    }
  }

  val solver: SolverFactory[Solver]
}

/* Status of invariant checking
 *
 * For a given invariant, its checking status can be either
 * - Complete(success) : checking has been performed previously and
 *                       resulted in a value of `success`.
 * - Pending           : invariant is currently being checked somewhere
 *                       in the program. If it fails, the failure is
 *                       assumed to be bubbled up to all relevant failure
 *                       points.
 * - NoCheck           : invariant has never been seen before. Discovering
 *                       NoCheck for an invariant will automatically update
 *                       the status to `Pending` as this creates a checking
 *                       obligation.
 */
sealed abstract class CheckStatus {
  /* The invariant was invalid and this particular case class can't exist */
  def isFailure: Boolean = this match {
    case Complete(status) => !status
    case _ => false
  }

  /* The invariant has never been checked before and the checking obligation
   * therefore falls onto the first caller of this method. */
  def isRequired: Boolean = this == NoCheck
}

case class Complete(success: Boolean) extends CheckStatus
case object Pending extends CheckStatus
case object NoCheck extends CheckStatus

object EvaluationBank {
  def empty(p: Program): EvaluationBank { val program: p.type } = new EvaluationBank {
    val program: p.type = p
    val checkCache = MutableMap.empty
  }

  private def apply(p: Program)(cache: MutableMap[p.trees.CaseClass, CheckStatus]): EvaluationBank { val program: p.type } = new EvaluationBank {
    val program: p.type = p
    val checkCache = cache
  }
}

trait EvaluationBank {
  implicit val program: Program
  import program._
  import program.trees._

  /* Shared set that tracks checked case-class invariants
   *
   * Checking case-class invariants can require invoking a solver
   * on a ground formula that contains a reference to `this` (the
   * current case class). If we then wish to check the model
   * returned by the solver, the expression given to the evaluator
   * will again contain the constructor for the current case-class.
   * This will create an invariant-checking loop.
   *
   * To avoid this problem, we introduce a set of invariants
   * that have already been checked that is shared between related
   * solvers and evaluators. This set is used by the evaluators to
   * determine whether the invariant of a given case
   * class should be checked.
   */
  val checkCache: MutableMap[CaseClass, CheckStatus]

  /* Status of the invariant checking for `cc` */
  def invariantCheck(cc: CaseClass): CheckStatus = synchronized {
    if (!cc.ct.tcd.hasInvariant) Complete(true)
    else checkCache.getOrElse(cc, {
      checkCache(cc) = Pending
      NoCheck
    })
  }

  /* Update the cache with the invariant check result for `cc` */
  def invariantResult(cc: CaseClass, success: Boolean): Unit = synchronized {
    checkCache(cc) = Complete(success)
  }

  override def clone: EvaluationBank { val program: EvaluationBank.this.program.type } =
    EvaluationBank(program)(checkCache.clone)
}
