/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package datagen

import evaluators._
import solvers._
import utils._

trait ModelEnumerator {
  val factory: SolverFactory
  lazy val program: factory.program.type = factory.program
  import program._
  import program.trees._
  import program.symbols._

  import SolverResponses._

  protected val evaluator: RecursiveEvaluator { val program: ModelEnumerator.this.program.type } =
    RecursiveEvaluator(program)(ctx.toEvaluator, ctx.toSolver)

  def enumSimple(vs: Seq[ValDef], satisfying: Expr): FreeableIterator[Map[ValDef, Expr]] = {
    enumVarying0(vs, satisfying, None, -1)
  }

  /**
   * Enumerate at most `nPerCaracteristic` models with the same value for
   * `caracteristic`.
   *
   * Note: there is no guarantee that the models enumerated consecutively share the
   * same `caracteristic`.
   */
  def enumVarying(vs: Seq[ValDef], satisfying: Expr, measure: Expr, nPerMeasure: Int = 1) = {
    enumVarying0(vs, satisfying, Some(measure), nPerMeasure)
  }

  private[this] def enumVarying0(vs: Seq[ValDef], satisfying: Expr, measure: Option[Expr], nPerMeasure: Int = 1): FreeableIterator[Map[ValDef, Expr]] = {
    val s = factory.getNewSolver

    s.assertCnstr(satisfying)

    val m = measure match {
      case Some(ms) =>
        val m = Variable(FreshIdentifier("measure"), ms.getType)
        s.assertCnstr(Equals(m, ms))
        m
      case None =>
        Variable(FreshIdentifier("noop"), BooleanType)
    }

    var perMeasureRem = Map[Expr, Int]().withDefaultValue(nPerMeasure)

    new FreeableIterator[Map[ValDef, Expr]] {
      def computeNext() = {
        s.check(Model) match {
          case SatWithModel(model) =>
            val fullModel = vs.map { v =>
              v -> model.getOrElse(v, simplestValue(v.getType))
            }.toMap

            // Vary the model
            s.assertCnstr(not(andJoin(fullModel.toSeq.sortBy(_._1).map {
              case (k, v) => equality(k.toVariable, v)
            })))

            measure match {
              case Some(ms) =>
                val mValue = evaluator.eval(ms, fullModel).result.get

                perMeasureRem += (mValue -> (perMeasureRem(mValue) - 1))

                if (perMeasureRem(mValue) <= 0) {
                  s.assertCnstr(not(equality(m, mValue)))
                }

              case None =>
            }

            Some(fullModel)

          case _ =>
            None
        }
      }

      def free() {
        factory.reclaim(s)
      }
    }
  }

  def enumMinimizing(vs: Seq[ValDef], cnstr: Expr, measure: Expr) = {
    enumOptimizing(vs, cnstr, measure, Down)
  }

  def enumMaximizing(vs: Seq[ValDef], cnstr: Expr, measure: Expr) = {
    enumOptimizing(vs, cnstr, measure, Up)
  }

  abstract class SearchDirection
  case object Up   extends SearchDirection
  case object Down extends SearchDirection

  private[this] def enumOptimizing(vs: Seq[ValDef], satisfying: Expr, measure: Expr, dir: SearchDirection): FreeableIterator[Map[ValDef, Expr]] = {
    assert(measure.getType == IntegerType)

    val s = factory.getNewSolver

    s.assertCnstr(satisfying)

    val m = Variable(FreshIdentifier("measure"), measure.getType)
    s.assertCnstr(Equals(m, measure))

    // Search Range
    var ub: Option[BigInt] = None
    var lb: Option[BigInt] = None

    def rangeEmpty() = (lb, ub) match {
      case (Some(l), Some(u)) => u-l <= 1
      case _ => false
    }

    def getPivot(): Option[BigInt] = (lb, ub, dir) match {
      // Bisection Method
      case (Some(l), Some(u), _) => Some(l + (u-l)/2)
      // No bound yet, let the solver find at least one bound
      case (None, None, _)       => None

      // Increase lower bound
      case (Some(l), None, Up)   => Some(l + l.abs + 1)
      // Decrease upper bound
      case (None, Some(u), Down) => Some(u - u.abs - 1)

      // This shouldn't happen
      case _ => None
    }

    new FreeableIterator[Map[ValDef, Expr]] {
      def computeNext(): Option[Map[ValDef, Expr]] = {
        if (rangeEmpty()) {
          None
        } else {
          // Assert a new pivot point
          val thisTry = getPivot().map { t =>
            s.push()
            dir match {
              case Up =>
                s.assertCnstr(GreaterThan(m, IntegerLiteral(t)))
              case Down =>
                s.assertCnstr(LessThan(m, IntegerLiteral(t)))
            }
            t
          }

          s.check(Model) match {
            case SatWithModel(model) =>
              val fullModel = vs.map { v =>
                v -> model.getOrElse(v, simplestValue(v.getType))
              }.toMap

              evaluator.eval(measure, fullModel).result match {
                case Some(IntegerLiteral(measureVal)) =>
                  // Positive result
                  dir match {
                    case Up   => lb = Some(measureVal)
                    case Down => ub = Some(measureVal)
                  }

                  Some(fullModel)

                case _ =>
                  ctx.reporter.warning("Evaluator failed to evaluate measure!")
                  None
              }

            case Unsat =>
              // Negative result
              thisTry match {
                case Some(t) =>
                  s.pop()

                  dir match {
                    case Up   => ub = Some(t)
                    case Down => lb = Some(t)
                  }
                  computeNext()

                case None =>
                  None
              }

            case Unknown =>
              None
          }
        }
      }

      def free() {
        factory.reclaim(s)
      }
    }
  }
}

object ModelEnumerator {
  def apply(sf: SolverFactory): ModelEnumerator { val factory: sf.type } = new ModelEnumerator {
    val factory: sf.type = sf
  }
}
