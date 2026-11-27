/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

import scala.collection.immutable.{ListSet, VectorMap}

/** The distinguishing inputs of first-class functions: whenever two functions of the same type
  * can be distinct, a pair of fresh arguments on which they differ (see `function-witnesses.md`).
  *
  * The lambdas and free functions register their pairs as they appear (see [[LambdaTemplates]]),
  * and the pending pairs are instantiated progressively by the solver, at a depth that grows with
  * the unrolling (see [[witnessEqualities]]), or on demand when model extraction needs them (see
  * [[onDemandWitnesses]]). The instantiation itself is [[Templates.instantiateWitness]].
  */
trait WitnessTemplates { self: Templates =>
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  import witnessState._

  /** The witness nesting depth of the symbols currently being instantiated (0 for regular inputs).
    *
    * Everything that descends from a distinguishing input inherits its depth: the free functions in
    * its type unfolding (including ADT fields that are unfolded at later generations, see
    * [[TypeTemplates]]) and the results of the applications it takes part in. Otherwise, the free
    * functions that appear in these could get fresh distinguishing inputs of their own without bound
    * (eg. lambdas that are created anew in each distinguishing input). */
  private var currentWitnessDepth = 0

  protected def witnessDepth: Int = currentWitnessDepth

  protected def withWitnessDepth[T](depth: Int)(body: => T): T = {
    val previous = currentWitnessDepth
    currentWitnessDepth = depth
    try body finally currentWitnessDepth = previous
  }

  /** Registers a distinguishing input for `f1` and `f2` (needed when `cond` holds), to be
    * instantiated by [[instantiateWitnesses]]. Until then, the returned clause lets the solver
    * assume that `f1 == f2` through the [[PendingWitness.equality]] literal. */
  private[unrolling] def registerWitness(
    cond: Encoded, tpe: FunctionType, f1: Encoded, f2: Encoded, onDemand: Boolean = false
  ): Clauses = {
    val depth = (witnessDepths.getOrElse(f1, 0) max witnessDepths.getOrElse(f2, 0)) + 1
    val equality = encodeSymbol(Variable.fresh("b_eq", BooleanType(), true))
    pendingWitnesses += PendingWitness(cond, tpe, f1, f2, depth, equality, onDemand)
    // the equality of on-demand pairs isn't assumed until they are promoted, and a free literal
    // implying it lets the solver merge lambdas in models, which extraction then can't tell apart
    if (onDemand) Seq.empty else Rule.Hypothesis(equality, cond, mkEquals(f1, f2)).clauses
  }

  /** Registers two lambdas of the program, which are both defined when `cond` holds, as only
    * equal under extensional equality when they agree on every input (see [[lambdaDistinctions]]).
    * `closuresEqual` is the equality of their closures when they have the same body, under which
    * they are equal (see [[Rule.LambdaEquality]]). */
  private[unrolling] def registerLambdaPair(cond: Encoded, f1: Encoded, f2: Encoded, closuresEqual: Option[Encoded]): Unit =
    lambdaPairs += LambdaPair(cond, f1, f2, closuresEqual)

  /** Whether the query has lambdas whose equality a model must not assume (see [[lambdaDistinctions]]). */
  protected def hasLambdaPairs: Boolean = lambdaPairs.nonEmpty

  /** The literals under which the model checks keep apart the lambdas that a model made equal.
    *
    * A pending distinguishing input lets the model checks assume that two functions are equal (see
    * [[witnessEqualities]]). That is a valid model when one of them is free, which can be taken to
    * be the other, but two lambdas of the program that differ in structure (or in closures) are
    * only equal if they agree on every input, which neither the unfolding nor the distinguishing
    * input establishes: the input only tells distinct functions apart. Models that make such
    * lambdas equal are therefore rejected, and the model checks then assume them distinct through
    * these literals (see [[distinguishLambdas]]). Like the equalities, they are only assumed by
    * the model checks, so a query that is only satisfiable with such lambdas equal remains unknown,
    * and the refutations are unchanged. */
  protected def lambdaDistinctions: Set[Encoded] = distinctLambdas.toSet.map(_._2)

  /** The pairs of lambdas that the model, given by `holds`, makes equal although their equality
    * doesn't follow from their structure, and that aren't kept apart yet. */
  protected def equatedLambdas(holds: Encoded => Boolean): Seq[LambdaPair] =
    lambdaPairs.toSeq.filter { p =>
      !distinctLambdas.contains(p) && holds(p.cond) && holds(mkEquals(p.f1, p.f2)) && !p.closuresEqual.exists(holds)
    }

  /** Keeps the lambdas of `pairs` apart in the following model checks (see [[lambdaDistinctions]]). */
  protected def distinguishLambdas(pairs: Seq[LambdaPair]): Clauses = pairs.flatMap { p =>
    val literal = encodeSymbol(Variable.fresh("b_neq", BooleanType(), true))
    distinctLambdas += p -> literal
    val distinct = mkNot(mkEquals(p.f1, p.f2))
    Rule.Hypothesis(literal, p.cond, p.closuresEqual.fold(distinct)(mkOr(distinct, _))).clauses
  }

  /** The equality literals of the pending distinguishing inputs, along with their depth.
    *
    * Distinguishing inputs are unfolded progressively, much like function calls: once it has found
    * a model, the solver assumes that the pairs of functions that don't have a distinguishing input
    * yet are equal. A model under these assumptions needs no more distinguishing inputs, and if they
    * make the formula unsatisfiable, the solver instantiates the ones whose equalities are in the
    * unsat core (see [[instantiateWitnesses]]). This keeps distinguishing inputs away from unsatisfiable
    * queries and from the pairs of functions that a model can keep equal.
    *
    * To stay fair with the rest of the unfolding, the solver only instantiates distinguishing inputs
    * up to a depth that grows by one with each unrolling. Each round stays finite: the free functions
    * and lambdas a distinguishing input creates on the spot inherit its depth, and the others are only
    * created by later unrollings. */
  protected def witnessEqualities: Map[Encoded, Int] =
    VectorMap.from(pendingWitnesses.toSeq.filterNot(_.onDemand).map(w => w.equality -> w.depth))

  /** The pending distinguishing inputs that are only unfolded when model extraction needs them,
    * as the compared functions and the equality literal to instantiate them with.
    *
    * Without function equality, whether two lambdas of the program are equal can't be observed, so
    * their equality is left open. Their distinguishing input is only needed when an extracted function
    * must tell them apart, and instantiating it for every pair of lambdas can make queries much harder.
    * Pairs that involve a free function are on demand as well unless equality is extensional (see
    * [[UnfoldingModes.onDemandFreeWitnesses]]), and join the regular unfolding once a model shows them. */
  protected def onDemandWitnesses: Seq[(FunctionType, (Encoded, Encoded, Encoded, Int))] =
    pendingWitnesses.toSeq.filter(_.onDemand).map(w => w.tpe -> (w.f1, w.f2, w.equality, w.depth))

  /** Turns the on-demand distinguishing inputs with the given equality literals into regular ones,
    * which are unfolded through their equality (see [[witnessEqualities]]). */
  protected def promoteWitnesses(equalities: Set[Encoded]): Clauses = {
    pendingWitnesses.toSeq.filter(w => w.onDemand && equalities(w.equality)).flatMap { w =>
      pendingWitnesses -= w
      pendingWitnesses += w.copy(onDemand = false)
      Rule.Hypothesis(w.equality, w.cond, mkEquals(w.f1, w.f2)).clauses
    }
  }

  /** Instantiates the pending distinguishing inputs with the given equality literals. */
  protected def instantiateWitnesses(equalities: Set[Encoded]): Clauses = {
    pendingWitnesses.toSeq.filter(w => equalities(w.equality)).sortBy(_.depth).flatMap { w =>
      pendingWitnesses -= w
      withWitnessDepth(w.depth)(instantiateWitness(w.cond, w.tpe, w.f1, w.f2))
    }
  }

  /** Whether `e` is the argument of a distinguishing input (see [[Templates.instantiateWitness]]). */
  protected def isWitnessArgument(e: Encoded): Boolean = witnessArguments(e)

  /** The instantiated distinguishing inputs, as the arguments on which each pair of functions
    * is compared (see [[Templates.instantiateWitness]]). */
  protected def distinguishingInputs: Seq[((Encoded, Encoded), (FunctionType, Seq[Encoded]))] = witnessInputs.toSeq

  /** Records that the function `f` was introduced at the current witness depth. */
  private[unrolling] def recordFunctionDepth(f: Encoded): Unit =
    if (witnessDepth > 0) witnessDepths += f -> witnessDepth

  /** Records that the application `app` was registered at the current witness depth. */
  private[unrolling] def recordAppDepth(app: App): Unit =
    if (witnessDepth > 0) appDepths += app -> (witnessDepth max appDepths.getOrElse(app, 0))

  /** The witness depth at which the function `f` was introduced. */
  private[unrolling] def functionDepth(f: Encoded): Int = witnessDepths.getOrElse(f, 0)

  /** The witness depth at which the application `app` was registered. */
  private[unrolling] def appDepth(app: App): Int = appDepths.getOrElse(app, 0)

  /** The free functions of type `ft` that need distinguishing inputs with the other functions of
    * their type, with the conditions under which they are free. */
  private[unrolling] def witnessedFunctions(ft: FunctionType): Set[(Encoded, Encoded)] = witnessFunctions(ft)

  /** Registers the free function `f` of type `ft`, which is free under `guard`, as needing
    * distinguishing inputs with the other functions of its type. */
  private[unrolling] def registerWitnessedFunction(ft: FunctionType, guard: Encoded, f: Encoded): Unit =
    witnessFunctions += ft -> (witnessFunctions(ft) + (guard -> f))

  /** Records the distinguishing input `ws` of type `tpe` of the functions `f1` and `f2`. */
  private[unrolling] def recordDistinguishingInput(f1: Encoded, f2: Encoded, tpe: FunctionType, ws: Seq[Encoded]): Unit = {
    witnessArguments ++= ws
    witnessInputs += (f1 -> f2) -> (tpe, ws)
  }

  protected case class LambdaPair(cond: Encoded, f1: Encoded, f2: Encoded, closuresEqual: Option[Encoded])

  protected case class PendingWitness(
    cond: Encoded, tpe: FunctionType, f1: Encoded, f2: Encoded, depth: Int, equality: Encoded, onDemand: Boolean)

  private[unrolling] object witnessState extends IncrementalStateWrapper {
    /** This mapping maintains the set of free functions (along with the condition under which
      * they are free) which require distinguishing inputs with other functions of the same type.
      * @see [[Templates.instantiateWitness]]
      */
    private[WitnessTemplates] val witnessFunctions = new IncrementalMap[FunctionType, Set[(Encoded, Encoded)]].withDefaultValue(ListSet.empty)

    /** Witness nesting depth of the free functions that were introduced as distinguishing inputs. */
    private[WitnessTemplates] val witnessDepths = new IncrementalMap[Encoded, Int]

    /** Witness nesting depth of the applications that were registered while instantiating distinguishing inputs. */
    private[WitnessTemplates] val appDepths = new IncrementalMap[App, Int]

    /** The witness arguments of the instantiated distinguishing inputs. */
    private[WitnessTemplates] val witnessArguments = new IncrementalSet[Encoded]

    /** The type and arguments of the distinguishing input of each pair of functions that received one. */
    private[WitnessTemplates] val witnessInputs = new IncrementalMap[(Encoded, Encoded), (FunctionType, Seq[Encoded])]

    /** The distinguishing inputs that haven't been instantiated yet. */
    private[WitnessTemplates] val pendingWitnesses = new IncrementalSet[PendingWitness]

    /** The pairs of lambdas whose equality a model must not assume (see [[registerLambdaPair]]). */
    private[WitnessTemplates] val lambdaPairs = new IncrementalSet[LambdaPair]

    /** The pairs of lambdas that the model checks keep apart, with the literal under which they do. */
    private[WitnessTemplates] val distinctLambdas = new IncrementalMap[LambdaPair, Encoded]

    val incrementals: Seq[IncrementalState] =
      Seq(witnessFunctions, witnessDepths, appDepths, witnessArguments, witnessInputs, pendingWitnesses,
        lambdaPairs, distinctLambdas)
  }
}
