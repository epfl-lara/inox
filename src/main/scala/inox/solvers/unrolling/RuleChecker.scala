/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

/** Checks the clauses and the assumptions of the unrolling against the rule kernel as it runs (see
  * [[RuleChecker]]). This is meant for tests: it records every clause that the rules build. */
object optCheckRules extends FlagOptionDef("check-rules", false)

/** What [[RuleChecker]] reports. Unlike the errors of the solver, it doesn't turn into an `Unknown`
  * answer, so a test that runs into it fails. */
class RuleCheckFailure(msg: String) extends Exception(msg)

/** Checks, while the solver runs, what the soundness of its proofs relies on (see [[RuleKernel]]):
  *  - every clause that the solver asserts is built by a rule. For [[Rule.Unfold]] and
  *    [[Rule.Instance]], these are the clauses that the generator gave for the template, once
  *    substituted, while the clauses of the items of the instantiation come from rules of their own.
  *    A template that is instantiated outside a rule fails the check right away;
  *  - each fresh symbol that a rule introduces, the literal of a [[Rule.Define]] or of a
  *    [[Rule.Hypothesis]], or the root blocker of a [[Rule.Root]], is introduced by one rule
  *    application only, as their arguments require;
  *  - every check whose unsatisfiable answer the solver returns only assumes the assumptions of
  *    the query and the completeness of the open conjunctions and disjunctions that refutations may
  *    assume (see [[OpenJunctions.AssumedComplete]]), and has no clauses that only restrict its
  *    models, such as those of the finite range check.
  *
  * These are the properties whose arguments span several places in the code. It doesn't build the
  * clauses of each rule a second time: [[Rule.clauses]] states each one in a line, and a second copy
  * would only repeat it. The solver calls it when [[optCheckRules]] is set, and the tests set it. */
trait RuleChecker { self: Templates =>
  import context.{given, _}

  /** Whether the rules are checked (see [[optCheckRules]]). */
  lazy val checkingRules: Boolean = options.findOptionOrDefault(optCheckRules)

  private[unrolling] object ruleCheckerState extends IncrementalStateWrapper {
    /** The clauses that the rules built. */
    private[RuleChecker] val built = new IncrementalSet[Encoded]

    /** The fresh symbols that the rules introduced, with the name of the rule. */
    private[RuleChecker] val introduced = new IncrementalMap[Encoded, String]

    /** The completeness assumptions that the refutation checks may make. */
    private[RuleChecker] val refutable = new IncrementalSet[Encoded]

    val incrementals: Seq[IncrementalState] = Seq(built, introduced, refutable)
  }

  import ruleCheckerState._

  /** The clauses that the generator gave for the instantiations in progress, innermost first. */
  private var instantiations: List[scala.collection.mutable.ListBuffer[Encoded]] = Nil

  private def fail(msg: String): Nothing = throw new RuleCheckFailure(msg)

  /** The clauses that `build` builds for `rule`, which are recorded as its clauses. */
  private[unrolling] def applying(rule: Rule)(build: => Clauses): Clauses = if (!checkingRules) build else {
    val generated = scala.collection.mutable.ListBuffer.empty[Encoded]
    instantiations = generated :: instantiations
    val clauses = try build finally instantiations = instantiations.tail

    built ++= (rule match {
      case _: Rule.Unfold | _: Rule.Instance => generated
      case _ => clauses
    })

    val symbol = rule match {
      case Rule.Define(_, literal, _) => Some(literal)
      case Rule.Hypothesis(literal, _, _) => Some(literal)
      case Rule.Root(start) => Some(start)
      case _ => None
    }

    for (s <- symbol) introduced.get(s) match {
      case Some(other) =>
        fail(s"${asString(s)} is introduced by both a ${other} and a ${rule.productPrefix} rule")
      case None =>
        introduced += s -> rule.productPrefix
    }

    clauses
  }

  /** The substituted clauses that the generator gave for a template, which the innermost rule
    * application instantiates. */
  private[unrolling] def generated(clauses: Clauses): Clauses = {
    if (checkingRules) instantiations match {
      case gen :: _ => gen ++= clauses
      case Nil => fail("A template is instantiated outside of a rule: " + clauses.map(asString).mkString(", "))
    }
    clauses
  }

  /** Records the open conjunction or disjunction `junction`, whose `rest` may be fresh. */
  private[unrolling] def declared(junction: OpenJunction[?]): Unit =
    if (checkingRules && junction.assumedComplete == AssumedComplete.Always) {
      refutable += junction.completenessAssumption
    }

  /** Checks that `clause`, which the solver asserts for good, is built by a rule. */
  def checkAsserted(clause: Encoded): Unit =
    if (checkingRules && !built(clause)) fail("The solver asserts a clause that no rule built: " + asString(clause))

  /** Checks that the check that gave an unsatisfiable answer may refute the query: it assumed
    * `assumptions`, if it had no clauses of its own, and the query assumes `allowed`. */
  def checkRefutation(assumptions: Option[Iterable[Encoded]], allowed: Set[Encoded]): Unit =
    if (checkingRules) assumptions match {
      case None =>
        fail("An unsatisfiable answer comes from a check with clauses that only restrict its models")
      case Some(as) =>
        for (a <- as if !allowed(a) && !refutable(a)) {
          fail("An unsatisfiable answer relies on " + asString(a) + ", which refutations don't assume")
        }
    }
}
