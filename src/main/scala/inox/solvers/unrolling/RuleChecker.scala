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

  /** The rule applications in progress, innermost first, each with the clauses that the generator
    * gave for its instantiation. */
  private var instantiations: List[(Rule, scala.collection.mutable.ListBuffer[Encoded])] = Nil

  private def fail(msg: String): Nothing = throw new RuleCheckFailure(msg)

  /** Whether the rules that the solver applies are logged (see [[logged]]), such as for the
    * certificates of its answers (see [[certificates.Certificates]]). */
  protected def loggingRules: Boolean = false

  /** Called, when [[loggingRules]], with each rule application of kind `kind`, its arguments (see
    * [[Rule.arguments]]) and the clauses that it builds: for [[Rule.Unfold]] and [[Rule.Instance]],
    * the clauses that the generator gave for `template`, the instantiated template contents with
    * the values of their symbols. */
  protected def logged(kind: String, arguments: Seq[(String, Seq[Encoded])],
                       template: Option[(TemplateContents, Map[Encoded, Encoded])], clauses: Clauses): Unit = ()

  /** Called, when [[loggingRules]], with a template that is instantiated outside of a rule, which
    * the certificate of an answer can't account for. */
  protected def unruled(clauses: Clauses): Unit = ()

  private def tracking: Boolean = checkingRules || loggingRules

  /** The clauses that `build` builds for `rule`, which are recorded as its clauses. */
  private[unrolling] def applying(rule: Rule)(build: => Clauses): Clauses = if (!tracking) build else {
    val generated = scala.collection.mutable.ListBuffer.empty[Encoded]
    instantiations = (rule -> generated) :: instantiations
    val clauses = try build finally instantiations = instantiations.tail

    rule match {
      case _: Rule.Unfold | _: Rule.Instance => // logged as they are generated
      case _ => if (loggingRules && clauses.nonEmpty) logged(rule.productPrefix, rule.arguments, None, clauses)
    }

    if (checkingRules) {
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
    }

    clauses
  }

  /** The clauses that the generator gave for `contents`, substituted with `subst`, which give the
    * values of their start blocker and arguments and the fresh symbols that replace their other
    * symbols, and which the innermost rule application instantiates. */
  private[unrolling] def generated(contents: TemplateContents, subst: Map[Encoded, Encoded], clauses: Clauses): Clauses = {
    if (tracking) instantiations match {
      case (rule, gen) :: _ =>
        gen ++= clauses
        if (loggingRules && clauses.nonEmpty) logged(rule.productPrefix, rule.arguments, Some(contents -> subst), clauses)
      case Nil =>
        if (checkingRules) fail("A template is instantiated outside of a rule: " + clauses.map(asString).mkString(", "))
        if (loggingRules && clauses.nonEmpty) unruled(clauses)
    }
    clauses
  }

  /** Records the open conjunction or disjunction `junction`, whose `rest` may be fresh. */
  private[unrolling] def declared(junction: OpenJunction[?]): Unit =
    if (tracking && junction.assumedComplete == AssumedComplete.Always) {
      refutable += junction.completenessAssumption
    }

  /** Whether `assumption` is the completeness of an open conjunction or disjunction that the
    * refutation checks may assume (see [[OpenJunctions.AssumedComplete]]). The rules are tracked
    * when this is asked. */
  def assumedComplete(assumption: Encoded): Boolean = refutable(assumption)

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
