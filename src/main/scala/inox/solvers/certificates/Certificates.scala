/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package certificates

/** Has the solvers that can produce proofs do so: the unrolling solver logs the rules that it
  * applies, and cvc5 runs with proofs. Proof production slows the solver down from its first
  * assertion, so that it is set only where proofs will be asked for: Inox sets it for an input
  * that asks for a proof (see [[Main]]). */
object optProduceProofs extends FlagOptionDef("produce-proofs", false)

object Certificates {
  /** What the unrolling solver checked in a refutation, in its terms `E`: the clauses that it
    * asserted and the assumptions of the check that answered unsat, in the order of the asserts
    * of the solver's session, the rules that gave the clauses, and the templates that they
    * instantiate, which a rule names by their index. */
  final case class Refutation[E](clauses: Seq[E], assumptions: Seq[E], templates: Seq[TemplateClauses[E]], rules: Seq[AppliedRule[E]])

  /** A template: its start blocker and arguments, and its clauses. */
  final case class TemplateClauses[E](params: Seq[E], clauses: Seq[E])

  /** A rule that the solver applied (see [[unrolling.RuleKernel]]): its kind, its clauses, and
    * when they are an instance of the clauses of a template, the instance. */
  final case class AppliedRule[E](kind: String, instance: Option[Instance[E]], clauses: Seq[E])

  /** Terms as the solver's session prints them, and the declarations that printing them made. */
  final case class Printed(terms: Seq[SExpr], declarations: Seq[SExpr])

  /** The certificate that a solver's session has no model, which the unrolling solver checked and
    * the solver proved with `proof`, where the asserts of the session are the clauses and then
    * the assumptions of `refutation`, or why there is none. It prints as:
    * {{{
    * (certificate
    * (script
    * <the SMT-LIB script that asserts the clauses, then the assumptions>
    * )
    * (templates
    * (script
    * <the SMT-LIB script that asserts the clauses of the templates, after the declarations of the script>
    * )
    * (<index> (params <its start blocker and arguments>) <the indices of the asserts of its clauses>)
    * ...)
    * (rules
    * (<kind> <the indices of the asserts of its clauses>)
    * (<kind> (instance <template index> ((<template symbol> <value>) ...)) <the indices>)
    * ...)
    * (assumptions <the indices of the asserts of the assumptions>)
    * (cpc
    * <the solver's CPC proof that the script has no model>
    * ))
    * }}}
    * The values of an instance's symbols are those of the template's start blocker and arguments,
    * then of the fresh symbols that replace its other symbols. `print` prints terms in the
    * solver's session.
    *
    * The proof's assumptions are the script's asserts. A checker checks that each template is
    * the template of its function, that each rule is an instance of its kind for the program,
    * that its clauses are the asserts it names, that every assert is named, and the proof. */
  def certificate[E](proof: ScriptProof, refutation: Refutation[E], print: Seq[E] => Printed): Either[String, Certificate] = {
    val Refutation(clauses, assumptions, templates, rules) = refutation
    val asserts = proof.asserts.size
    if (asserts != clauses.size + assumptions.size) {
      Left(s"the solver's session has $asserts asserts, for ${clauses.size} clauses and ${assumptions.size} assumptions")
    } else try {
      // a clause may be asserted several times
      val index = clauses.zipWithIndex.foldLeft(Map[E, Seq[Int]]()) {
        case (m, (e, i)) => m + (e -> (m.getOrElse(e, Seq()) :+ i))
      }
      def names(es: Seq[E]): Seq[Int] = es.flatMap(index).distinct

      // all terms are printed at once, along with the declarations that they need
      val values = rules.flatMap(_.instance.toSeq.flatMap(_.values))
      val Printed(terms, declarations) = print(templates.flatMap(t => t.params ++ t.clauses) ++ values.flatMap(v => Seq(v.symbol, v.value)))
      val it = terms.iterator

      val templateAsserts = scala.collection.mutable.ListBuffer[SExpr]()
      val templateSeq = templates.map { t =>
        val ps = t.params.map(_ => it.next())
        val first = templateAsserts.size
        templateAsserts ++= t.clauses.map(_ => SList(Seq(Atom("assert"), it.next())))
        Template(ps, first until templateAsserts.size)
      }
      val ruleSeq = rules.map { r =>
        Rule(r.kind, r.instance.map(i => Instance(i.template, i.values.map(_ => Value(it.next(), it.next())))), names(r.clauses))
      }
      Right(Certificate(proof, declarations ++ templateAsserts, templateSeq, ruleSeq, clauses.size until asserts))
    } catch {
      case e: Throwable if !e.isInstanceOf[VirtualMachineError] =>
        Left(s"the templates can't be printed in SMT-LIB (${e.getMessage})")
    }
  }

  /** The CPC proof that cvc5 answers to `(get-proof)`, or why it isn't one that checkers accept. */
  def cpc(answer: String): Either[String, Seq[SExpr]] = SExpr.parse(answer) match {
    case Left(why) => Left(s"cvc5's proof can't be read ($why)")
    case Right(Seq(SList(Atom("error") +: _))) => Left(s"cvc5 answered: ${answer.take(200)}")
    // cvc5 wraps the proof in parentheses, which the checkers don't accept
    case Right(Seq(SList(steps))) =>
      def trusted(step: SExpr): Boolean = step match {
        case SList(items) => items.sliding(2).exists { case Seq(Atom(":rule"), Atom("trust")) => true; case _ => false }
        case _ => false
      }
      if (steps.exists(trusted)) Left("cvc5's proof has trusted steps") else Right(steps)
    case _ => Left(s"cvc5 answered: ${answer.take(200)}")
  }
}
