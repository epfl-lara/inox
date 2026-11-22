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
  /** A solver whose session prints terms of Inox trees, as the certificates of an unrolling
    * solver over it need for the terms that its session doesn't have. */
  trait SessionPrinter {
    /** `es` as terms of the session, and the declarations of their symbols that printing them made. */
    def printed(es: Seq[inox.trees.Expr]): Printed
  }

  /** Terms as the solver's session prints them, and the declarations that printing them made. */
  final case class Printed(terms: Seq[SExpr], declarations: Seq[SExpr])

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
