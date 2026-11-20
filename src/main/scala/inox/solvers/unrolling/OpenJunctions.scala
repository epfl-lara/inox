/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

/** Conjunctions and disjunctions whose operands the unrolling discovers over time.
  *
  * An [[OpenAnd]] stands for `op1 ∧ ... ∧ opN ∧ rest`, and an [[OpenOr]] for `op1 ∨ ... ∨ opN ∨ rest`.
  * The operands found so far are explicit, and `rest` is a fresh literal that stands for the operands
  * still to come. Extending one defines its `rest` as the new operands and the `rest` of the [[next]] one.
  *
  * The managers never assert that an open conjunction or disjunction is complete. Assuming it is
  * complete means assuming that no operand is left: `rest` holds in an `OpenAnd` and doesn't in an
  * `OpenOr`. Each one declares in which checks that is assumed (see [[AssumedComplete]]), and the
  * managers derive their [[Manager.satisfactionAssumptions]] and [[Manager.refutationAssumptions]]
  * from it (see [[completenessAssumptions]]). Why that is sound is a property of each one, stated
  * where it is declared.
  */
trait OpenJunctions { self: Templates =>
  import program.trees._

  /** The checks that assume an open conjunction or disjunction has no operands left. */
  enum AssumedComplete {
    /** Only the model checks, where every operand left out must be ruled out. */
    case ForModels
    /** The model checks and the refutation checks. */
    case Always
  }

  /** An [[OpenAnd]] or an [[OpenOr]], whose operands so far are defined, and whose remaining operands
    * are the literal `rest`. Fresh `rest` literals are named `restName`. */
  sealed abstract class OpenJunction[J <: OpenJunction[J]] { this: J =>
    val restName: String
    val assumedComplete: AssumedComplete
    val rest: Encoded

    protected def join(operands: Seq[Encoded]): Encoded
    protected def withRest(rest: Encoded): J

    /** The literal that the checks assume when they assume no operand is left. */
    def completenessAssumption: Encoded

    /** The conjunction (or disjunction) of `operands` and `rest`, or `rest` alone when there are no operands. */
    def withOperands(operands: Seq[Encoded]): Encoded =
      if (operands.isEmpty) rest else join(operands :+ rest)

    /** The same conjunction (or disjunction) with a fresh `rest`, which [[link]] then defines. */
    def next: J = withRest(encodeSymbol(Variable.fresh(restName, BooleanType(), true)))

    /** The clause that defines `rest` as `operands` and the `rest` of `next`, under `guard` if there
      * is one (see [[Rule.Define]]). */
    def link(next: J, operands: Seq[Encoded], guard: Option[Encoded] = None): Clauses =
      Rule.Define(guard, rest, next.withOperands(operands)).clauses
  }

  /** A conjunction whose operands the unrolling discovers over time. */
  case class OpenAnd(restName: String, assumedComplete: AssumedComplete, rest: Encoded) extends OpenJunction[OpenAnd] {
    protected def join(operands: Seq[Encoded]): Encoded = mkAnd(operands*)
    protected def withRest(rest: Encoded): OpenAnd = copy(rest = rest)
    def completenessAssumption: Encoded = rest
  }

  object OpenAnd {
    /** An open conjunction with no operands yet, whose `rest` is a fresh literal named `restName`. */
    def apply(restName: String, assumedComplete: AssumedComplete): OpenAnd =
      OpenAnd(restName, assumedComplete, encodeSymbol(Variable.fresh(restName, BooleanType(), true)))
  }

  /** A disjunction whose operands the unrolling discovers over time. */
  case class OpenOr(restName: String, assumedComplete: AssumedComplete, rest: Encoded) extends OpenJunction[OpenOr] {
    protected def join(operands: Seq[Encoded]): Encoded = mkOr(operands*)
    protected def withRest(rest: Encoded): OpenOr = copy(rest = rest)
    def completenessAssumption: Encoded = mkNot(rest)
  }

  object OpenOr {
    /** An open disjunction with no operands yet, whose `rest` is a fresh literal named `restName`. */
    def apply(restName: String, assumedComplete: AssumedComplete): OpenOr =
      OpenOr(restName, assumedComplete, encodeSymbol(Variable.fresh(restName, BooleanType(), true)))
  }

  /** The completeness assumptions that a check makes: all of them in a model check, and only those
    * assumed [[AssumedComplete.Always]] in a refutation check. */
  protected def completenessAssumptions(junctions: Iterable[OpenJunction[?]], refuting: Boolean): Seq[Encoded] =
    junctions.toSeq
      .filter(j => !refuting || j.assumedComplete == AssumedComplete.Always)
      .map(_.completenessAssumption)
}
