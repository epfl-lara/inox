/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

/** The view of the templates that the solver loop and model extraction have (see
  * [[AbstractUnrollingSolver]]), in five groups. Each facade only delegates, and the members it
  * delegates to are protected, so the solver depends on the templates through these and the
  * encoding primitives (`mkEncoder`, `mkApp`, `mkEquals`, `extractNot`, `push`, `pop`, `reset`).
  */
trait SolverFacades { self: Templates =>
  import program.trees._

  /** Unfolding: instantiating the query, and unrolling the blocked items. */
  object unfolding {
    /** Whether a manager has items left to unroll. */
    def canUnroll: Boolean = self.canUnroll

    /** Unrolls the items of the next generation, and returns their clauses. */
    def unroll: Clauses = self.unroll

    /** The negations of the blockers of the items left to unroll, which a model must satisfy. */
    def satisfactionAssumptions: Seq[Encoded] = self.satisfactionAssumptions

    /** The literals that the refutation checks assume (see [[Manager.refutationAssumptions]]). */
    def refutationAssumptions: Seq[Encoded] = self.refutationAssumptions

    /** Moves the items that `b` blocks (and, under `force`, those below it) to the current
      * generation, so that the next unrolling unfolds them. */
    def promoteBlocker(b: Encoded, force: Boolean = false): Boolean = self.promoteBlocker(b, force)

    /** The clauses of the expression `expr`, which the solver asserts. */
    def instantiateExpr(expr: Expr, bindings: Map[Variable, Encoded]): Clauses =
      self.instantiateExpr(expr, bindings)

    /** The clauses of the free variable `v`, the first time it is declared. */
    def instantiateVariable(v: Variable, bindings: Map[Variable, Encoded]): Clauses =
      self.instantiateVariable(v, bindings)
  }

  /** The congruences of calls, which the models of the proof checks call for (see
    * [[FunctionTemplates.modelCongruences]]). */
  object congruences {
    def hasWaiting: Boolean = self.hasWaitingCongruences

    /** @see [[FunctionTemplates.modelCongruences]] */
    def ofModel(holds: Encoded => Boolean): Clauses = self.modelCongruences(holds)
  }

  /** The distinguishing inputs of first-class functions (see [[WitnessTemplates]]). */
  object witnesses {
    /** @see [[WitnessTemplates.witnessEqualities]] */
    def equalities: Map[Encoded, Int] = self.witnessEqualities

    /** @see [[WitnessTemplates.onDemandWitnesses]] */
    def onDemand: Seq[(FunctionType, (Encoded, Encoded, Encoded, Int))] = self.onDemandWitnesses

    /** @see [[WitnessTemplates.promoteWitnesses]] */
    def promote(equalities: Set[Encoded]): Clauses = self.promoteWitnesses(equalities)

    /** @see [[WitnessTemplates.hasLambdaPairs]] */
    def hasLambdaPairs: Boolean = self.hasLambdaPairs

    /** @see [[WitnessTemplates.lambdaDistinctions]] */
    def distinctions: Set[Encoded] = self.lambdaDistinctions

    /** A pair of lambdas whose equality a model must justify (see [[WitnessTemplates.lambdaDistinctions]]). */
    type LambdaPair = self.LambdaPair

    /** @see [[WitnessTemplates.equatedLambdas]] */
    def equatedLambdas(holds: Encoded => Boolean): Seq[LambdaPair] = self.equatedLambdas(holds)

    /** @see [[WitnessTemplates.nextRound]] */
    def nextRound(): Seq[LambdaPair] = self.nextRound()

    /** @see [[WitnessTemplates.lambdaComparison]] */
    def comparison(p: LambdaPair): (Encoded, Seq[Encoded], Clauses) = self.lambdaComparison(p)

    /** The argument types of the lambdas of `p`. */
    def argumentTypes(p: LambdaPair): Seq[Type] = p.t1.tpe.from

    /** @see [[WitnessTemplates.lambdaCaptures]] */
    def captures(p: LambdaPair): Seq[(Encoded, Type)] = self.lambdaCaptures(p)

    /** @see [[WitnessTemplates.fixCaptures]] */
    def fixCaptures(captures: Seq[Encoded], values: Seq[Expr]): (Encoded, Clauses) = self.fixCaptures(captures, values)

    /** @see [[WitnessTemplates.markEqualLambdas]] */
    def markEqual(p: LambdaPair): Unit = self.markEqualLambdas(p)

    /** @see [[WitnessTemplates.keepApart]] */
    def keepApart(p: LambdaPair): Clauses = self.keepApart(p)

    /** @see [[WitnessTemplates.wasProbed]] */
    def wasProbed(p: LambdaPair): Boolean = self.wasProbed(p)

    /** @see [[WitnessTemplates.probeLambdas]] */
    def probe(p: LambdaPair, args: Seq[Expr]): Clauses = self.probeLambdas(p, args)

    /** @see [[WitnessTemplates.instantiateWitnesses]] */
    def instantiate(equalities: Set[Encoded]): Clauses = self.instantiateWitnesses(equalities)

    /** @see [[WitnessTemplates.distinguishingInputs]] */
    def distinguishingInputs: Seq[((Encoded, Encoded), (FunctionType, Seq[Encoded]))] = self.distinguishingInputs

    /** @see [[WitnessTemplates.isWitnessArgument]] */
    def isArgument(e: Encoded): Boolean = self.isWitnessArgument(e)
  }

  /** The quantifiers of the query, and the checks that a model satisfies them (see
    * [[QuantificationTemplates]]). */
  object quantifiers {
    def hasAxioms: Boolean = self.hasAxioms
    def axioms: Seq[Axiom] = self.getAxioms

    /** Whether a model must be checked against the quantifiers before it is accepted. */
    def requiresFiniteRangeCheck: Boolean = self.requiresFiniteRangeCheck

    /** The clauses that hold when the quantifiers have all their instantiations. */
    def finiteRangeClauses: Clauses = self.getFiniteRangeClauses

    def hasInstantiationsWithBlockers: Boolean = self.hasInstantiationsWithBlockers
    def instantiationsWithBlockers: Seq[(Encoded, Set[Encoded])] = self.getInstantiationsWithBlockers

    /** Whether some instantiations are deferred to a later generation. */
    def hasPendingInstantiations: Boolean = quantificationsManager.unrollGeneration.isDefined

    /** Moves the deferred instantiations to the current generation. */
    def promote(): Unit = self.promoteQuantifications
  }

  /** What model extraction needs to read back the values of the model. */
  object model {
    /** The templates of all the lambdas that have been unrolled. */
    def lambdaTemplates: Seq[LambdaTemplate] = self.getLambdaTemplates

    /** The templates of the lambdas of type `tpe` that have been unrolled. */
    def lambdaTemplates(tpe: FunctionType): Set[LambdaTemplate] = self.getLambdaTemplates(tpe)

    /** The matchers of type `tpe`, as their blocker and arguments (@see
      * [[QuantificationTemplates.getGroundInstantiations]]). */
    def groundInstantiations(e: Encoded, tpe: Type): Seq[(Encoded, Seq[Encoded])] =
      self.getGroundInstantiations(e, tpe)

    /** @see [[PartialFunctions.appFailureLiterals]] */
    def appFailureLiterals(tpe: FunctionType): Seq[((Encoded, Seq[Encoded]), Encoded)] =
      self.appFailureLiterals(tpe)

    /** @see [[TemplateGenerator.uninterpretedFunctions]] */
    def uninterpretedFunctions: scala.collection.Map[(Identifier, Seq[Type]), (Variable, Encoded)] =
      self.uninterpretedFunctions

    /** @see [[TemplateGenerator.uninterpretedConstants]] */
    def uninterpretedConstants: scala.collection.Set[(Identifier, Seq[Type])] = self.uninterpretedConstants

    /** @see [[TemplateGenerator.uninterpretedTypes]] */
    def uninterpretedTypes: scala.collection.Map[(Identifier, Seq[Type]), Type] = self.uninterpretedTypes

    /** The type parameters of the query, with their flags (@see [[TypeTemplates.storeTypeParameter]]). */
    def typeParameterFlags: Seq[(TypeParameter, Encoded)] = typesManager.typeParameterFlags

    /** @see [[LambdaTemplates.equalCaptures]] */
    def equalCaptures: Seq[(Encoded, Encoded, Encoded)] = self.equalCaptures

    /** @see [[LambdaTemplates.relateCapture]] */
    def relateCapture(lambda: Encoded, f: Encoded): Clauses = self.relateCapture(lambda, f)
  }
}
