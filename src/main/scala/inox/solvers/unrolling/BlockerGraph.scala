/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

import scala.collection.immutable.ListSet

/** The implications and equalities between the blockers of the unrolling: the condition variables
  * of instantiated templates, their start blockers and the conjunctions of blockers that
  * [[encodeBlockers]] introduces. The quantifier instantiation and the blocker promotion of the
  * solver follow these implications (see [[blockerPath]] and [[Templates.promoteBlocker]]).
  */
trait BlockerGraph { self: Templates =>
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  import blockerGraph._

  private[unrolling] object blockerGraph extends IncrementalStateWrapper {
    // implication tree that we're sure about: if  (b1, b2) is in the tree, then
    // we have the precise semantics of b1 ==> b2 in the resulting clause set
    private[BlockerGraph] val condImplies = new IncrementalMap[Encoded, Set[Encoded]].withDefaultValue(Set.empty)
    private[BlockerGraph] val condImplied = new IncrementalMap[Encoded, Set[Encoded]].withDefaultValue(Set.empty)

    // implication tree that isn't quite ensured in the resulting clause set
    // this can happen due to defBlocker caching in unrolling
    private[BlockerGraph] val potImplies = new IncrementalMap[Encoded, Set[Encoded]].withDefaultValue(Set.empty)
    private[BlockerGraph] val potImplied = new IncrementalMap[Encoded, Set[Encoded]].withDefaultValue(Set.empty)

    private[BlockerGraph] val condEquals  = new IncrementalBijection[Encoded, Set[Encoded]]

    val incrementals: Seq[IncrementalState] = Seq(condImplies, condImplied, potImplies, potImplied, condEquals)
  }

  protected def freshConds(
    pathVar: Encoded,
    condVars: Map[Variable, Encoded],
    tree: Map[Variable, Set[Variable]]): Map[Encoded, Encoded] = {

    val subst = condVars.map { case (v, idT) => idT -> encodeSymbol(v) }
    val mapping = condVars.view.mapValues(subst).toMap

    for ((parent, children) <- tree) {
      mapping.get(parent) match {
        case None => // enabling condition, corresponds to pathVar
          for (child <- children) {
            val ec = mapping(child)
            condImplies += pathVar -> (condImplies(pathVar) + ec)
            condImplied += ec -> (condImplied(ec) + pathVar)
          }

        case Some(ep) =>
          for (child <- children) {
            val ec = mapping(child)
            condImplies += ep -> (condImplies(ep) + ec)
            condImplied += ec -> (condImplied(ec) + ep)
          }
      }
    }

    subst
  }

  private val sym = Variable.fresh("bs", BooleanType(), true)
  protected def encodeBlockers(bs: Set[Encoded]): (Encoded, Clauses) = bs.toSeq.filter(_ != trueT) match {
    case Seq(b) if (
      condImplies.isDefinedAt(b) || condImplied.isDefinedAt(b) ||
      potImplies.isDefinedAt(b) || potImplied.isDefinedAt(b) ||
      condEquals.containsA(b)
    ) => (b, Seq.empty)

    case _ =>
      // the conjuncts keep the order of `bs` rather than hash order, so that the clause doesn't depend
      // on hash codes (see [[Items]])
      val flatBs: Set[Encoded] =
        fixpoint((bs: Set[Encoded]) => ListSet.from(bs.iterator.flatMap(b => condEquals.getBorElse(b, Set(b)))))(ListSet.from(bs))
      condEquals.getA(flatBs) match {
        case Some(b) => (b, Seq.empty)
        case None =>
          val b = encodeSymbol(sym)
          condEquals += (b -> flatBs)
          (b, Rule.Define(None, b, if (flatBs.isEmpty) trueT else mkAnd(flatBs.toSeq*)).clauses)
      }
  }

  protected def registerImplication(b1: Encoded, b2: Encoded): Unit = {
    potImplies += b1 -> (potImplies(b1) + b2)
    potImplied += b2 -> (potImplied(b2) + b1)
  }

  protected def blockerEquals(b: Encoded): Set[Encoded] = condEquals.getBorElse(b, Set.empty)

  protected def blockerParents(b: Encoded, strict: Boolean = true): Set[Encoded] = {
    condImplied(b) ++ (if (!strict) potImplied(b) else Set.empty)
  }

  protected def blockerChildren(b: Encoded, strict: Boolean = true): Set[Encoded] = {
    condImplies(b) ++ (if (!strict) potImplies(b) else Set.empty)
  }

  protected def blockerPath(b: Encoded): Set[Encoded] = blockerPath(Set(b))

  /* This set is guaranteed finite and won't expand beyond the limit of a function's
   * definition as aVar ==> defBlocker is NOT a strict implication (ie. won't be in
   * the condImplied map) */
  protected def blockerPath(bs: Set[Encoded]): Set[Encoded] = fixpoint((bs: Set[Encoded]) => bs.flatMap { b =>
    val equal = condEquals.getBorElse(b, Set.empty)
    if (equal.nonEmpty) equal else (condImplied(b) + b)
  })(bs).filter(_ != trueT)
}
