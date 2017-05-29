/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package tip

import smtlib.trees.Terms._
import smtlib.theories.Operations._

object Bags {

  private val BagInsert = "bag.insert"
  private val BagUnion = "bag.union"
  private val BagIntersection = "bag.intersection"
  private val BagEmpty = "bag.empty"
  private val BagSingleton = "bag.singleton"
  private val BagMultiplicity = "bag.multiplicity"
  private val BagDifference = "bag.difference"

  object BagSort {
    def apply(el: Sort): Sort = Sort(Identifier(SSymbol("Bag")), Seq(el))

    def unapply(sort: Sort): Option[Sort] = sort match {
      case Sort(Identifier(SSymbol("Bag"), Seq()), Seq(el)) => Some(el)
      case _ => None
    }
  }

  object EmptyBag {
    def apply(s: Sort): Term = QualifiedIdentifier(Identifier(SSymbol(BagEmpty)), Some(s))
    def unapply(t: Term): Option[Sort] = t match {
      case QualifiedIdentifier(Identifier(SSymbol(BagEmpty), Seq()), Some(s)) => Some(s)
      case _ => None
    }
  }

  object Singleton extends Operation2 { override val name = BagSingleton }

  object Union extends Operation2 { override val name = BagUnion }
  object Intersection extends Operation2 { override val name = BagIntersection }
  object Difference extends Operation2 { override val name = BagDifference }
  object Multiplicity extends Operation2 { override val name = BagMultiplicity }
  object Insert extends OperationN2 { override val name = BagInsert }
}
