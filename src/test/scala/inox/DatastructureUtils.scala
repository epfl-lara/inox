/* Copyright 2009-2016 EPFL, Lausanne */

package inox

trait DatastructureUtils {
  import trees._
  import dsl._

  val listID = FreshIdentifier("List")
  val consID = FreshIdentifier("Cons")
  val nilID  = FreshIdentifier("Nil")

  val head = FreshIdentifier("head")
  val tail = FreshIdentifier("tail")

  val List = mkSort(listID)("A") {
    case Seq(aT) => Seq(
      (nilID, Seq()),
      (consID, Seq(ValDef(head, aT), ValDef(tail, T(listID)(aT))))
    )
  }


  val optionID = FreshIdentifier("Option")
  val someID   = FreshIdentifier("Some")
  val noneID   = FreshIdentifier("None")

  val v = FreshIdentifier("value")

  val option = mkSort(optionID)("A") {
    case Seq(aT) => Seq(
      (noneID, Seq()),
      (someID, Seq(ValDef(v, aT)))
    )
  }

  val baseSymbols = NoSymbols.withSorts(Seq(List, option))
}
