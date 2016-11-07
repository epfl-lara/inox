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

  val List = mkSort(listID)("A")(Seq(consID, nilID))
  val Nil  = mkConstructor(nilID)("A")(Some(listID))(_ => Seq.empty)
  val Cons = mkConstructor(consID)("A")(Some(listID)) {
    case Seq(aT) => Seq(ValDef(head, aT), ValDef(tail, List(aT)))
  }


  val optionID = FreshIdentifier("Option")
  val someID   = FreshIdentifier("Some")
  val noneID   = FreshIdentifier("None")

  val v = FreshIdentifier("value")

  val option = mkSort(optionID)("A")(Seq(someID, noneID))
  val none   = mkConstructor(noneID)("A")(Some(optionID))(_ => Seq.empty)
  val some   = mkConstructor(someID)("A")(Some(optionID)) {
    case Seq(aT) => Seq(ValDef(v, aT))
  }

  val baseSymbols = NoSymbols.withADTs(Seq(List, Nil, Cons, option, none, some))
}
