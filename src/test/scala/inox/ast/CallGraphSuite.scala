/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package ast

import org.scalatest.funsuite.AnyFunSuite

class CallGraphSuite extends AnyFunSuite {
  import inox.trees.{given, _}
  import dsl._

  val fID = FreshIdentifier("f")
  val gID = FreshIdentifier("g")
  val hID = FreshIdentifier("h")
  val kID = FreshIdentifier("k")
  val loneID = FreshIdentifier("lone")
  val lone2ID = FreshIdentifier("lone2")
  val mainID = FreshIdentifier("main")
  val invID = FreshIdentifier("inv")
  val boxID = FreshIdentifier("Box")
  val boxConsID = FreshIdentifier("BoxCons")
  val wrapID = FreshIdentifier("Wrap")
  val wrapConsID = FreshIdentifier("WrapCons")

  // f and g call each other, h calls itself, k calls nothing
  val f = mkFunDef(fID)() { _ => (Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) => E(gID)(x) }) }
  val g = mkFunDef(gID)() { _ => (Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) => E(fID)(x) }) }
  val h = mkFunDef(hID)() { _ => (Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) => E(hID)(x) }) }
  val k = mkFunDef(kID)() { _ => (Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) => x }) }
  // lone neither calls nor is called
  val lone = mkFunDef(loneID)() { _ => (Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) => x }) }
  val lone2 = mkFunDef(lone2ID)() { _ => (Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) => x }) }
  // main calls f and h and builds a Wrap
  val main = mkFunDef(mainID)() { _ => (Seq("x" :: IntegerType()), ADTType(wrapID, Seq()), {
    case Seq(x) => ADT(wrapConsID, Seq(), Seq(ADT(boxConsID, Seq(), Seq(E(fID)(x) + E(hID)(x)))))
  }) }
  // Box's invariant calls k, Wrap contains a Box
  val inv = mkFunDef(invID)() { _ => (Seq("b" :: ADTType(boxID, Seq())), BooleanType(), {
    case Seq(b) => E(kID)(b.getField(FreshIdentifier("v"))) >= E(BigInt(0))
  }) }
  val vID = FreshIdentifier("v")
  val box = new ADTSort(boxID, Seq(), Seq(new ADTConstructor(boxConsID, boxID, Seq(ValDef(vID, IntegerType())))), Seq(HasADTInvariant(invID)))
  val wrap = mkSort(wrapID)() { _ => Seq((wrapConsID, Seq(ValDef(FreshIdentifier("box"), ADTType(boxID, Seq()))))) }

  val invFixed = inv.copy(fullBody = E(kID)(ADTSelector(inv.params.head.toVariable, vID)) >= E(BigInt(0)))

  val symbols = NoSymbols.withFunctions(Seq(f, g, h, k, lone, lone2, main, invFixed)).withSorts(Seq(box, wrap))
  given Symbols = symbols

  test("Direct calls") {
    assert(symbols.calls(fID, gID) && symbols.calls(gID, fID) && !symbols.calls(fID, hID))
    assert(symbols.callees(mainID) == Set(fID, hID))
    assert(symbols.callers(fID) == Set(gID, mainID))
    assert(symbols.callees(main) == Set(f, h))
    assert(symbols.callers(Set(fID, hID)) == Set(gID, mainID, hID))
    assert(symbols.callees(Set(mainID, kID)) == Set(fID, hID))
    assert(symbols.allCalls.contains(mainID -> fID))
    assert(symbols.callers(f) == Set(g, main))
    assert(symbols.callers(Set(f, h)) == Set(g, main, h))
    assert(symbols.callees(Set(main, k)) == Set(f, h))
    assert(symbols.callers(loneID).isEmpty && symbols.callees(loneID).isEmpty)
  }

  test("Transitive calls") {
    assert(symbols.transitiveCallees(mainID) == Set(fID, gID, hID))
    assert(symbols.transitiveCallers(fID) == Set(fID, gID, mainID))
    assert(symbols.transitivelyCalls(main, g))
    assert(!symbols.transitivelyCalls(kID, kID))
    assert(symbols.transitiveCallees(Set(f, k)) == Set(f, g))
    assert(symbols.transitiveCallees(Set(mainID, kID)) == Set(fID, gID, hID))
    assert(symbols.transitiveCallers(g) == Set(f, g, main))
    assert(symbols.transitiveCallers(Set(gID, kID)) == Set(fID, gID, mainID, invID))
    assert(symbols.transitiveCallers(Set(h, k)) == Set(h, main, invFixed))
  }

  test("Recursion") {
    assert(symbols.isRecursive(fID) && symbols.isRecursive(gID) && symbols.isRecursive(hID))
    assert(!symbols.isRecursive(kID) && !symbols.isRecursive(mainID))
    assert(symbols.isSelfRecursive(hID) && !symbols.isSelfRecursive(fID))
  }

  test("Strongly connected components and their ordering") {
    assert(symbols.sccs.N.contains(Set(fID, gID)))
    assert(symbols.sccs.N.contains(Set(hID)))
    import symbols.CallGraphOrderings.given
    // callers come before their callees
    val sorted = Seq(f, h, g, main).sorted
    assert(sorted.head == main)
    assert(Seq(k, invFixed).sorted == Seq(invFixed, k))
    // functions outside of the call graph come first
    assert(Seq(main, lone).sorted == Seq(lone, main))
    val ordering = summon[Ordering[FunDef]]
    assert(ordering.compare(lone, main) < 0 && ordering.compare(main, lone) > 0)
    // functions outside of the call graph are sorted by name
    assert(ordering.compare(lone, lone2) == loneID.uniqueName.compare(lone2ID.uniqueName))
    assert(ordering.compare(lone, lone) == 0)
  }

  test("Dependencies of functions and sorts") {
    // main depends on the sorts it builds
    assert(symbols.dependsOn(mainID, wrapID) && symbols.dependsOn(mainID, boxID))
    assert(symbols.dependsOn(wrapID, boxID))
    // the invariant depends on its sort, but not the other way around: otherwise every
    // sort with an invariant would be mutually recursive with it, which Stainless rejects
    assert(symbols.dependsOn(invID, boxID) && symbols.dependsOn(invID, kID))
    assert(!symbols.dependsOn(boxID, invID))
    assert(symbols.dependencies(mainID) == Set(fID, gID, hID, wrapID, boxID))
    assert(!symbols.dependsOn(kID, boxID))
  }
}
