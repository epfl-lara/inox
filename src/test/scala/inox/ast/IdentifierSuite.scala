/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package ast

import org.scalatest.funsuite.AnyFunSuite

class IdentifierSuite extends AnyFunSuite {

  test("Canonical identifiers are the same in every process and never fresh") {
    val canonical = (0 until 10).map(FreshIdentifier.canonical)
    assert(canonical == (0 until 10).map(FreshIdentifier.canonical))
    assert(canonical.map(id => (id.name, id.globalId, id.id)) == (0 until 10).map(i => ("x", -1 - i, i)))
    assert(canonical.distinct.size == 10)
    val fresh = Seq.fill(10)(FreshIdentifier("x"))
    assert(fresh.forall(id => !canonical.contains(id)))
    assertThrows[IllegalArgumentException](FreshIdentifier.canonical(-1))
  }

  test("Subclasses extend an existing identifier") {
    class Tagged(base: Identifier, val tag: String) extends Identifier(base, false)
    val base = FreshIdentifier("t")
    val tagged = new Tagged(base, "tag")
    assert(tagged == base && tagged.hashCode == base.hashCode)
    assert((tagged.name, tagged.globalId, tagged.id) == (base.name, base.globalId, base.id))
  }
}
