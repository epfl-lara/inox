/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

import org.scalatest._

import inox.trees._

class TreeTestsSuite extends FunSuite {

  test("And- and Or- simplifications") {

    //TODO dont like the fact that we need to create an empty program
    //     to get access to the and/or constructors
    val pgm = InoxProgram(Context.empty, Seq(), Seq())
    import pgm.symbols._

    val x = Variable.fresh("x", BooleanType)
    val y = Variable.fresh("y", BooleanType)
    val t = BooleanLiteral(true)
    val f = BooleanLiteral(false)

    //def and(es : Expr*) : Expr = andJoin(es)
    //def or(es : Expr*) : Expr = orJoin(es)

    assert(and(x, and(x, x), x) === and(x, x, x, x))
    assert(and(x, t, x, t) === and(x, x))
    assert(and(x, t, f, x) === and(x, f))
    assert(and(x) === x)
    assert(and() === t)
    assert(and(t, t) === t)
    assert(and(f) === f)

    assert(or(x, or(x, x), x) === or(x, x, x, x))
    assert(or(x, f, x, f) === or(x, x))
    assert(or(x, f, t, x) === or(x, t))
    assert(or(x) === x)
    assert(or() === f)
    assert(or(f, f) === f)
    assert(or(t) === t)

    assert(and(y, and(x, y), x) === and(y, x, y, x))
    assert(and(x, t, y, t) === and(x, y))
    assert(or(x, or(x, y), y) === or(x, x, y, y))
    assert(or(x, f, y, f) === or(x, y))
  }
}
