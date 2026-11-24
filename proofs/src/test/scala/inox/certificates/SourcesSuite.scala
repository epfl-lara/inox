/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package certificates

import org.scalatest.funsuite.AnyFunSuite

/** The check that the clauses of a template are those of its source. */
class SourcesSuite extends AnyFunSuite {
  import Checker._
  import Sources._

  val signature: Signature = Signature(parse(
    """(declare-datatypes ((List 0)) (((Nil) (Cons (head Int) (tail List)))))
      |(declare-fun size (List) Int)
      |(declare-fun f (Int) Int)
      |(declare-fun g (Int) Int)""".stripMargin))

  def term(text: String): SExpr = parse(text).head

  def traced(params: String, source: Source, clauses: String*): Either[String, Ranks] =
    Sources.check(parse(params), clauses.map(term), source, signature)

  // the clauses of `size`, whose recursive call is assumed not to be negative
  val size: Function = Function(term("(size l)"),
    term("(ite (is-Cons l) (+ 1 (let ((res (size (tail l)))) (assume (>= res 0) res))) 0)"),
    List(term("e") -> term("(ite c (+ 1 lt) 0)")))
  val sizeClauses: Seq[String] = Seq(
    "(=> start (= c (is-Cons l)))",
    "(=> start (= (size l) e))",
    "(=> b1 (= e (+ 1 lt)))",
    "(=> b1 (= lt (size (tail l))))",
    "(=> b1 (>= lt 0))",
    "(=> b2 (= e 0))",
    "(= (and start c) b1)",
    "(= (and start (not c)) b2)",
    "(=> b1 (or (> (apply rank l) (apply rank (tail l))) diverges))")

  test("The clauses of a function with a conditional, an assumption and a recursive call are traced") {
    assert(traced("start l", size, sizeClauses*) ==
      Right(Ranks(Set(Atom("size") -> Atom("rank")), Set(Atom("rank") -> Set(Atom("size"))), Set(Atom("diverges")))))
  }

  test("The source of a defined function is its call, with the names and meanings that it has") {
    assert(Source.unapply(term("(definition (size l))")) == Some(Definition(term("(size l)"), Nil)))
    assert(Source.unapply(term("(definition (size l) (names (n (f 1))) (where (e 0)))")) ==
      Some(Definition(term("(size l)"), List(term("n") -> term("(f 1)")), List(term("e") -> term("0")))))
    assert(Source.unapply(term("(definition (size l) (where (e 0)))")) ==
      Some(Definition(term("(size l)"), Nil, List(term("e") -> term("0")))))
    assert(Source.unapply(term("(definition (size l) (names n))")).isEmpty)
  }

  test("A value, an assumption or a decrease that the source doesn't have is not traced") {
    def changed(from: String, to: String) = traced("start l", size, sizeClauses.map(c => if (c == from) to else c)*)
    assert(changed("(=> b2 (= e 0))", "(=> b2 (= e 1))").isLeft)
    assert(changed("(=> b1 (>= lt 0))", "(=> b1 (>= lt 1))").isLeft)
    // the assumption holds on the path of the call only
    assert(changed("(=> b1 (>= lt 0))", "(=> start (>= (size (tail l)) 0))").isLeft)
    assert(changed("(=> b1 (or (> (apply rank l) (apply rank (tail l))) diverges))",
      "(=> b1 (or (> (apply rank l) (apply rank l)) diverges))").isLeft)
    assert(changed("(= (and start (not c)) b2)", "(= (and start c) b2)").isLeft)
    // nor is a meaning that the clauses don't give
    assert(traced("start l", Function(size.call, size.body, List(term("e") -> term("(ite c (+ 2 lt) 0)"))), sizeClauses*).isLeft)
    assert(traced("start l", Function(size.call, size.body), sizeClauses*).isLeft)
  }

  test("The operands of a conjunction are on the path of those before them") {
    val source = Expression(term("(and (= y 0) (= (div x y) 5))"), List(term("e") -> term("(and res (= (div x y) 5))")))
    val clauses = Seq(
      "(=> start (=> (not res) (not e)))",
      "(=> start (= res (= y 0)))",
      "(=> start e)",
      "(=> b (= e (= (div x y) 5)))",
      "(=> b (not (= y 0)))",
      "(= (and start res) b)")
    assert(traced("start y x", source, clauses*).isRight)
    // the divisor is not zero where the division is reached, and nowhere else
    assert(traced("start y x", source, clauses.map(c => if (c == "(=> b (not (= y 0)))") "(=> b (not (= x 0)))" else c)*).isLeft)
  }

  test("A selector needs its constructor, and a bound expression is reached where it is bound") {
    val source = Function(term("(f x)"), term("(let ((v (f (head (Cons x Nil))))) (ite (> x 0) v 0))"),
      List(term("e") -> term("(ite (> x 0) lt 0)")))
    val clauses = Seq(
      "(=> start (= lt (f (head (Cons x Nil)))))",
      "(=> start (is-Cons (Cons x Nil)))",
      "(=> start (= (f x) e))",
      "(=> b1 (= e lt))",
      "(=> b2 (= e 0))",
      "(= (and start (> x 0)) b1)",
      "(= (and start (not (> x 0))) b2)",
      "(=> start (> (apply rank x) (apply rank (head (Cons x Nil)))))")
    assert(traced("start x", source, clauses*).isRight)
    assert(traced("start x", source, clauses.map(c => if (c == "(=> start (is-Cons (Cons x Nil)))") "(=> start (is-Nil (Cons x Nil)))" else c)*).isLeft)
  }

  test("A call made on two paths is under the merge of their blockers") {
    val source = Function(term("(f x)"), term("(ite (> x 0) (g x) (+ 1 (g x)))"), List(term("e") -> term("(ite c lt (+ 1 lt))")))
    val clauses = Seq(
      "(=> start (= c (> x 0)))",
      "(= (and start c) b1)",
      "(= (and start (not c)) b2)",
      "(= (or b1 b2) bm)",
      "(=> bm (= lt (g x)))",
      "(=> b1 (= e lt))",
      "(=> b2 (= e (+ 1 lt)))",
      "(=> start (= (f x) e))")
    assert(traced("start x", source, clauses*).isRight)
    // the value on the first path is the call itself
    assert(traced("start x", source, clauses.map(c => if (c == "(=> b1 (= e lt))") "(=> b1 (= e (+ 1 lt)))" else c)*).isLeft)
  }

  test("The functions that a lambda captures come before it, which the source of a capture assumes") {
    val captured = term("(typing capture \"List\" l c)")
    val source = Expression(captured, List(captured ->
      term("(ite (is-Cons l) (and (assume (< (order (f (head l))) (order c)) true) (assume (typing capture \"List\" (tail l) c) true)) true)")))
    val clauses = Seq(
      "(=> start true)",
      "(= (and start (is-Cons l)) b)",
      "(=> b (< (order (f (head l))) (order c)))")
    assert(traced("start c l", source, clauses*).isRight)
    // the order is the other way around, or on the other path
    assert(traced("start c l", source, clauses.map(c => if (c.startsWith("(=> b (<")) "(=> b (< (order c) (order (f (head l)))))" else c)*).isLeft)
    assert(traced("start c l", source, clauses.map(c => if (c.startsWith("(=> b (<")) "(=> start (< (order (f (head l))) (order c)))" else c)*).isLeft)
  }

  test("The rank of a function without parameters is a symbol") {
    val source = Function(Atom("k"), term("(f 1)"))
    val clauses = Seq(
      "(=> start (= k e))",
      "(=> start (= e (f 1)))",
      "(=> start (or (> rank_k (apply rank_f 1)) diverges))")
    assert(traced("start", source, clauses*) ==
      Right(Ranks(Set(Atom("k") -> Atom("rank_k")), Set(Atom("rank_f") -> Set(Atom("f"))), Set(Atom("diverges")))))
    assert(traced("start", source, clauses.map(c => if (c.contains("rank_f")) "(=> start (or (> rank_k (apply rank_f 2)) diverges))" else c)*).isLeft)
  }

  test("A conjunction that an assumption equates with another term is the conjunction of its operands") {
    val source = Function(term("(f x)"), term("(let ((c (and (> x 0) (> (g x) 0)))) (assume (= c (> x 1)) (ite c 1 0)))"),
      List(term("e") -> term("(and r (> lt 0))"), term("v") -> term("(ite e 1 0)")))
    val clauses = Seq(
      "(=> start (= e (> x 1)))",
      "(=> start (=> (not r) (not e)))",
      "(=> start (= r (> x 0)))",
      "(=> b (= e (> lt 0)))",
      "(=> b (= lt (g x)))",
      "(= (and start r) b)",
      "(=> start (= (f x) v))",
      "(=> b1 (= v 1))",
      "(=> b2 (= v 0))",
      "(= (and start e) b1)",
      "(= (and start (not e)) b2)")
    assert(traced("start x", source, clauses*).isRight)
    // the assumption is not one of the conjunction's operands
    assert(traced("start x", source, clauses.map(c => if (c == "(=> start (= e (> x 1)))") "(=> start (= e (> x 2)))" else c)*).isLeft)
  }

  test("The meanings of a source are of its symbols and terms, never of a literal or of themselves") {
    assert(traced("start y", Expression(term("(= y 0)"), List(Atom("true") -> term("(= y 1)"))), "(=> start (= y 0))").isLeft)
    assert(traced("start y", Expression(term("(= y v)"), List(Atom("v") -> term("(+ v 1)"))), "(=> start (= y v))").isLeft)
  }
}
