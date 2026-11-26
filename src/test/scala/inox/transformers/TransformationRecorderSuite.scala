/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package transformers

import org.scalatest.funsuite.AnyFunSuite

class TransformationRecorderSuite extends AnyFunSuite {
  import inox.trees._

  val p = Variable.fresh("p", BooleanType())
  val q = Variable.fresh("q", BooleanType())
  val r = Variable.fresh("r", BooleanType())
  val t = BooleanLiteral(true)

  def recorder(e: Expr) = TransformationRecorder(inox.trees)(e)

  test("A rewrite is a step to the whole term") {
    val (por, pand) = (Or(p, q), And(p, r))
    val rec = recorder(And(por, pand))
    rec.at(pand) { rec.rewrite("logic", r); r }
    rec.at(por) { rec.rewrite("logic", t); t }
    assert(rec.result(And(t, r)) == Seq("logic" -> And(por, r), "logic" -> And(t, r)))
  }

  test("Nothing is recorded of a term that doesn't change") {
    val e = And(p, q)
    assert(recorder(e).result(e) == Seq())
    assert(recorder(e).result(And(p, q)) == Seq())
    val rec = recorder(e)
    assert(rec.at(p)(p) eq p)
    rec.rewrite("logic", And(p, q))
    assert(rec.result(e) == Seq())
  }

  test("A subterm is found by its identity, below the subterms too") {
    val inner = Or(q, r)
    val e = And(p, Not(inner))
    val rec = recorder(e)
    rec.at(inner) { rec.rewrite("logic", q); q }
    assert(rec.result(And(p, Not(q))) == Seq("logic" -> And(p, Not(q))))
  }

  test("The occurrences of an object are found in the order of the subterms") {
    val e = And(p, p)
    val rec = recorder(e)
    rec.at(p)(p)
    rec.at(p) { rec.rewrite("logic", t); t }
    assert(rec.result(And(p, t)) == Seq("logic" -> And(p, t)))
  }

  test("The term that a rewrite gives is the one that the transformation goes on with") {
    val rest = Or(q, r)
    val rec = recorder(And(Seq(p, q, r)))
    rec.rewrite("logic", And(p, rest))
    // the transformation is at `rest` once the term is `rest`
    rec.rewrite("logic", rest)
    rec.at(rest) { rec.at(q) { rec.rewrite("logic", t); t }; rec.rewrite("logic", t); t }
    assert(rec.result(t).map(_._1) == Seq("logic", "logic", "logic", "logic"))
    assert(rec.result(t).map(_._2) == Seq(And(p, rest), rest, Or(t, r), t))
  }

  test("What is done to a subterm without a step is a step of the rule of the pass") {
    val por = Or(p, q)
    val e = And(p, por)
    val rec = recorder(e)
    assert(rec.at(e, "pass") { And(p, rec.at(por)(p)) } == And(p, p))
    assert(rec.result(And(p, p)) == Seq("pass" -> And(p, p)))

    // and nothing more than the steps that the pass records
    val recording = recorder(e)
    recording.at(e, "pass") { recording.rewrite("logic", p); p }
    assert(recording.result(p) == Seq("logic" -> p))
  }

  test("What is done outside of the steps and of the passes is a step of unrecorded") {
    val por = Or(p, q)
    val e = And(p, por)
    val rec = recorder(e)
    rec.at(por) { rec.rewrite("logic", p); p }
    assert(rec.result(p) == Seq("logic" -> And(p, p), "unrecorded" -> p))
  }

  test("A transformation of a term that is not found is not recorded") {
    val e = And(p, Or(p, q))
    val rec = recorder(e)
    // an equal term is not the subterm
    val res = rec.at(Or(p, q), "pass") { assert(!rec.active); rec.rewrite("logic", p); p }
    assert(rec.active && res == p)
    assert(rec.result(And(p, p)) == Seq("unrecorded" -> And(p, p)))
    // unless it is the whole of what the transformation is at
    val whole = recorder(e)
    whole.at(And(p, Or(p, q)), "pass") { whole.rewrite("logic", p); p }
    assert(whole.result(p) == Seq("logic" -> p))
  }

  test("A suspended transformation is not recorded") {
    val e = And(p, q)
    val rec = recorder(e)
    rec.suspended { rec.at(p) { rec.rewrite("logic", t); t } }
    assert(rec.result(e) == Seq())
  }

  test("The occurrences of a variable are told apart in an unshared term") {
    val e = TransformationRecorder.unshared(inox.trees)(And(p, Or(p, q)))
    assert(e == And(p, Or(p, q)))
    val And(Seq(first, Or(Seq(second, _)))) = e: @unchecked
    assert(first ne second)
    // the second occurrence is found, although the first one comes first
    val rec = recorder(e)
    rec.at(second) { rec.rewrite("logic", t); t }
    rec.rewrite("logic", first)
    assert(rec.result(first) == Seq("logic" -> And(p, Or(t, q)), "logic" -> p))
  }

  test("The recorder of a transformation that is not recorded is never active") {
    val rec = TransformationRecorder.none(inox.trees)
    assert(!rec.active)
    // the transformation runs, and none of its steps is recorded
    assert(rec.at(And(p, q), "pass") { rec.rewrite("logic", t); t } == t)
    assert(rec.suspended(rec.active) == false)
    assert(!rec.active)
    assert(rec.result(t) == Seq())
  }
}
