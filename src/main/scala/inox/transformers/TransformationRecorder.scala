/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package transformers

/** Records the steps of a transformation of a term, such as its simplification.
  *
  * A transformation says what it does as it does it, and not where: it rewrites the subterm
  * that it is at ([[rewrite]]), which names the rule of the step, and it tells which subterm it
  * goes on to transform ([[at]]). The recorder keeps the whole term as the steps so far rewrite
  * it, and finds the subterm in it by its identity: a transformation that recurses on the
  * subterms that it was given needs one call of [[at]], where it starts on a term. A step is
  * the rule and the whole term after it.
  *
  * Nothing is assumed of the transformation. What it makes of a subterm without a step is a
  * step too, of the rule of the pass that it runs in (see [[at]]) or of [[unrecorded]] outside
  * of any, and it runs without being recorded on a term that the recorder doesn't find, which
  * then shows as such a step where the result is used. The steps always lead from the original
  * term to the result: whoever reads them decides what each rule is worth.
  */
final class TransformationRecorder private (val trees: ast.Trees)(original: trees.Expr) {
  import trees._

  // A subterm that the transformation is at: `index` is its place among the subterms of the
  // parent's term, and `rule` names what is done to it without a step.
  private final class Frame(var current: Expr, val parent: Frame, val index: Int, var rule: String) {
    // the next subterm that a traversal of the subterms of `current` visits
    var next: Int = 0
  }

  private var top: Frame = new Frame(original, null, -1, TransformationRecorder.unrecorded)
  private val steps = scala.collection.mutable.ArrayBuffer[(String, Expr)]()
  private var suspensions: Int = 0

  /** Whether steps are recorded: not while the transformation runs on a term that is not a
    * subterm of the recorded one. */
  def active: Boolean = suspensions == 0

  /** The subterm that the transformation is at, as the steps so far rewrite it. */
  def node: Expr = top.current

  /** The whole term, as the steps so far rewrite it. */
  private def root: Expr = {
    var frame = top
    var e = frame.current
    while (frame.parent != null) {
      val Operator(es, recons) = frame.parent.current: @unchecked
      e = if (es(frame.index) eq e) frame.parent.current else recons(es.updated(frame.index, e))
      frame = frame.parent
    }
    e
  }

  /** Rewrites the subterm that the transformation is at into `to`, by `rule`. */
  def rewrite(rule: String, to: Expr): Unit = if (active && (top.current ne to)) {
    val changed = top.current != to
    // the transformation goes on with its own copy of the term, where it is the same
    top.current = to
    top.next = 0
    if (changed) steps += rule -> root
  }

  /** The places to descend into from `e` to reach `target`, a subterm of `e` that is not `e`:
    * one of its subterms from the `next`-th on first, as a traversal reaches the subterms in
    * order, then the others, then one below them. */
  private def find(e: Expr, target: Expr, next: Int): Option[List[Int]] = {
    val Operator(es, _) = e: @unchecked
    val direct = es.indexWhere(_ eq target, next) match {
      case -1 => es.indexWhere(_ eq target)
      case i => i
    }
    if (direct >= 0) Some(List(direct))
    else es.iterator.zipWithIndex.map((sub, i) => find(sub, target, 0).map(i :: _)).collectFirst { case Some(path) => path }
  }

  /** Runs `transform`, which transforms `e`, at `e`: the subterm that the transformation is at,
    * or one of its subterms. What `transform` makes of `e` without a step is a step of `rule`,
    * which names a pass, or of the rule of the pass around when it is `null`. When `e` is not
    * found, `transform` runs without being recorded. */
  def at(e: Expr, rule: String = null)(transform: => Expr): Expr = if (!active) transform else {
    val outer = top
    val name = if (rule ne null) rule else outer.rule
    def here: Expr = {
      val saved = outer.rule
      outer.rule = name
      try { val res = transform; rewrite(name, res); res } finally outer.rule = saved
    }
    if (outer.current eq e) here
    else find(outer.current, e, outer.next) match {
      case Some(path) =>
        outer.next = if (path.size == 1) path.head + 1 else path.head
        for (i <- path) {
          val Operator(es, _) = top.current: @unchecked
          top = new Frame(es(i), top, i, name)
        }
        try { val res = transform; rewrite(name, res); res }
        finally while (top ne outer) {
          // the subterm goes back where it was taken from
          val child = top
          top = child.parent
          val Operator(es, recons) = top.current: @unchecked
          if (es(child.index) ne child.current) top.current = recons(es.updated(child.index, child.current))
        }
      case None if outer.current == e => here
      case None => suspended(transform)
    }
  }

  /** Runs `body` without recording: on terms that are not subterms of the recorded one. */
  def suspended[A](body: => A): A = {
    suspensions += 1
    try body finally suspensions -= 1
  }

  /** The steps that rewrite the original term into `result`, which the transformation made. */
  def result(result: Expr): Seq[(String, Expr)] = {
    rewrite(TransformationRecorder.unrecorded, result)
    steps.toSeq
  }
}

object TransformationRecorder {
  /** The rule of the steps that a transformation didn't record, outside of any pass. */
  val unrecorded = "unrecorded"

  /** A recorder of the steps of a transformation of `e`, a term of `t`. */
  def apply(t: ast.Trees)(e: t.Expr): TransformationRecorder { val trees: t.type } =
    new TransformationRecorder(t)(e).asInstanceOf[TransformationRecorder { val trees: t.type }]

  /** `e`, a term of `t`, with a copy of each occurrence of its variables. A recorder finds
    * subterms by their identity, and a term has the same object of a variable wherever it
    * occurs: the occurrences are told apart in the copy. */
  def unshared(t: ast.Trees)(e: t.Expr): t.Expr = {
    import t._
    def rec(e: Expr): Expr = e match {
      case v: Variable => v.copy().copiedFrom(v)
      case Operator(es, recons) =>
        val nes = es.map(rec)
        if ((es zip nes).exists((a, b) => a ne b)) recons(nes).copiedFrom(e) else e
    }
    rec(e)
  }
}
