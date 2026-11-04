/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package utils

/** Splits a large pattern match into several smaller methods, e.g. one per theory.
  *
  * Each method handles some of the cases and returns [[unhandled]] for the others, and the
  * methods are chained with [[otherwise]]:
  * {{{
  *   def e(expr: Expr): Expr =
  *     eCore(expr) otherwise eArithmetic(expr) otherwise eStrings(expr) otherwise unexpected(expr)
  * }}}
  * Both are inlined, so the chain compiles to a sequence of null checks and allocates nothing.
  * Keeping methods small matters for the JIT, which doesn't compile very large methods, and
  * for coverage instrumentation, which skips them.
  *
  * The combinator isn't called `orElse` because members such as `Option.orElse` would silently
  * take precedence over the extension.
  */
object CaseSplit {
  /** The result of a split method for inputs it doesn't handle. */
  inline def unhandled: Null = null

  extension [A <: AnyRef](inline result: A) {
    /** `result`, unless it is [[unhandled]], in which case `next` is evaluated. */
    infix inline def otherwise(inline next: A): A = {
      val r = result
      if (r ne null) r else next
    }
  }
}
