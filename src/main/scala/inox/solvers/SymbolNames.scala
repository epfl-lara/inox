package inox
package solvers

import scala.collection.mutable

/** Names the symbols that a solver declares, numbering those of each name from 0.
  *
  * The ids of identifiers come from global counters, so a query named with them gets different
  * names depending on the identifiers that other threads create, and solvers such as Z3 depend on
  * the names: the same query then takes different amounts of work. A solver that names its symbols
  * with its own instance of this class gets the same names whenever it is given the same query.
  */
final class SymbolNames(delimiter: String = "!") {
  private val names = mutable.Map.empty[Identifier, String]
  private val counts = mutable.Map.empty[String, Int]

  /** A name that no other call returns, starting with `base` */
  def fresh(base: String): String = {
    val n = counts.getOrElse(base, 0)
    counts(base) = n + 1
    s"$base$delimiter$n"
  }

  /** The name of `id`, the same on every call, starting with `base` the first time */
  def apply(id: Identifier, base: String): String = names.getOrElseUpdate(id, fresh(base))

  /** The name of `id`, the same on every call */
  def apply(id: Identifier): String = apply(id, id.name)
}
