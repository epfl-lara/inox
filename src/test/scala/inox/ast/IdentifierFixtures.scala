/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package ast

/** Builds identifiers that `FreshIdentifier` doesn't know about, as another process would. */
object IdentifierFixtures {
  def unrestored(name: String, globalId: Int, id: Int): Identifier = new Identifier(name, globalId, id)
}
