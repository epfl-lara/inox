/* Copyright 2009-2020 EPFL, Lausanne */

package inox
package tip

import smtlib.theories.Operations._

object MapExtensions {
  private val MapMerge = "map.merge"

  object Merge extends Operation3 { override val name = MapMerge }
}
