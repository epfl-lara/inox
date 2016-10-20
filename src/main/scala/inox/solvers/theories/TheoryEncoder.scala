/* Copyright 2009-2015 EPFL, Lausanne */

package inox
package solvers
package theories

import utils._

trait TheoryEncoder extends ast.ProgramEncoder { self =>
  lazy val trees: sourceProgram.trees.type = sourceProgram.trees
  lazy val t: trees.type = trees
}

trait NoEncoder extends TheoryEncoder {
  import trees._

  protected object encoder extends IdentityTreeTransformer
  protected object decoder extends IdentityTreeTransformer
}

