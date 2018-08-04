package inox
package parser

import elaboration._
import elaborators._

trait Elaborators
  extends Trees
     with IRs
     with SimpleTypes
     with Constraints
     with ExprElaborators
     with TypeElaborators
     with IdentifierElaborators {

  trait Elaborator[-A] {
    type Context
    type Result

    def elaborate(template: A, context: Context)(implicit store: Store): Constrained[Result]
  }

  trait Store {
    def getIdentifier(name: String): Constrained[inox.Identifier]
    def getSort(identifier: inox.Identifier): Constrained[trees.ADTSort]
    def getHole[A: Manifest](hole: Hole): Constrained[A]
  }
}