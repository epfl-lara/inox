package inox
package parser

trait TypeIRs { self: IRs =>

  sealed trait TypeIR extends IR[Option[inox.Identifier], trees.Type]

}