package inox
package parser

trait IdentifierIRs { self: IRs =>

  trait IdentifierIR extends IR[Unit, inox.Identifier]

  case class IdentifierName(name: String) extends IdentifierIR {
    override def elaborate(context: Unit)(implicit store: Store, args: Args): Constrained[inox.Identifier] =
      Constrained.pure(store.getIdentifier(name))
    override def extract(scrutinee: inox.Identifier): Matching =
      Matching.ensureConsistent(name, scrutinee)
  }

  case class IdentifierHole(index: Int) extends  IRHole[Unit, inox.Identifier] with IdentifierIR
}