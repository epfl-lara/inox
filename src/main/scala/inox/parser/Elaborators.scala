package inox
package parser

import elaboration._
import elaborators._

trait Elaborators
  extends Trees
     with IRs
     with Constraints
     with SimpleTypes
     with SimpleBindings
     with BindingElaborators
     with ExprElaborators
     with TypeElaborators
     with IdentifierElaborators {

  trait Store {
    def getIdentifier(name: String): Option[inox.Identifier]
    def getVariable(identifier: inox.Identifier): Option[(SimpleTypes.Type, Eventual[trees.Type])]
    def getType(identifier: inox.Identifier): Option[(SimpleTypes.Type, Eventual[trees.Type])]
    def getTypeConstructor(identifier: inox.Identifier): Option[(Int, Seq[SimpleTypes.Type] => SimpleTypes.Type, Eventual[Seq[trees.Type] => trees.Type])]
    def getHole[A: Manifest](index: Int): Option[A]
    val getSymbols: trees.Symbols

    def addVariable(id: inox.Identifier, simpleType: SimpleTypes.Type, eventualType: Eventual[trees.Type]): Store
    def addVariables(triples: Seq[(inox.Identifier, SimpleTypes.Type, Eventual[trees.Type])]): Store
  }

  trait Elaborator[-A <: IR, -C, +R] {
    def elaborate(template: A, context: C)(implicit store: Store): Constrained[R]
  }

  implicit class ElaborateDecorator[-A <: IR, -C, +R](template: A)(implicit elaborator: Elaborator[A, C, R]) {
    def elaborate(context: C)(implicit store: Store): Constrained[R] = elaborator.elaborate(template, context)(store)
  }

  abstract class HSeqE[-A <: IR, -C, H: Manifest, +R] extends Elaborator[HSeq[A], Seq[C], Seq[R]] {
    val elaborator: Elaborator[A, C, R]

    def wrap(value: H)(implicit store: Store): R

    override def elaborate(template: HSeq[A], contexts: Seq[C])(implicit store: Store): Constrained[Seq[R]] = {
      val elems = template.elems
      require(elems.size == contexts.size)

      Constrained.sequence(elems.zip(contexts).map {
        case (Left(index), _) => store.getHole[Seq[H]](index) match {
          case None => Constrained.fail("TODO: Error")
          case Some(xs) => Constrained.pure(xs.map(wrap(_)))
        }
        case (Right(t), c) => elaborator.elaborate(t, c).map(Seq(_))
      }).map(_.flatten)
    }
  }
}