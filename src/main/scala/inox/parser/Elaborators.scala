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
     with SimpleFunctions
     with BindingElaborators
     with ExprElaborators
     with TypeElaborators
     with IdentifierElaborators
     with NumberUtils {

  type Signature = (Int, Seq[SimpleTypes.Type] => (Seq[SimpleTypes.Type], SimpleTypes.Type))


  case class FunctionStore(
    functions: Map[inox.Identifier, Signature]) {

    def addFunction(identifier: inox.Identifier, signature: Signature): FunctionStore =
      copy(functions=functions + (identifier -> signature))
    def addFunctions(pairs: Seq[(inox.Identifier, Signature)]): FunctionStore =
      copy(functions=functions ++ pairs)
  }

  case class ADTStore(
    sortArities: Map[inox.Identifier, Int],
    constructors: Map[inox.Identifier, Signature],
    fieldIdsByName: Map[String, Seq[inox.Identifier]],
    fieldTypeByConsType: Map[Identifier, Seq[SimpleTypes.Type] => SimpleTypes.Type],
    sortIdByFieldId: Map[inox.Identifier, inox.Identifier],
    sortIdByConstructorId: Map[inox.Identifier, inox.Identifier])

  case class Store(
    symbols: trees.Symbols,
    identifierByName: Map[String, inox.Identifier],
    variables: Map[inox.Identifier, (SimpleTypes.Type, Eventual[trees.Type])],
    adtStore: ADTStore,
    funStore: FunctionStore,
    args: Seq[Any]) {

    def getSymbols = symbols
    def getIdentifier(name: String): Option[inox.Identifier] = identifierByName.get(name)
    def getFieldByName(name: String): Seq[(inox.Identifier, inox.Identifier)] = for {
      fid <- adtStore.fieldIdsByName.getOrElse(name, Seq())
      sid <- adtStore.sortIdByFieldId.get(fid)
    } yield (sid, fid)
    def getSortByField(identifier: Identifier): Option[inox.Identifier] = adtStore.sortIdByFieldId.get(identifier)
    def getTypeOfField(identifier: inox.Identifier): Seq[SimpleTypes.Type] => SimpleTypes.Type = adtStore.fieldTypeByConsType(identifier)
    def getVariable(identifier: inox.Identifier): Option[(SimpleTypes.Type, Eventual[trees.Type])] = variables.get(identifier)
    def getType(identifier: inox.Identifier): Option[(SimpleTypes.Type, Eventual[trees.Type])] = variables.get(identifier)
    def getTypeConstructor(identifier: inox.Identifier): Option[Int] = adtStore.sortArities.get(identifier)
    def getFunction(identifier: inox.Identifier): Option[Signature] = funStore.functions.get(identifier)
    def getConstructor(identifier: inox.Identifier): Option[Signature] = adtStore.constructors.get(identifier)
    def getSortOfConstructor(identifier: inox.Identifier): Option[inox.Identifier] = adtStore.sortIdByConstructorId.get(identifier)
    def getHole[A: Manifest](index: Int): Option[A] = {
      if (args.size <= index) None
      else args(index) match {
        case x: A => Some(x)
        case _ => None
      }
    }

    def addBinding(binding: SimpleBindings.Binding): Store =
      copy(
        variables=variables + (binding.id -> (binding.tpe, binding.evTpe)),
        identifierByName=identifierByName ++ binding.name.map(_ -> binding.id))
    def addBindings(bindings: Seq[SimpleBindings.Binding]): Store =
      copy(
        variables=variables ++ bindings.map(binding => (binding.id -> (binding.tpe, binding.evTpe))),
        identifierByName=identifierByName ++ bindings.flatMap(binding => binding.name.map(_ -> binding.id)))
    def addTypeBinding(binding: SimpleBindings.TypeBinding): Store =
      copy(
        variables=variables + (binding.id -> (binding.tpe, binding.evTpe)),
        identifierByName=identifierByName ++ binding.name.map(_ -> binding.id))
    def addTypeBindings(bindings: Seq[SimpleBindings.TypeBinding]): Store =
      copy(
        variables=variables ++ bindings.map(binding => (binding.id -> (binding.tpe, binding.evTpe))),
        identifierByName=identifierByName ++ bindings.flatMap(binding => binding.name.map(_ -> binding.id)))
    def addFunction(identifier: inox.Identifier, signature: Signature): Store =
      copy(funStore=funStore.addFunction(identifier, signature))
    def addFunctions(pairs: Seq[(inox.Identifier, Signature)]): Store =
      copy(funStore=funStore.addFunctions(pairs))
    def addSort(identifier: inox.Identifier, arity: Int): Store = ???
  }

  trait Elaborator[-A, +R] {
    def elaborate(template: A)(implicit store: Store): Constrained[R]
  }

  abstract class HSeqE[-A <: IR, H: Manifest, +R] extends Elaborator[HSeq[A], Seq[R]] {
    val elaborator: Elaborator[A, R]

    def wrap(value: H)(implicit store: Store): Constrained[R]

    override def elaborate(template: HSeq[A])(implicit store: Store): Constrained[Seq[R]] = {
      val elems = template.elems

      Constrained.sequence(elems.map {
        case Left(index) => store.getHole[Seq[H]](index) match {
          case None => Constrained.fail("TODO: Error")
          case Some(xs) => Constrained.sequence(xs.map(wrap(_)))
        }
        case Right(t) => elaborator.elaborate(t).map(Seq(_))
      }).map(_.flatten)
    }
  }
}