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
     with SimpleADTs
     with BindingElaborators
     with ExprElaborators
     with TypeElaborators
     with IdentifierElaborators
     with FunctionElaborators
     with ADTsElaborators
     with ProgramElaborators
     with NumberUtils
     with Solvers
     with ElaborationErrors {

  type Signature = (Int, Seq[SimpleTypes.Type] => (Seq[SimpleTypes.Type], SimpleTypes.Type))

  private def toSignature(function: SimpleFunctions.Function): Signature =
    (function.typeParams.size, (actualTypes: Seq[SimpleTypes.Type]) => {
      require(actualTypes.size == function.typeParams.size)

      val replacements = function.typeParams.map(_.id).zip(actualTypes).toMap

      (function.params.map(_.tpe.replaceTypeParams(replacements)), function.retTpe.replaceTypeParams(replacements))
    })

  private def toSignature(sort: SimpleADTs.Sort, constructor: SimpleADTs.Constructor): Signature = {
    require(sort.id == constructor.sort)

    (sort.typeParams.size, (actualTypes: Seq[SimpleTypes.Type]) => {
      require(actualTypes.size == sort.typeParams.size)

      val replacements = sort.typeParams.map(_.id).zip(actualTypes).toMap

      (constructor.params.map(_.tpe.replaceTypeParams(replacements)), SimpleTypes.ADTType(sort.id, actualTypes))
    })
  }


  case class FunctionStore(signatures: Map[inox.Identifier, Signature]) {

    def addFunction(function: SimpleFunctions.Function): FunctionStore =
      FunctionStore(signatures + (function.id -> toSignature(function)))
    def addFunctions(functions: Seq[SimpleFunctions.Function]): FunctionStore =
      FunctionStore(signatures ++ functions.map(f => (f.id -> toSignature(f))))
  }

  case class ADTStore(
    sortArities: Map[inox.Identifier, Int],
    constructors: Map[inox.Identifier, Signature],
    fieldIdsByName: Map[String, Seq[inox.Identifier]],
    fieldTypeByConsType: Map[Identifier, Seq[SimpleTypes.Type] => SimpleTypes.Type],
    sortIdByFieldId: Map[inox.Identifier, inox.Identifier],
    sortIdByConstructorId: Map[inox.Identifier, inox.Identifier]) {

    def addSort(sort: SimpleADTs.Sort): ADTStore =
      ADTStore(
        sortArities + (sort.id -> sort.typeParams.size),
        constructors ++ (sort.constructors.map(c => (c.id, toSignature(sort, c)))),
        sort.constructors.flatMap(c => c.params.flatMap(f => f.name.map((_, f.id)))).foldLeft(fieldIdsByName) {
          case (acc, (name, id)) => acc + (name -> (acc.getOrElse(name, Seq()) :+ id))
        },
        fieldTypeByConsType ++ (sort.constructors.flatMap(c => c.params.map(f => {
          f.id -> { (actualTypes: Seq[SimpleTypes.Type]) =>
            require(actualTypes.size == sort.typeParams.size)

            val replacements = sort.typeParams.map(_.id).zip(actualTypes).toMap

            f.tpe.replaceTypeParams(replacements)
          }
        }))),
        sortIdByFieldId ++ sort.constructors.flatMap(c => c.params.map(f => (f.id -> sort.id))),
        sortIdByConstructorId ++ sort.constructors.map(c => (c.id -> sort.id)))

    def addSorts(sorts: Seq[SimpleADTs.Sort]): ADTStore =
      sorts.foldLeft(this) {
        case (acc, sort) => acc.addSort(sort)
      }
  }

  case class Store(
    symbols: trees.Symbols,
    names: Map[String, inox.Identifier],
    typeNames: Map[String, inox.Identifier],
    variables: Map[inox.Identifier, (SimpleTypes.Type, Eventual[trees.Type])],
    adtStore: ADTStore,
    funStore: FunctionStore,
    args: Seq[Any]) {

    def getSymbols = symbols
    def getExprIdentifier(name: String): Option[inox.Identifier] = names.get(name)
    def getTypeIdentifier(name: String): Option[inox.Identifier] = typeNames.get(name)
    def getFieldByName(name: String): Seq[(inox.Identifier, inox.Identifier)] = for {
      fid <- adtStore.fieldIdsByName.getOrElse(name, Seq())
      sid <- adtStore.sortIdByFieldId.get(fid)
    } yield (sid, fid)
    def getSortByField(identifier: Identifier): Option[inox.Identifier] =
      adtStore.sortIdByFieldId.get(identifier)
    def getTypeOfField(identifier: inox.Identifier): Seq[SimpleTypes.Type] => SimpleTypes.Type =
      adtStore.fieldTypeByConsType(identifier)
    def getVariable(identifier: inox.Identifier): Option[(SimpleTypes.Type, Eventual[trees.Type])] =
      variables.get(identifier)
    def getType(identifier: inox.Identifier): Option[(SimpleTypes.Type, Eventual[trees.Type])] =
      variables.get(identifier)
    def getTypeConstructor(identifier: inox.Identifier): Option[Int] =
      adtStore.sortArities.get(identifier)
    def getFunction(identifier: inox.Identifier): Option[Signature] =
      funStore.signatures.get(identifier)
    def getConstructor(identifier: inox.Identifier): Option[Signature] =
      adtStore.constructors.get(identifier)
    def getSortOfConstructor(identifier: inox.Identifier): Option[inox.Identifier] =
      adtStore.sortIdByConstructorId.get(identifier)
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
        names=names ++ binding.name.map(_ -> binding.id))
    def addBindings(bindings: Seq[SimpleBindings.Binding]): Store =
      copy(
        variables=variables ++ bindings.map(binding => (binding.id -> (binding.tpe, binding.evTpe))),
        names=names ++ bindings.flatMap(binding => binding.name.map(_ -> binding.id)))
    def addTypeBinding(binding: SimpleBindings.TypeBinding): Store =
      copy(
        variables=variables + (binding.id -> (binding.tpe, binding.evTpe)),
        typeNames=typeNames ++ binding.name.map(_ -> binding.id))
    def addTypeBindings(bindings: Seq[SimpleBindings.TypeBinding]): Store =
      copy(
        variables=variables ++ bindings.map(binding => (binding.id -> (binding.tpe, binding.evTpe))),
        typeNames=typeNames ++ bindings.flatMap(binding => binding.name.map(_ -> binding.id)))
    def addFunction(function: SimpleFunctions.Function): Store =
      copy(
        funStore=funStore.addFunction(function),
        names=names ++ function.optName.map((_, function.id)))
    def addFunctions(functions: Seq[SimpleFunctions.Function]): Store =
      copy(
        funStore=funStore.addFunctions(functions),
        names=names ++ functions.flatMap(f => f.optName.map((_, f.id))))
    def addSort(sort: SimpleADTs.Sort): Store =
      copy(
        adtStore=adtStore.addSort(sort),
        typeNames=typeNames ++ sort.optName.map((_, sort.id)),
        names=names ++ sort.constructors.flatMap(c => c.optName.map((_, c.id))))
    def addSorts(sorts: Seq[SimpleADTs.Sort]): Store =
      copy(
        adtStore=adtStore.addSorts(sorts),
        typeNames=typeNames ++ sorts.flatMap(sort => sort.optName.map((_, sort.id))),
        names=names ++ sorts.flatMap(sort => sort.constructors.flatMap(c => c.optName.map((_, c.id)))))
  }

  def createStore(symbols: trees.Symbols, args: Seq[Any]): Store = {

    val adtStore: ADTStore = ADTStore(Map(), Map(), Map(), Map(), Map(), Map())

    val funStore: FunctionStore = FunctionStore(Map())

    Store(symbols, Map(), Map(), Map(), adtStore, funStore, args)
      .addFunctions(symbols.functions.values.flatMap(SimpleFunctions.fromInox(_)).toSeq)
      .addSorts(symbols.sorts.values.flatMap(SimpleADTs.fromInox(_)).toSeq)
  }

  trait Elaborator[-A, +R] {
    def elaborate(template: A)(implicit store: Store): Constrained[R]
  }

  abstract class HSeqE[-A <: IR, H: Manifest, +R](underlying: String) extends Elaborator[HSeq[A], Seq[R]] {
    val elaborator: Elaborator[A, R]

    def wrap(value: H, where: IR)(implicit store: Store): Constrained[R]

    override def elaborate(template: HSeq[A])(implicit store: Store): Constrained[Seq[R]] = {
      val elems = template.elems

      Constrained.sequence(elems.map {
        case Left(r) => store.getHole[Seq[H]](r.index) match {
          case None => Constrained.fail(invalidHoleType("Seq[" + underlying + "]")(r.pos))
          case Some(xs) => Constrained.sequence(xs.map(wrap(_, r)))
        }
        case Right(t) => elaborator.elaborate(t).map(Seq(_))
      }).map(_.flatten)
    }
  }
}