package inox
package parser
package elaboration
package elaborators

trait ADTsElaborators { self: Elaborators =>

  import ADTs._

  class EmptySortE extends Elaborator[Sort, SimpleADTs.Sort] {
    override def elaborate(sort: Sort)(implicit store: Store): Constrained[SimpleADTs.Sort] = for {
      (i, optName) <- DefIdE.elaborate(sort.identifier)
      typeBindings <- DefIdSeqE.elaborate(sort.typeParams).map(_.map({
        case (varId, optVarName) => SimpleBindings.TypeBinding(
          varId, SimpleTypes.TypeParameter(varId), Eventual.pure(trees.TypeParameter(varId, Seq())), optVarName)
      }))
    } yield SimpleADTs.Sort(i, optName, typeBindings, Seq())
  }
  val EmptySortE = new EmptySortE

  class SortE extends Elaborator[Sort, (SimpleADTs.Sort, Eventual[trees.ADTSort])] {
    override def elaborate(sort: Sort)(implicit store: Store): Constrained[(SimpleADTs.Sort, Eventual[trees.ADTSort])] = for {
      s <- EmptySortE.elaborate(sort)
      (scs, ecs) <- new ConstructorSeqE(s.id).elaborate(sort.constructors)({
        store
          .addSort(s)
          .addTypeBindings(s.typeParams)
        }).map(_.unzip)
      fieldNames = scs.flatMap(_.params.flatMap(_.name))
      _ <- Constrained.checkImmediate(fieldNames.toSet.size == fieldNames.size, sort, fieldsNotDistincts)
    } yield (s.copy(constructors=scs), Eventual.withUnifier { implicit unifier =>
        new trees.ADTSort(s.id, s.typeParams.map(tb => trees.TypeParameterDef(tb.id, Seq())), ecs.map(_.get), Seq()) })
  }
  val SortE = new SortE

  class ConstructorE(sortId: inox.Identifier) extends Elaborator[Constructor, (SimpleADTs.Constructor, Eventual[trees.ADTConstructor])] {
    override def elaborate(constructor: Constructor)(implicit store: Store): Constrained[(SimpleADTs.Constructor, Eventual[trees.ADTConstructor])] = constructor match {
      case ConstructorValue(identifier, parameters) => for {
        (id, optName) <- DefIdE.elaborate(identifier)
        params <- BindingSeqE.elaborate(parameters)
      } yield (SimpleADTs.Constructor(id, optName, params, sortId), Eventual.withUnifier { implicit unifier =>
          new trees.ADTConstructor(id, sortId, params.map(_.evValDef.get)) })
      case ConstructorHole(index) => Constrained.fail(unsupportedHoleTypeForElaboration("ADTConstructor")(constructor.pos))
    }
  }

  class ConstructorSeqE(sortId: inox.Identifier) extends HSeqE[Constructor, trees.ADTConstructor, (SimpleADTs.Constructor, Eventual[trees.ADTConstructor])]("ADTConstructor") {

    override val elaborator = new ConstructorE(sortId)

    def wrap(c: trees.ADTConstructor, where: IR)(implicit store: Store): Constrained[(SimpleADTs.Constructor, Eventual[trees.ADTConstructor])] =
      Constrained.fail(unsupportedHoleTypeForElaboration("ADTConstructor")(where.pos))
  }
}