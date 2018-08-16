package inox
package parser
package elaboration
package elaborators

trait ADTsElaborators { self: Elaborators =>

  import ADTs._

  object EmptySortE extends Elaborator[Sort, SimpleADTs.Sort] {
    override def elaborate(sort: Sort)(implicit store: Store): Constrained[SimpleADTs.Sort] = for {
      (i, optName) <- DefIdE.elaborate(sort.identifier)
      typeBindings <- DefIdSeqE.elaborate(sort.typeParams).map(_.map({
        case (varId, optVarName) => SimpleBindings.TypeBinding(
          varId, SimpleTypes.TypeParameter(varId), Eventual.pure(trees.TypeParameter(varId, Seq())), optVarName)
      }))
    } yield SimpleADTs.Sort(i, optName, typeBindings, Seq())
  }

  object SortE extends Elaborator[Sort, (SimpleADTs.Sort, Eventual[trees.ADTSort])] {
    override def elaborate(sort: Sort)(implicit store: Store): Constrained[(SimpleADTs.Sort, Eventual[trees.ADTSort])] = for {
      s <- EmptySortE.elaborate(sort)
      (scs, ecs) <- new ConstructorSeqE(s.id).elaborate(sort.constructors)({
        store
          .addSort(s)
          .addTypeBindings(s.typeParams)
        }).map(_.unzip)
    } yield (s.copy(constructors=scs), Eventual.withUnifier { implicit unifier =>
        new trees.ADTSort(s.id, s.typeParams.map(tb => trees.TypeParameterDef(tb.id, Seq())), ecs.map(_.get), Seq()) })
  }

  class ConstructorE(sortId: inox.Identifier) extends Elaborator[Constructor, (SimpleADTs.Constructor, Eventual[trees.ADTConstructor])] {
    override def elaborate(constructor: Constructor)(implicit store: Store): Constrained[(SimpleADTs.Constructor, Eventual[trees.ADTConstructor])] = for {
      (id, optName) <- DefIdE.elaborate(constructor.identifier)
      params <- BindingSeqE.elaborate(constructor.params)
    } yield (SimpleADTs.Constructor(id, optName, params, sortId), Eventual.withUnifier { implicit unifier =>
        new trees.ADTConstructor(id, sortId, params.map(_.evValDef.get)) })
  }

  class ConstructorSeqE(sortId: inox.Identifier) extends HSeqE[Constructor, trees.ADTConstructor, (SimpleADTs.Constructor, Eventual[trees.ADTConstructor])] {

    override val elaborator = new ConstructorE(sortId)

    def wrap(c: trees.ADTConstructor)(implicit store: Store): Constrained[(SimpleADTs.Constructor, Eventual[trees.ADTConstructor])] =
      Constrained.attempt(SimpleADTs.fromInox(c).map(sc => (sc, Eventual.pure(c))), "TODO: Error: Invalid constructor.")
  }
}