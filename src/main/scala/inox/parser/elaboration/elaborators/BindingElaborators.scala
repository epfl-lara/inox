package inox
package parser
package elaboration
package elaborators

trait BindingElaborators { self: Elaborators =>

  import Bindings._

  object BindingE extends Elaborator[Binding, (SimpleBindings.Binding, Eventual[trees.ValDef])] {

    override def elaborate(template: Binding)(implicit store: Store): Constrained[(SimpleBindings.Binding, Eventual[trees.ValDef])] = template match {
      case BindingHole(index) => store.getHole[trees.ValDef](index) match {
        case None => Constrained.fail("TODO: Error")
        case Some(vd) => Constrained.attempt(SimpleBindings.fromInox(vd).map { sb =>
          (sb, Eventual.pure(vd))
        }, "TODO: Error")
      }
      case ExplicitValDef(id, tpe) => for {
        i <- DefIdE.elaborate(id)
        (st, et) <- TypeE.elaborate(tpe)
      } yield (SimpleBindings.Binding(i, st), Eventual.withUnifier { implicit unifier =>
        trees.ValDef(i, et.get)
      })
      case InferredValDef(id) => for {
        i <- DefIdE.elaborate(id)
      } yield {

        val u = SimpleTypes.Unknown.fresh
        val sb = SimpleBindings.Binding(i, u)
        val vd = Eventual.withUnifier { unifier =>
          trees.ValDef(i, SimpleTypes.toInox(unifier.get(u)))
        }

        (sb, vd)
      }
    }
  }

  object BindingSeqE extends HSeqE[Binding, trees.ValDef, (SimpleBindings.Binding, Eventual[trees.ValDef])] {

    override val elaborator = BindingE
    override def wrap(vd: trees.ValDef)(implicit store: Store): Constrained[(SimpleBindings.Binding, Eventual[trees.ValDef])] =
      Constrained.attempt(SimpleBindings.fromInox(vd), "TODO: Error").map { sb =>
        (sb, Eventual.pure(vd))
      }
  }
}