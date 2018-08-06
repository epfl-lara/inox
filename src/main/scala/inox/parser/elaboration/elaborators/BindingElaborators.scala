package inox
package parser
package elaboration
package elaborators

trait BindingElaborators { self: Elaborators =>

  import Bindings._

  implicit object BindingE extends Elaborator[Binding, String, (SimpleBindings.Binding, Eventual[trees.ValDef])] {
    override def elaborate(template: Binding, name: String)(implicit store: Store): Constrained[(SimpleBindings.Binding, Eventual[trees.ValDef])] = template match {
      case BindingHole(index) => store.getHole[trees.ValDef](index) match {
        case None => Constrained.fail("TODO: Error")
        case Some(vd) => Constrained.pure((SimpleBindings.fromInox(vd), Eventual.pure(vd)))
      }
      case ExplicitValDef(id, tpe) => for {
        i <- IdE.elaborate(id, Modes.Def)
        (st, et) <- TypeE.elaborate(tpe, Some(i))
      } yield (SimpleBindings.Binding(i, st), Eventual.withUnifier { implicit unifier =>
        trees.ValDef(i, et.get)
      })
      case InferredValDef(id) => for {
        i <- IdE.elaborate(id, Modes.Def)
      } yield {

        val u = SimpleTypes.Unknown.fresh
        val sb = SimpleBindings.Binding(i, u)
        val vd = Eventual.withUnifier { unifier =>
          trees.ValDef(i, SimpleTypes.toInox(unifier.get(u)))
        }

        (sb, vd)
      }
      case UnnamedValDef(tpe) => for {
        (st, et) <- TypeE.elaborate(tpe, None)
      } yield {
        val i = FreshIdentifier(name)
        val sb = SimpleBindings.Binding(i, st)
        val evd = Eventual.withUnifier { implicit unifier =>
          trees.ValDef(i, et.get)
        }

        (sb, evd)
      }
    }
  }

  implicit object BindingSeqE extends HSeqE[Binding, String, trees.ValDef, (SimpleBindings.Binding, Eventual[trees.ValDef])] {
    override val elaborator = BindingE
    override def wrap(vd: trees.ValDef)(implicit store: Store): (SimpleBindings.Binding, Eventual[trees.ValDef]) =
      (SimpleBindings.fromInox(vd), Eventual.pure(vd))
  }
}