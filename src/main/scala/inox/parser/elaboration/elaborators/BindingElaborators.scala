package inox
package parser
package elaboration
package elaborators

trait BindingElaborators { self: Elaborators =>

  import Bindings._

  implicit object BindingE extends Elaborator[Binding, String, (SimpleTypes.Type, Eventual[trees.ValDef])] {
    override def elaborate(template: Binding, name: String)(implicit store: Store): Constrained[(SimpleTypes.Type, Eventual[trees.ValDef])] = template match {
      case BindingHole(index) => store.getHole[trees.ValDef](index) match {
        case None => Constrained.fail("TODO: Error")
        case Some(vd) => Constrained.pure((SimpleTypes.fromInox(vd.tpe), Eventual.pure(vd)))
      }
      case ExplicitValDef(id, tpe) => for {
        i <- IdE.elaborate(id, Modes.Def)
        (st, et) <- TypeE.elaborate(tpe, Some(i))
      } yield (st, Eventual.withUnifier { implicit unifier =>
        trees.ValDef(i, et.get)
      })
      case InferredValDef(id) => for {
        i <- IdE.elaborate(id, Modes.Def)
      } yield {

        val u = SimpleTypes.Unknown.fresh
        val vd = Eventual.withUnifier { unifier =>
          trees.ValDef(i, SimpleTypes.toInox(unifier.get(u)))
        }

        (u, vd)
      }
      case UnnamedValDef(tpe) => for {
        (st, et) <- TypeE.elaborate(tpe, None)
      } yield (st, Eventual.withUnifier { implicit unifier =>
        trees.ValDef(FreshIdentifier(name), et.get)
      })
    }
  }

  implicit object BindingSeqE extends HSeqE[Binding, String, trees.ValDef, (SimpleTypes.Type, Eventual[trees.ValDef])] {
    override val elaborator = BindingE
    override def wrap(vd: trees.ValDef)(implicit store: Store): (SimpleTypes.Type, Eventual[trees.ValDef]) =
      (SimpleTypes.fromInox(vd.tpe), Eventual.pure(vd))
  }
}