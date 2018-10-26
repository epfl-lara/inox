package inox
package parser
package elaboration
package elaborators

trait BindingElaborators { self: Elaborators =>

  import Bindings._

  object BindingE extends Elaborator[Binding, SimpleBindings.Binding] {

    override def elaborate(template: Binding)(implicit store: Store): Constrained[SimpleBindings.Binding] = template match {
      case BindingHole(index) => store.getHole[trees.ValDef](index) match {
        case None => Constrained.fail(invalidHoleType("ValDef")(template.pos))
        case Some(vd) => Constrained.attempt(SimpleBindings.fromInox(vd).map(_.forgetName), template, invalidInoxValDef(vd))
      }
      case ExplicitValDef(id, tpe) => for {
        (i, on) <- DefIdE.elaborate(id)
        (st, et) <- TypeE.elaborate(tpe)
      } yield SimpleBindings.Binding(i, st, Eventual.withUnifier { implicit unifier =>
        trees.ValDef(i, et.get)
      }, on)
      case InferredValDef(id) => {
        val u = SimpleTypes.Unknown.fresh.setPos(template.pos)
        for {
          (i, on) <- DefIdE.elaborate(id).addConstraint(Constraint.exist(u))
        } yield {

          val vd = Eventual.withUnifier { unifier =>
            trees.ValDef(i, SimpleTypes.toInox(unifier.get(u)))
          }
          val sb = SimpleBindings.Binding(i, u, vd, on)

          sb
        }
      }
    }
  }

  object BindingSeqE extends HSeqE[Binding, trees.ValDef, SimpleBindings.Binding]("ValDef") {

    override val elaborator = BindingE
    override def wrap(vd: trees.ValDef, where: IR)(implicit store: Store): Constrained[SimpleBindings.Binding] =
      Constrained.attempt(SimpleBindings.fromInox(vd).map(_.forgetName), where, invalidInoxValDef(vd))
  }
}