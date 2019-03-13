package inox
package parser
package elaboration
package elaborators

trait BindingElaborators { self: Elaborators =>

  import Bindings._

  class BindingE extends Elaborator[Binding, SimpleBindings.Binding] {

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
  val BindingE = new BindingE

  class BindingSeqE extends HSeqE[Binding, trees.ValDef, SimpleBindings.Binding]("ValDef") {

    override val elaborator = BindingE
    override def wrap(vd: trees.ValDef, where: IR)(implicit store: Store): Constrained[SimpleBindings.Binding] =
      Constrained.attempt(SimpleBindings.fromInox(vd).map(_.forgetName), where, invalidInoxValDef(vd))

    override def elaborate(template: HSeq[Binding])(implicit store: Store): Constrained[Seq[SimpleBindings.Binding]] = {
      val elems = template.elems

      val sequence = elems.foldRight((store: Store) => Constrained.pure(Seq[SimpleBindings.Binding]())) {
        case (x, f) => (store: Store) => x match {
          case Left(r) => {
            val c: Constrained[Seq[SimpleBindings.Binding]] = store.getHole[Seq[trees.ValDef]](r.index) match {
              case None => Constrained.fail(invalidHoleType("Seq[ValDef]")(r.pos))
              case Some(xs) => Constrained.sequence(xs.map(wrap(_, r)(store)))
            }

            c.flatMap { (as: Seq[SimpleBindings.Binding]) =>
              f(store).map((bs: Seq[SimpleBindings.Binding]) => as ++ bs)
            }
          }
          case Right(t) => elaborator.elaborate(t)(store).flatMap { (b: SimpleBindings.Binding) =>
            f(store.addBinding(b)).map((bs: Seq[SimpleBindings.Binding]) => b +: bs)
          }
        }
      }

      sequence(store)
    }
  }
  val BindingSeqE = new BindingSeqE
}