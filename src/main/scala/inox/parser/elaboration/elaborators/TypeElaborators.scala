package inox
package parser
package elaboration
package elaborators

trait TypeElaborators { self: Elaborators =>

  import Types._

  object TypeE extends Elaborator[Type, (SimpleTypes.Type, Eventual[trees.Type])] {
    override def elaborate(template: Type)(implicit store: Store): Constrained[(SimpleTypes.Type, Eventual[trees.Type])] = template match {
      case Variable(id) => for {
        i <- UseIdE.elaborate(id)
        (st, et) <- Constrained.attempt(store.getType(i), "TODO: Error: i is not a type.")
      } yield (st, et)
      case Invocation(id, args) => for {
        i <- UseIdE.elaborate(id)
        (n, stc, etc) <- Constrained.attempt(store.getTypeConstructor(i), "TODO: Error: i is not a type constructor.")
        zas <- TypeSeqE.elaborate(args)
        _ <- Constrained.checkImmediate(n == zas.size, "TODO: Error: wrong number of arguments.")
        (sas, eas) = zas.unzip
      } yield (stc(sas), Eventual.withUnifier { implicit u =>
        etc.get.apply(eas.map(_.get))
      })
      case TupleType(elems) => for {
        zes <- TypeSeqE.elaborate(elems)
        (ses, ees) = zes.unzip
      } yield (SimpleTypes.TupleType(ses), Eventual.sequence(ees).map(trees.TupleType(_)))
      case FunctionType(froms, to) => for {
        zfs <- TypeSeqE.elaborate(froms)
        (sfs, efs) = zfs.unzip
        (st, et) <- TypeE.elaborate(to)
      } yield (SimpleTypes.FunctionType(sfs, st), Eventual.withUnifier(implicit u => trees.FunctionType(efs.map(_.get), et.get)))
      case RefinementType(binding, pred) => for {
        (sb, ev) <- BindingE.elaborate(binding)
        (pt, ep) <- ExprE.elaborate(pred)(store.addVariable(sb.id, sb.tpe, ev.map(_.tpe)))
        _ <- Constrained(Constraint.equal(pt, SimpleTypes.BooleanType()))
      } yield (sb.tpe, Eventual.withUnifier(implicit u => trees.RefinementType(ev.get, ep.get)))
      case SigmaType(bindings, to) => for {
        zs <- BindingSeqE.elaborate(bindings)
        triples = zs.map {
          case (sb, evd) => (sb.id, sb.tpe, evd.map(_.tpe))
        }
        (st, et) <- TypeE.elaborate(to)(store.addVariables(triples))
      } yield (SimpleTypes.TupleType(zs.map(_._1.tpe) :+ st), Eventual.withUnifier { implicit u =>
        trees.SigmaType(zs.map(_._2.get), et.get)
      })
      case PiType(bindings, to) => for {
        zs <- BindingSeqE.elaborate(bindings)
        triples = zs.map {
          case (sb, evd) => (sb.id, sb.tpe, evd.map(_.tpe))
        }
        (st, et) <- TypeE.elaborate(to)(store.addVariables(triples))
      } yield (SimpleTypes.FunctionType(zs.map(_._1.tpe), st), Eventual.withUnifier { implicit u =>
        trees.PiType(zs.map(_._2.get), et.get)
      })
    }
  }

  implicit object TypeSeqE extends HSeqE[Type, trees.Type, (SimpleTypes.Type, Eventual[trees.Type])] {
    override val elaborator = TypeE

    override def wrap(tpe: trees.Type)(implicit store: Store): (SimpleTypes.Type, Eventual[trees.Type]) =
      (SimpleTypes.fromInox(tpe), Eventual.pure(tpe))
  }
}