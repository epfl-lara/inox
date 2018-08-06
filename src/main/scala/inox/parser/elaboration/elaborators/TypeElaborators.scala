package inox
package parser
package elaboration
package elaborators

trait TypeElaborators { self: Elaborators =>

  import Types._

  implicit object TypeE extends Elaborator[Type, Option[inox.Identifier], (SimpleTypes.Type, Eventual[trees.Type])] {
    override def elaborate(template: Type, context: Option[inox.Identifier])
                          (implicit store: Store): Constrained[(SimpleTypes.Type, Eventual[trees.Type])] = template match {
      case UnitType() => Constrained.pure((SimpleTypes.UnitType(), Eventual.pure(trees.UnitType())))
      case BooleanType() => Constrained.pure((SimpleTypes.BooleanType(), Eventual.pure(trees.BooleanType())))
      case BitVectorType(size) => Constrained.pure((SimpleTypes.BitVectorType(size), Eventual.pure(trees.BVType(size))))
      case CharType() => Constrained.pure((SimpleTypes.CharType(), Eventual.pure(trees.CharType())))
      case StringType() => Constrained.pure((SimpleTypes.StringType(), Eventual.pure(trees.StringType())))
      case IntegerType() => Constrained.pure((SimpleTypes.IntegerType(), Eventual.pure(trees.IntegerType())))
      case RealType() => Constrained.pure((SimpleTypes.RealType(), Eventual.pure(trees.RealType())))
      case SetType(tpe) => for {
        (st, et) <- TypeE.elaborate(tpe, None)
      } yield (SimpleTypes.SetType(st), et.map(trees.SetType(_)))
      case BagType(tpe) => for {
        (st, et) <- TypeE.elaborate(tpe, None)
      } yield (SimpleTypes.BagType(st), et.map(trees.BagType(_)))
      case MapType(from, to) => for {
        (sf, ef) <- TypeE.elaborate(from, None)
        (st, et) <- TypeE.elaborate(from, None)
      } yield (SimpleTypes.MapType(sf, st), Eventual.withUnifier(implicit u => trees.MapType(ef.get, et.get)))
      case TupleType(elems) => for {
        zes <- TypeSeqE.elaborate(elems, Seq.fill(elems.size)(None))
        (ses, ees) = zes.unzip
      } yield (SimpleTypes.TupleType(ses), Eventual.sequence(ees).map(trees.TupleType(_)))
      case FunctionType(froms, to) => for {
        zfs <- TypeSeqE.elaborate(froms, Seq.fill(froms.size)(None))
        (sfs, efs) = zfs.unzip
        (st, et) <- TypeE.elaborate(to, None)
      } yield (SimpleTypes.FunctionType(sfs, st), Eventual.withUnifier(implicit u => trees.FunctionType(efs.map(_.get), et.get)))
      case TypeParameter(id) => for {
        i <- IdE.elaborate(id, Modes.Use)
      } yield (SimpleTypes.TypeParameter(i), Eventual.pure(trees.TypeParameter(i, Seq())))
      case RefinementType(binding, pred) => {
        for {
          (st, ev) <- BindingE.elaborate(binding, context.map(_.name).getOrElse("x"))
          (pt, ep) <- ExprE.elaborate(pred, ()) // TODO: Update store.
          _ <- Constrained(Constraint.equal(pt, SimpleTypes.BooleanType()))
        } yield (st, Eventual.withUnifier(implicit u => trees.RefinementType(ev.get, ep.get)))
      }
    }
  }

  implicit object TypeSeqE extends HSeqE[Type, Option[inox.Identifier], trees.Type, (SimpleTypes.Type, Eventual[trees.Type])] {
    override val elaborator = TypeE

    override def wrap(tpe: trees.Type)(implicit store: Store): (SimpleTypes.Type, Eventual[trees.Type]) =
      (SimpleTypes.fromInox(tpe), Eventual.pure(tpe))
  }
}