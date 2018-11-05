package inox
package parser
package elaboration
package elaborators

import scala.util.parsing.input.Position

trait TypeElaborators { self: Elaborators =>

  import Types._

  class TypeE extends Elaborator[Type, (SimpleTypes.Type, Eventual[trees.Type])] {
    override def elaborate(template: Type)(implicit store: Store): Constrained[(SimpleTypes.Type, Eventual[trees.Type])] = template match {
      case TypeHole(index) => for {
        t <- Constrained.attempt(store.getHole[trees.Type](index), template, invalidHoleType("Type"))
        st <- Constrained.attempt(SimpleTypes.fromInox(t).map(_.setPos(template.pos)), template, invalidInoxType(t))
      } yield (st, Eventual.pure(t))
      case Variable(id) => for {
        i <- TypeUseIdE.elaborate(id)
        (st, et) <- Constrained.attempt(store.getType(i).orElse(store.getTypeConstructor(i).flatMap { (n: Int) =>
          if (n == 0) Some((SimpleTypes.ADTType(i, Seq()), Eventual.pure(trees.ADTType(i, Seq()))))
          else None
        }), template, typeConstructorUsedAsTypeVariable(i.name))
      } yield (st.withPos(template.pos), et)
      case Primitive(tpe) => {
        import Primitives._
        val st = tpe match {
          case UnitType => SimpleTypes.UnitType().setPos(template.pos)
          case BooleanType => SimpleTypes.BooleanType().setPos(template.pos)
          case BVType(size) => SimpleTypes.BitVectorType(size).setPos(template.pos)
          case IntegerType => SimpleTypes.IntegerType().setPos(template.pos)
          case RealType => SimpleTypes.RealType().setPos(template.pos)
          case StringType => SimpleTypes.StringType().setPos(template.pos)
          case CharType => SimpleTypes.CharType().setPos(template.pos)
        }
        Constrained.pure((st, Eventual.pure(SimpleTypes.toInox(st))))
      }
      case Operation(Operators.Set, args) => for {
        zs <- TypeSeqE.elaborate(args)
        _ <- Constrained.checkImmediate(zs.size == 1, template, wrongNumberOfTypeArguments("Set", 1, zs.size))
      } yield {
        val Seq((st, et)) = zs
        (SimpleTypes.SetType(st).setPos(template.pos), et.map(trees.SetType(_)))
      }
      case Operation(Operators.Bag, args) => for {
        zs <- TypeSeqE.elaborate(args)
        _ <- Constrained.checkImmediate(zs.size == 1, template, wrongNumberOfTypeArguments("Bag", 1, zs.size))
      } yield {
        val Seq((st, et)) = zs
        (SimpleTypes.BagType(st).setPos(template.pos), et.map(trees.BagType(_)))
      }
      case Operation(Operators.Map, args) => for {
        zs <- TypeSeqE.elaborate(args)
        _ <- Constrained.checkImmediate(zs.size == 2, template, wrongNumberOfTypeArguments("Map", 2, zs.size))
      } yield {
        val Seq((sf, ef), (st, et)) = zs
        (SimpleTypes.MapType(sf, st).setPos(template.pos), Eventual.withUnifier { implicit u =>
          trees.MapType(ef.get, et.get)
        })
      }
      case Invocation(id, args) => for {
        i <- TypeUseIdE.elaborate(id)
        n <- Constrained.attempt(store.getTypeConstructor(i), template, typeVariableUsedAsTypeConstructor(i.name))
        zas <- TypeSeqE.elaborate(args)
        _ <- Constrained.checkImmediate(n == zas.size, template, wrongNumberOfTypeArguments(i.name, n, zas.size))
        (sas, eas) = zas.unzip
      } yield (SimpleTypes.ADTType(i, sas).setPos(template.pos), Eventual.withUnifier { implicit u =>
        trees.ADTType(i, eas.map(_.get))
      })
      case TupleType(elems) => for {
        zes <- TypeSeqE.elaborate(elems)
        (ses, ees) = zes.unzip
      } yield (SimpleTypes.TupleType(ses).setPos(template.pos), Eventual.sequence(ees).map(trees.TupleType(_)))
      case FunctionType(froms, to) => for {
        zfs <- TypeSeqE.elaborate(froms)
        (sfs, efs) = zfs.unzip
        (st, et) <- TypeE.elaborate(to)
      } yield (SimpleTypes.FunctionType(sfs, st).setPos(template.pos), Eventual.withUnifier(implicit u => trees.FunctionType(efs.map(_.get), et.get)))
      case RefinementType(binding, pred) => for {
        sb <- BindingE.elaborate(binding)
        (pt, ep) <- ExprE.elaborate(pred)(store.addBinding(sb))
        _ <- Constrained(Constraint.equal(pt, SimpleTypes.BooleanType().setPos(template.pos)))
      } yield (sb.tpe, Eventual.withUnifier(implicit u => trees.RefinementType(sb.evValDef.get, ep.get)))
      case SigmaType(bindings, to) => for {
        bs <- BindingSeqE.elaborate(bindings)
        (st, et) <- TypeE.elaborate(to)(store.addBindings(bs))
      } yield (SimpleTypes.TupleType(bs.map(_.tpe) :+ st).setPos(template.pos), Eventual.withUnifier { implicit u =>
        trees.SigmaType(bs.map(_.evValDef.get), et.get)
      })
      case PiType(bindings, to) => for {
        bs <- BindingSeqE.elaborate(bindings)
        (st, et) <- TypeE.elaborate(to)(store.addBindings(bs))
      } yield (SimpleTypes.FunctionType(bs.map(_.tpe), st).setPos(template.pos), Eventual.withUnifier { implicit u =>
        trees.PiType(bs.map(_.evValDef.get), et.get)
      })
    }
  }
  val TypeE = new TypeE

  class OptTypeE extends Elaborator[Either[Position, Type], (SimpleTypes.Type, Eventual[trees.Type])] {
    override def elaborate(optType: Either[Position, Type])(implicit store: Store):
        Constrained[(SimpleTypes.Type, Eventual[trees.Type])] = optType match {
      case Right(tpe) => TypeE.elaborate(tpe)
      case Left(pos) => {
        val u = SimpleTypes.Unknown.fresh.setPos(pos)

        Constrained
          .pure((u, Eventual.withUnifier { unifier => SimpleTypes.toInox(unifier.get(u)) }))
          .addConstraint(Constraint.exist(u))
      }
    }
  }
  val OptTypeE = new OptTypeE

  class TypeSeqE extends HSeqE[Type, trees.Type, (SimpleTypes.Type, Eventual[trees.Type])]("Type") {
    override val elaborator = TypeE

    override def wrap(tpe: trees.Type, where: IR)(implicit store: Store): Constrained[(SimpleTypes.Type, Eventual[trees.Type])] =
      Constrained.attempt(SimpleTypes.fromInox(tpe).map(_.setPos(where.pos)), where, invalidInoxType(tpe)).map { st => (st, Eventual.pure(tpe)) }
  }
  val TypeSeqE = new TypeSeqE
}