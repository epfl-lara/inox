/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

import scala.util.parsing.input._

import Utils.plural

trait TypeElaborators { self: Elaborators => 

  import Utils.{either, traverse, plural}

  trait TypeElaborator { self: Elaborator =>

    import TypeIR._

    private lazy val basicInv = basic.map(_.swap)

    private lazy val parametric: Map[Value, (Int, Seq[trees.Type] => trees.Type)] =
      (primitives ++ sorts).toMap

    private lazy val primitives = Seq(
      "Set" -> (1, (ts: Seq[trees.Type]) => trees.SetType(ts.head)),
      "Map" -> (2, (ts: Seq[trees.Type]) => trees.MapType(ts(0), ts(1))),
      "Bag" -> (1, (ts: Seq[trees.Type]) => trees.BagType(ts.head))).map({ case (n, v) => Name(n) -> v })

    private lazy val sorts = symbols.sorts.toSeq.flatMap({
      case (i, d) => {
        val f = (d.tparams.length, (ts: Seq[trees.Type]) => trees.ADTType(i, ts))

        Seq(
          Name(i.name) -> f,
          EmbeddedIdentifier(i) -> f)
      }
    })

    def getSimpleType(tpe: Expression)(using Store): trees.Type = {
      toSimpleType(tpe) match {
        case Right(inoxType) => inoxType
        case Left(errors) => throw new ElaborationException(errors)
      }
    }

    def toSimpleType(expr: Expression)(using store: Store): Either[Seq[ErrorLocation], trees.Type] = expr match {
      case Operation(Tuple | Sigma, irs) if irs.size >= 2 =>
        traverse(irs.map {
          case TypeBinding(_, tpe) => toSimpleType(tpe)
          case tpe => toSimpleType(tpe)
        }).left.map(_.flatten).map(trees.TupleType(_))

      case Operation(Arrow | Pi, Seq(Operation(Group, froms), to)) => 
        either(
          traverse(froms.map {
            case TypeBinding(_, tpe) => toSimpleType(tpe)
            case tpe => toSimpleType(tpe)
          }).left.map(_.flatten),
          toSimpleType(to)
        ){
          case (argTpes, retTpe) => trees.FunctionType(argTpes, retTpe)
        }

      case Refinement(_, tpe, _) => toSimpleType(tpe)

      case Application(l @ Literal(value), irs) =>
        either(
          parametric.get(value).orElse(value match {
            case Name(name) if store `isTypeParameter` name => None
            case Name(name) if store `isSort` name =>
              val sort = store `getSort` name
              Some((sort.tparams.length, (tps: Seq[trees.Type]) => trees.ADTType(sort.id, tps)))
            case _ => None
          }).map { case (n, cons) =>
            if (n == irs.length) {
              Right(cons)
            } else {
              Left(Seq(ErrorLocation("Type constructor " + value + " takes " +
                n + " " + plural(n, "argument", "arguments") + ", " +
                irs.length + " " + plural(irs.length, "was", "were") + " given.", l.pos)))
            }
          }.getOrElse {
            Left(Seq(ErrorLocation("Unknown type constructor: " + value, l.pos)))
          },
          traverse(irs.map(toSimpleType(_))).left.map(_.flatten)
        ){
          case (cons, tpes) => cons(tpes)
        }

      case Literal(EmbeddedType(t)) => Right(t)

      case Literal(Name(BVType(signed, size))) => Right(trees.BVType(signed, size))

      case l @ Literal(value) =>
        basic.get(value)
          .map(tpe => (0 -> ((tps: Seq[trees.Type]) => tpe)))
          .orElse(parametric.get(value))
          .orElse(value match {
            case Name(name) if store `isTypeParameter` name =>
              val tp = store `getTypeParameter` name
              Some((0, (tps: Seq[trees.Type]) => tp))
            case Name(name) if store `isSort` name =>
              val sort = store `getSort` name
              Some((sort.tparams.length, (tps: Seq[trees.Type]) => trees.ADTType(sort.id, tps)))
            case _ => None
          }).map { case (n, cons) =>
            if (n == 0) {
              Right(cons(Seq()))
            } else {
              Left(Seq(ErrorLocation("Type " + value + " expects " +
                n + " " + plural(n, "argument", "arguments") + ", none were given", l.pos)))
            }
          }.getOrElse {
            Left(Seq(ErrorLocation("Unknown type: " + value, l.pos)))
          }

      case _ => Left(Seq(ErrorLocation("Invalid type.", expr.pos)))
    }

    private def getTypeBindings(tps: Seq[(Option[ExprIR.Identifier], Expression)])
                               (using store0: Store): (Store, Constrained[Seq[trees.ValDef]]) = {
      val (newStore, vds) = tps.foldLeft((store0, Seq[Constrained[trees.ValDef]]())) {
        case ((store, vds), (oid, tpe)) =>
          getType(tpe)(using store) match {
            case unsat: Unsatisfiable => (store, vds :+ unsat)
            case c @ WithConstraints(ev, cs) => oid match {
              case Some(ident) =>
                val id = getIdentifier(ident)
                val newStore = store + (ident.getName, id, getSimpleType(tpe)(using store), ev)
                val newVds = vds :+ c.transform(tp => trees.ValDef(id, tp))
                (newStore, newVds)
              case None =>
                (store, vds :+ c.transform(tp => trees.ValDef.fresh("x", tp)))
            }
          }
      }

      (newStore, Constrained.sequence(vds))
    }

    def getType(expr: Expression, bound: Option[String] = None)
               (using store: Store): Constrained[trees.Type] = {
      given Position = expr.pos

      expr match {
        case Operation(Tuple, irs) if irs.size >= 2 =>
          Constrained.sequence({
            irs.map(getType(_))
          }).transform({
            trees.TupleType(_)
          })

        case Operation(Sigma, irs) if irs.size >= 2 =>
          val (newStore, bindings) = getTypeBindings(irs.init.map {
            case TypeBinding(id, tpe) => (Some(id), tpe)
            case tpe => (None, tpe)
          })

          bindings.combine(getType(irs.last)(using newStore))({
            case (params, to) => trees.SigmaType(params, to)
          })

        case Operation(Arrow, Seq(Operation(Group, froms), to)) =>
          Constrained.sequence({
            froms.map(getType(_))
          }).combine(getType(to))({
            case (from, to) => trees.FunctionType(from, to)
          })

        case Operation(Pi, Seq(Operation(Group, froms), to)) =>
          val (newStore, bindings) = getTypeBindings(froms.map {
            case TypeBinding(id, tpe) => (Some(id), tpe)
            case tpe => (None, tpe)
          })

          bindings.combine(getType(to)(using newStore))({
            case (params, to) => trees.PiType(params, to)
          })

        case Refinement(oid, tpe, pred) =>
          val ident = oid orElse bound.map(ExprIR.IdentifierName(_))
          val (newStore, vds) = getTypeBindings(Seq(ident -> tpe))

          val u = Unknown.fresh
          vds.combine(getExpr(pred, u)(using newStore))({
            case (Seq(vd), pred) => trees.RefinementType(vd, pred)
            case (vds, _) => 
              // there were 0 or > 1 bindings, should not happen
              throw new ElaborationException(Seq(ErrorLocation(s"Invalid refinement type elaboration, expected 1 binding, found ${vds.length}", expr.pos)))
          }).addConstraint({
            Constraint.equal(u, trees.BooleanType())
          })

        case Application(l @ Literal(value), irs) =>
          (parametric.get(value).orElse(value match {
            case Name(name) if store `isTypeParameter` name => None
            case Name(name) if store `isSort` name =>
              val sort = store `getSort` name
              Some((sort.tparams.length, (tps: Seq[trees.Type]) => trees.ADTType(sort.id, tps)))
            case _ => None
          }).map { case (n, cons) =>
            if (n == irs.length) {
              Constrained.pure(cons)
            } else {
              Constrained.fail("Type constructor " + value + " takes " +
                n + " " + plural(n, "argument", "arguments") + ", " +
                irs.length + " " + plural(irs.length, "was", "were") + " given.", l.pos)
            }
          }.getOrElse {
            Constrained.fail("Unknown type constructor: " + value, l.pos)
          }).combine(Constrained.sequence(irs.map(getType(_))))({
            case (cons, tpes) => cons(tpes)
          })

        case Literal(EmbeddedType(t)) => Constrained.pure(t)

        case Literal(Name(BVType(signed, size))) => Constrained.pure(trees.BVType(signed, size))

        case l @ Literal(value) =>
          basic.get(value)
            .map(tpe => (0 -> ((tps: Seq[trees.Type]) => tpe)))
            .orElse(parametric.get(value))
            .orElse(value match {
              case Name(name) if store `isTypeParameter` name =>
                val tp = store `getTypeParameter` name
                Some((0, (tps: Seq[trees.Type]) => tp))
              case Name(name) if store `isSort` name =>
                val sort = store `getSort` name
                Some((sort.tparams.length, (tps: Seq[trees.Type]) => trees.ADTType(sort.id, tps)))
              case _ => None
            }).map { case (n, cons) =>
              if (n == 0) {
                Constrained.pure(cons(Seq()))
              } else {
                Constrained.fail("Type " + value + " expects " +
                  n + " " + plural(n, "argument", "arguments") + ", none were given", l.pos)
              }
            }.getOrElse {
              Constrained.fail("Unknown type: " + value, l.pos)
            }

        case _ => Constrained.fail("Invalid type.", expr.pos)
      }
    }
  }
}
