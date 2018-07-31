/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

import scala.util.parsing.input._

import Utils.plural

trait TypeElaborators { self: Elaborators =>

  import Utils.{either, traverse, plural}

  trait TypeElaborator { self: Elaborator =>

    import TypeIR._

    def replaceHoles(tpe: Expression)(implicit holes: HoleValues, dummy: DummyImplicit): Expression = tpe match {
      case TypeHole(i) => Literal(EmbeddedType(holes.getType(i).get))
      case Operation(operator, args) => Operation(operator, args.flatMap(replaceHolesSeq(_)))
      case Application(callee, args) => {
        val replacedCallee = callee match {
          case NameHole(i) => Literal(EmbeddedIdentifier(holes.getIdentifier(i).get))
          case _ => replaceHoles(callee)
        }

        Application(replacedCallee, args.flatMap(replaceHolesSeq(_)))
      }
      case Refinement(optId, tpe, pred) => Refinement(optId.map(replaceHoles(_)), replaceHoles(tpe), replaceHoles(pred))
      case TypeBinding(id, tpe) => TypeBinding(replaceHoles(id), replaceHoles(tpe))
      case Literal(_) => tpe
    }

    def replaceHolesSeq(tpe: Expression)(implicit holes: HoleValues, dummy: DummyImplicit): Seq[Expression] = tpe match {
      case TypeSeqHole(i) => holes.getTypeSeq(i).get.map(t => Literal(EmbeddedType(t)))
      case _ => Seq(replaceHoles(tpe))
    }

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

    def getSimpleType(tpe: Expression)(implicit store: Store): trees.Type = {
      toSimpleType(tpe) match {
        case Right(inoxType) => inoxType
        case Left(errors) => throw new ElaborationException(errors)
      }
    }

    def toSimpleType(expr: Expression)(implicit store: Store): Either[Seq[ErrorLocation], trees.Type] = expr match {
      case Operation(Tuple | Sigma, irs) if irs.size >= 2 =>
        traverse(irs.map {
          case TypeBinding(_, tpe) => toSimpleType(tpe)
          case tpe => toSimpleType(tpe)
        }).left.map(_.flatten).right.map(trees.TupleType(_))

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
            case Name(name) if store isTypeParameter name => None
            case Name(name) if store isSort name =>
              val sort = store getSort name
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

      case Literal(EmbeddedType(t)) => Right(t)  // This seems wrong. What if t is not simple ?

      case Literal(Name(BVType(size))) => Right(trees.BVType(size))

      case l @ Literal(value) =>
        basic.get(value)
          .map(tpe => (0 -> ((tps: Seq[trees.Type]) => tpe)))
          .orElse(parametric.get(value))
          .orElse(value match {
            case Name(name) if store isTypeParameter name =>
              val tp = store getTypeParameter name
              Some((0, (tps: Seq[trees.Type]) => tp))
            case Name(name) if store isSort name =>
              val sort = store getSort name
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
                               (implicit store: Store): (Store, Constrained[Seq[trees.ValDef]]) = {
      val (newStore, vds) = tps.foldLeft((store, Seq[Constrained[trees.ValDef]]())) {
        case ((store, vds), (oid, tpe)) =>
          getType(tpe)(store) match {
            case unsat: Unsatisfiable => (store, vds :+ unsat)
            case c @ WithConstraints(ev, cs) => oid match {
              case Some(ident) =>
                val id = getIdentifier(ident)
                val newStore = store + (ident.getName, id, getSimpleType(tpe)(store), ev)
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
               (implicit store: Store): Constrained[trees.Type] = {
      implicit val position: Position = expr.pos

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

          bindings.combine(getType(irs.last)(newStore))({
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

          bindings.combine(getType(to)(newStore))({
            case (params, to) => trees.PiType(params, to)
          })

        case Refinement(oid, tpe, pred) =>
          val ident = oid orElse bound.map(ExprIR.IdentifierName(_))
          val (newStore, vds) = getTypeBindings(Seq(ident -> tpe))

          val u = Unknown.fresh
          vds.combine(getExpr(pred, u)(newStore))({
            case (Seq(vd), pred) => trees.RefinementType(vd, pred)
          }).addConstraint({
            Constraint.equal(u, trees.BooleanType())
          })

        case Application(l @ Literal(value), irs) =>
          (parametric.get(value).orElse(value match {
            case Name(name) if store isTypeParameter name => None
            case Name(name) if store isSort name =>
              val sort = store getSort name
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

        case Literal(Name(BVType(size))) => Constrained.pure(trees.BVType(size))

        case l @ Literal(value) =>
          basic.get(value)
            .map(tpe => (0 -> ((tps: Seq[trees.Type]) => tpe)))
            .orElse(parametric.get(value))
            .orElse(value match {
              case Name(name) if store isTypeParameter name =>
                val tp = store getTypeParameter name
                Some((0, (tps: Seq[trees.Type]) => tp))
              case Name(name) if store isSort name =>
                val sort = store getSort name
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
