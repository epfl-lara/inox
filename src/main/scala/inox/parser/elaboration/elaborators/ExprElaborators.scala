package inox
package parser
package elaboration
package elaborators

trait ExprElaborators { self: Elaborators =>

  import Exprs._

  object ExprE extends Elaborator[Expr, (SimpleTypes.Type, Eventual[trees.Expr])] {
    override def elaborate(template: Expr)(implicit store: Store): Constrained[(SimpleTypes.Type, Eventual[trees.Expr])] = template match {
      case ExprHole(index) => Constrained.attempt(store.getHole[trees.Expr](index), "TODO: Error").flatMap { expr =>
        Constrained.attempt(SimpleTypes.fromInox(expr.getType(store.getSymbols)), "TODO: Error").map { st =>
          (st, Eventual.pure(expr))
        }
      }
      case Variable(id) => for {
        i <- UseIdE.elaborate(id)
        (st, et) <- Constrained.attempt(store.getVariable(i), "TODO: Error, i is not a variable.")
      } yield (st, et.map(trees.Variable(i, _, Seq())))
      case UnitLiteral() =>
        Constrained.pure((SimpleTypes.UnitType(), Eventual.pure(trees.UnitLiteral())))
      case BooleanLiteral(value) =>
        Constrained.pure((SimpleTypes.BooleanType(), Eventual.pure(trees.BooleanLiteral(value))))
      case IntegerLiteral(value) => {
        val u = SimpleTypes.Unknown.fresh
        val v = Eventual.withUnifier { unifier =>
          unifier.get(u) match {
            case SimpleTypes.BitVectorType(size) => trees.BVLiteral(value, size)
            case SimpleTypes.IntegerType() => trees.IntegerLiteral(value)
            case SimpleTypes.RealType() => trees.FractionLiteral(value, 1)
            case _ => throw new IllegalStateException("Unifier returned unexpected value.")
          }
        }
        Constrained.pure((u, v)).addConstraint(Constraint.isNumeric(u))
      }
      case FractionLiteral(numerator, denominator) =>
        Constrained.pure((SimpleTypes.RealType(), Eventual.pure(trees.FractionLiteral(numerator, denominator))))
      case StringLiteral(string) =>
        Constrained.pure((SimpleTypes.StringType(), Eventual.pure(trees.StringLiteral(string))))
      case CharLiteral(value) =>
        Constrained.pure((SimpleTypes.CharType(), Eventual.pure(trees.CharLiteral(value))))
      case SetConstruction(optType, elems) => for {
        (st, et) <- OptTypeE.elaborate(optType)
        (sts, evs) <- ExprSeqE.elaborate(elems).map(_.unzip)
        _ <- Constrained(sts.map(Constraint.equal(_, st)) : _*)
      } yield (SimpleTypes.SetType(st), Eventual.withUnifier { implicit unifier =>
        trees.FiniteSet(evs.map(_.get), et.get)
      })
      case BagConstruction(optType, elems) => for {
        (st, et) <- OptTypeE.elaborate(optType)
        (stps, evps) <- ExprPairSeqE.elaborate(elems).map(_.unzip)
        (sks, sts) = stps.unzip
        _ <- Constrained(sks.map(Constraint.equal(_, SimpleTypes.IntegerType())) : _*)
        _ <- Constrained(sts.map(Constraint.equal(_, st)) : _*)
      } yield (SimpleTypes.BagType(st), Eventual.withUnifier { implicit unifier =>
        trees.FiniteBag(evps.map(_.get), et.get)
      })
      case MapConstruction(optTypes, elems, default) => for {
        (Seq(stf, stt), Seq(etf, ett)) <- optTypes
          .map(TypeSeqE.elaborate(_))
          .getOrElse(Constrained.sequence(Seq.fill(2) {
            OptTypeE.elaborate(None)
          }))
          .checkImmediate(_.size == 2, "TODO: Error: Wrong number arguments for Map.")
          .map(_.unzip)
        (stps, evps) <- ExprPairSeqE.elaborate(elems).map(_.unzip)
        (sks, sts) = stps.unzip
        (std, ed) <- ExprE.elaborate(default)
          .addConstraints(sks.map(Constraint.equal(_, stf)))
          .addConstraints(sts.map(Constraint.equal(_, stt)))
        _ <- Constrained(Constraint.equal(std, stt))
      } yield (SimpleTypes.MapType(stf, stt), Eventual.withUnifier { implicit unifier =>
        trees.FiniteMap(evps.map(_.get), ed.get, etf.get, ett.get)
      })
      case Abstraction(quantifier, bindings, body) => for {
        zs <- BindingSeqE.elaborate(bindings)
        newStore = store.addVariables(zs.map {
          case (SimpleBindings.Binding(i, st), evd) =>
            (i, st, evd.map(_.tpe))
        })
        (stb, evb) <- ExprE.elaborate(body)(newStore)
      } yield quantifier match {
        case Lambda =>
          (SimpleTypes.FunctionType(zs.map(_._1.tpe), stb), Eventual.withUnifier { implicit unifier =>
            trees.Lambda(zs.map(_._2.get), evb.get)
          })
        case Forall =>
          (SimpleTypes.BooleanType(), Eventual.withUnifier { implicit unifier =>
            trees.Forall(zs.map(_._2.get), evb.get)
          })
      }
      case Application(callee, args) => {
        val u = SimpleTypes.Unknown.fresh
        for {
          (stc, evc) <- ExprE.elaborate(callee)
          (sts, evs) <- ExprSeqE.elaborate(args).map(_.unzip)
          _ <- Constrained(Constraint.equal(SimpleTypes.FunctionType(sts, u), stc))
        } yield (u, Eventual.withUnifier { implicit unifier =>
          trees.Application(evc.get, evs.map(_.get))
        })
      }
      case Assume(condition, body) => for {
        (stc, evc) <- ExprE.elaborate(condition)
        (stb, evb) <- ExprE.elaborate(body).addConstraint(Constraint.equal(stc, SimpleTypes.BooleanType()))
      } yield (stb, Eventual.withUnifier { implicit unifier =>
        trees.Assume(evc.get, evb.get)
      })
      case Cast(Casts.Widen, expr, size) => for {
        (st, ev) <- ExprE.elaborate(expr)
        _ <- Constrained(Constraint.isBits(st, upper=Some(size - 1)))
      } yield (SimpleTypes.BitVectorType(size), ev.map(trees.BVWideningCast(_, trees.BVType(size))))
      case Cast(Casts.Narrow, expr, size) => for {
        (st, ev) <- ExprE.elaborate(expr)
        _ <- Constrained(Constraint.isBits(st, lower=Some(size + 1)))
      } yield (SimpleTypes.BitVectorType(size), ev.map(trees.BVNarrowingCast(_, trees.BVType(size))))
      case Choose(binding, body) => for {
        (sb, evd) <- BindingE.elaborate(binding)
        (st, evb) <- ExprE.elaborate(body)(store.addVariable(sb.id, sb.tpe, evd.map(_.tpe)))
      } yield (st, Eventual.withUnifier { implicit unifier =>
        trees.Choose(evd.get, evb.get)
      })
      case If(condition, thenn, elze) => for {
        (stc, evc) <- ExprE.elaborate(condition)
        (stt, evt) <- ExprE.elaborate(thenn).addConstraint(Constraint.equal(stc, SimpleTypes.BooleanType()))
        (ste, eve) <- ExprE.elaborate(elze)
        _ <- Constrained(Constraint.equal(stt, ste))
      } yield (stt, Eventual.withUnifier { implicit unifier =>
        trees.IfExpr(evc.get, evt.get, eve.get)
      })
      case Invocation(id, optTypeArgs, args) => for {
        i <- UseIdE.elaborate(id)
        ((n, f), isFun) <- Constrained.attempt(
          store.getFunction(i).map((_, true)).orElse(store.getConstructor(i).map((_, false))),
          "TODO: Error: i is not a function nor a constructor.")
        (sts, ets) <- optTypeArgs
          .map(TypeSeqE.elaborate(_))
          .getOrElse(Constrained.sequence(Seq.fill(n) {
            OptTypeE.elaborate(None)
          }))
          .checkImmediate(_.size == n, "TODO: Error: Wrong number of type arguments for constructor/function.")
          .map(_.unzip)
        (ests, rst) = f(sts)
        (stas, evas) <- ExprSeqE.elaborate(args)
          .checkImmediate(_.size == ests.size, "TODO: Error: Wrong number of arguments for constructor/function.")
          .map(_.unzip)
        _ <- Constrained(ests.zip(stas).map { case (est, ast) => Constraint.equal(est, ast) } : _*)
      } yield (rst, Eventual.withUnifier { implicit unifier =>
        if (isFun) {
          trees.FunctionInvocation(i, ets.map(_.get), evas.map(_.get))
        }
        else {
          trees.ADT(i, ets.map(_.get), evas.map(_.get))
        }
      })
      case PrimitiveInvocation(fun, optTypeArgs, args) => {
        import Primitive._

        optTypeArgs
          .map(TypeSeqE.elaborate(_))
          .getOrElse(Constrained.sequence(Seq.fill(fun.typeArgs) {
            OptTypeE.elaborate(None)
          }))
          .checkImmediate(_.size == fun.typeArgs, "TODO: Error: Wrong number of type arguments for primitive function.")
          .map(_.map(_._1))
          .flatMap { (typeArgs) =>

          ExprSeqE
            .elaborate(args)
            .checkImmediate(_.size == fun.args, "TODO: Error: Wrong number of arguments for primitive function.")
            .map(_.unzip)
            .flatMap { case (sts, evs) => fun match {
              case SetAdd =>
                Constrained
                  .pure((SimpleTypes.SetType(typeArgs(0)), Eventual.withUnifier { implicit unifier =>
                    trees.SetAdd(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.SetType(typeArgs(0))))
                  .addConstraint(Constraint.equal(sts(1), typeArgs(0)))
              case ElementOfSet =>
                Constrained
                  .pure((SimpleTypes.BooleanType(), Eventual.withUnifier { implicit unifier =>
                    trees.ElementOfSet(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), typeArgs(0)))
                  .addConstraint(Constraint.equal(sts(1), SimpleTypes.SetType(typeArgs(0))))
              case SetIntersection =>
                Constrained
                  .pure((SimpleTypes.SetType(typeArgs(0)), Eventual.withUnifier { implicit unifier =>
                    trees.SetIntersection(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.SetType(typeArgs(0))))
                  .addConstraint(Constraint.equal(sts(1), SimpleTypes.SetType(typeArgs(0))))
              case SetUnion =>
                Constrained
                  .pure((SimpleTypes.SetType(typeArgs(0)), Eventual.withUnifier { implicit unifier =>
                    trees.SetUnion(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.SetType(typeArgs(0))))
                  .addConstraint(Constraint.equal(sts(1), SimpleTypes.SetType(typeArgs(0))))
              case SetDifference =>
                Constrained
                  .pure((SimpleTypes.SetType(typeArgs(0)), Eventual.withUnifier { implicit unifier =>
                    trees.SetUnion(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.SetType(typeArgs(0))))
                  .addConstraint(Constraint.equal(sts(1), SimpleTypes.SetType(typeArgs(0))))
              case BagAdd =>
                Constrained
                  .pure((SimpleTypes.BagType(typeArgs(0)), Eventual.withUnifier { implicit unifier =>
                    trees.BagAdd(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.BagType(typeArgs(0))))
                  .addConstraint(Constraint.equal(sts(1), typeArgs(0)))
              case MultiplicityInBag =>
                Constrained
                  .pure((SimpleTypes.IntegerType(), Eventual.withUnifier { implicit unifier =>
                    trees.MultiplicityInBag(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), typeArgs(0)))
                  .addConstraint(Constraint.equal(sts(1), SimpleTypes.BagType(typeArgs(0))))
              case BagIntersection =>
                Constrained
                  .pure((SimpleTypes.BagType(typeArgs(0)), Eventual.withUnifier { implicit unifier =>
                    trees.BagIntersection(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.BagType(typeArgs(0))))
                  .addConstraint(Constraint.equal(sts(1), SimpleTypes.BagType(typeArgs(0))))
              case BagUnion =>
                Constrained
                  .pure((SimpleTypes.BagType(typeArgs(0)), Eventual.withUnifier { implicit unifier =>
                    trees.BagUnion(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.BagType(typeArgs(0))))
                  .addConstraint(Constraint.equal(sts(1), SimpleTypes.BagType(typeArgs(0))))
              case BagDifference =>
                Constrained
                  .pure((SimpleTypes.BagType(typeArgs(0)), Eventual.withUnifier { implicit unifier =>
                    trees.BagUnion(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.BagType(typeArgs(0))))
                  .addConstraint(Constraint.equal(sts(1), SimpleTypes.BagType(typeArgs(0))))
              case MapApply =>
                Constrained
                  .pure((typeArgs(1), Eventual.withUnifier { implicit unifier =>
                    trees.MapApply(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.MapType(typeArgs(0), typeArgs(1))))
                  .addConstraint(Constraint.equal(sts(1), typeArgs(0)))
              case MapUpdated =>
                Constrained
                  .pure((SimpleTypes.MapType(typeArgs(0), typeArgs(1)), Eventual.withUnifier { implicit unifier =>
                    trees.MapUpdated(evs(0).get, evs(1).get, evs(2).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.MapType(typeArgs(0), typeArgs(1))))
                  .addConstraint(Constraint.equal(sts(1), typeArgs(0)))
                  .addConstraint(Constraint.equal(sts(2), typeArgs(1)))
            }
          }
        }
      }
      case IsConstructor(expr, id) => for {
        (st, ev) <- ExprE.elaborate(expr)
        i <- UseIdE.elaborate(id)
        s <- Constrained.attempt(store.getSortOfConstructor(i), "TODO: Error: i is not a constructor.")
        n = store.getTypeConstructor(s).getOrElse { throw new IllegalStateException("Inconsistent store.") }
        _ <- Constrained(Constraint.equal(st, SimpleTypes.ADTType(i, Seq.fill(n)(SimpleTypes.Unknown.fresh))))
      } yield (SimpleTypes.BooleanType(), ev.map(trees.IsConstructor(_, i)))
      case Let(binding, value, expr) => for {
        (sb, evd) <- BindingE.elaborate(binding)
        (stv, ev) <- ExprE.elaborate(value)
        (ste, ee) <- ExprE.elaborate(expr)(store.addVariable(sb.id, sb.tpe, evd.map(_.tpe)))
          .addConstraint(Constraint.equal(sb.tpe, stv))
      } yield (ste, Eventual.withUnifier { implicit unifier =>
        trees.Let(evd.get, ev.get, ee.get)
      })
      case TupleSelection(expr, index) => for {
        (st, ev) <- ExprE.elaborate(expr)
        u = SimpleTypes.Unknown.fresh
        _ <- Constrained(Constraint.atIndexIs(st, index, u))
      } yield (u, ev.map(trees.TupleSelect(_, index)))
      case Selection(expr, id) => for {
        (st, ev) <- ExprE.elaborate(expr)
        pis <- FieldIdE.elaborate(id)
        adtType = SimpleTypes.Unknown.fresh
        retType = SimpleTypes.Unknown.fresh
        _ <- Constrained(Constraint.hasFields(st, pis.map(_._2.name).toSet, pis.map {
          case (sortId, fieldId) => (sortId, (tpe: SimpleTypes.Type) => {
            val n = store.getTypeConstructor(sortId).getOrElse {
              throw new IllegalStateException("Inconsistent store.")
            }
            val as = Seq.fill(n)(SimpleTypes.Unknown.fresh)
            val r = store.getTypeOfField(sortId, fieldId)(as)
            Seq(
              Constraint.equal(adtType, tpe),
              Constraint.equal(r, retType),
              Constraint.equal(tpe, SimpleTypes.ADTType(sortId, as)))
          })
        }))
      } yield (retType, Eventual.withUnifier { implicit unifier =>
        val sortId = unifier.get(adtType) match {
          case SimpleTypes.ADTType(i, _) => i
          case _ => throw new IllegalStateException("Unifier returned unexpected value.")
        }
        val fieldId = pis.toMap.get(sortId).getOrElse {
          throw new IllegalStateException("Unifier returned unexpected value.")
        }
        trees.ADTSelector(ev.get, fieldId)
      })
      case TypeAnnotation(expr, tpe) => for {
        (ste, ev) <- ExprE.elaborate(expr)
        (stt, _) <- TypeE.elaborate(tpe)
        _ <- Constrained(Constraint.equal(ste, stt))
      } yield (stt, ev)
      case UnaryOperation(op, arg) => ExprE.elaborate(arg).flatMap { case (st, ev) =>
        import Unary._

        op match {
          case Minus =>
            Constrained
              .pure((st, ev.map(trees.UMinus(_))))
              .addConstraint(Constraint.isNumeric(st))
          case Not =>
            Constrained
              .pure((st, ev.map(trees.Not(_))))
              .addConstraint(Constraint.equal(st, SimpleTypes.BooleanType()))
          case BVNot =>
            Constrained
              .pure((st, ev.map(trees.BVNot(_))))
              .addConstraint(Constraint.isBits(st))
          case StringLength =>
            Constrained
              .pure((SimpleTypes.IntegerType(), ev.map(trees.StringLength(_))))
              .addConstraint(Constraint.equal(st, SimpleTypes.StringType()))
        }
      }
      case BinaryOperation(op, arg1, arg2) => ExprE.elaborate(arg1).flatMap { case (st1, ev1) =>
        ExprE.elaborate(arg2).flatMap { case (st2, ev2) =>
          import Binary._
          op match {
            case Plus =>
              Constrained
                .pure((st1, Eventual.withUnifier { implicit unifier => trees.Plus(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, st2))
                .addConstraint(Constraint.isNumeric(st1))
            case Minus =>
              Constrained
                .pure((st1, Eventual.withUnifier { implicit unifier => trees.Minus(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, st2))
                .addConstraint(Constraint.isNumeric(st1))
            case Times =>
              Constrained
                .pure((st1, Eventual.withUnifier { implicit unifier => trees.Times(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, st2))
                .addConstraint(Constraint.isNumeric(st1))
            case Division =>
              Constrained
                .pure((st1, Eventual.withUnifier { implicit unifier => trees.Division(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, st2))
                .addConstraint(Constraint.isNumeric(st1))
            case Modulo =>
              Constrained
                .pure((st1, Eventual.withUnifier { implicit unifier => trees.Modulo(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, st2))
                .addConstraint(Constraint.isIntegral(st1))
            case Remainder =>
              Constrained
                .pure((st1, Eventual.withUnifier { implicit unifier => trees.Remainder(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, st2))
                .addConstraint(Constraint.isIntegral(st1))
            case Implies =>
              Constrained
                .pure((SimpleTypes.BooleanType(), Eventual.withUnifier { implicit unifier => trees.Implies(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, SimpleTypes.BooleanType()))
                .addConstraint(Constraint.equal(st2, SimpleTypes.BooleanType()))
            case Equals =>
              Constrained
                .pure((SimpleTypes.BooleanType(), Eventual.withUnifier { implicit unifier => trees.Equals(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, st2))
            case LessEquals =>
              Constrained
                .pure((SimpleTypes.BooleanType(), Eventual.withUnifier { implicit unifier => trees.LessEquals(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, st2))
                .addConstraint(Constraint.isComparable(st1))
            case LessThan =>
              Constrained
                .pure((SimpleTypes.BooleanType(), Eventual.withUnifier { implicit unifier => trees.LessThan(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, st2))
                .addConstraint(Constraint.isComparable(st1))
            case GreaterEquals =>
              Constrained
                .pure((SimpleTypes.BooleanType(), Eventual.withUnifier { implicit unifier => trees.GreaterEquals(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, st2))
                .addConstraint(Constraint.isComparable(st1))
            case GreaterThan =>
              Constrained
                .pure((SimpleTypes.BooleanType(), Eventual.withUnifier { implicit unifier => trees.GreaterThan(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, st2))
                .addConstraint(Constraint.isComparable(st1))
            case BVAnd =>
              Constrained
                .pure((st1, Eventual.withUnifier { implicit unifier => trees.BVAnd(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, st2))
                .addConstraint(Constraint.isBits(st1))
            case BVOr =>
              Constrained
                .pure((st1, Eventual.withUnifier { implicit unifier => trees.BVOr(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, st2))
                .addConstraint(Constraint.isBits(st1))
            case BVXor =>
              Constrained
                .pure((st1, Eventual.withUnifier { implicit unifier => trees.BVXor(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, st2))
                .addConstraint(Constraint.isBits(st1))
            case BVShiftLeft =>
              Constrained
                .pure((st1, Eventual.withUnifier { implicit unifier => trees.BVShiftLeft(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, st2))
                .addConstraint(Constraint.isBits(st1))
            case BVAShiftRight =>
              Constrained
                .pure((st1, Eventual.withUnifier { implicit unifier => trees.BVAShiftRight(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, st2))
                .addConstraint(Constraint.isBits(st1))
            case BVLShiftRight =>
              Constrained
                .pure((st1, Eventual.withUnifier { implicit unifier => trees.BVLShiftRight(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, st2))
                .addConstraint(Constraint.isBits(st1))
            case StringConcat =>
              Constrained
                .pure((SimpleTypes.StringType(), Eventual.withUnifier { implicit unifier => trees.StringConcat(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, SimpleTypes.StringType()))
                .addConstraint(Constraint.equal(st2, SimpleTypes.StringType()))
          }
        }
      }
      case TernaryOperation(Ternary.SubString, arg1, arg2, arg3) => for {
        (st1, ev1) <- ExprE.elaborate(arg1)
        (st2, ev2) <- ExprE.elaborate(arg2)
        (st3, ev3) <- ExprE.elaborate(arg3)
        _ <- Constrained(Constraint.equal(st1, SimpleTypes.StringType()))
        _ <- Constrained(Constraint.equal(st2, SimpleTypes.IntegerType()))
        _ <- Constrained(Constraint.equal(st3, SimpleTypes.IntegerType()))
      } yield (SimpleTypes.StringType(), Eventual.withUnifier { implicit unifier =>
        trees.SubString(ev1.get, ev2.get, ev3.get)
      })
      case NaryOperation(op, args) => ExprSeqE.elaborate(args).map(_.unzip).flatMap { case (sts, evs) =>
        import NAry._

        op match {
          case And =>
            Constrained
              .pure((SimpleTypes.BooleanType(), Eventual.sequence(evs).map(trees.And(_))))
              .addConstraints(sts.map(Constraint.equal(_, SimpleTypes.BooleanType())))
          case Or =>
            Constrained
              .pure((SimpleTypes.BooleanType(), Eventual.sequence(evs).map(trees.Or(_))))
              .addConstraints(sts.map(Constraint.equal(_, SimpleTypes.BooleanType())))
        }
      }
    }
  }

  object ExprSeqE extends HSeqE[Expr, trees.Expr, (SimpleTypes.Type, Eventual[trees.Expr])] {
    override val elaborator = ExprE
    override def wrap(expr: trees.Expr)(implicit store: Store): Constrained[(SimpleTypes.Type, Eventual[trees.Expr])] =
      Constrained.attempt(SimpleTypes.fromInox(expr.getType(store.getSymbols)).map { st =>
        (st, Eventual.pure(expr))
      }, "TODO: Error")
  }

  object ExprPairE extends Elaborator[ExprPair, ((SimpleTypes.Type, SimpleTypes.Type), Eventual[(trees.Expr, trees.Expr)])] {
    override def elaborate(pair: ExprPair)(implicit store: Store):
        Constrained[((SimpleTypes.Type, SimpleTypes.Type), Eventual[(trees.Expr, trees.Expr)])] = pair match {
      case PairHole(index) => Constrained.attempt(store.getHole[(trees.Expr, trees.Expr)](index), "TODO: Error").flatMap {
        case p@(lhs, rhs) => for {
          stl <- Constrained.attempt(SimpleTypes.fromInox(lhs.getType(store.getSymbols)), "TODO: Error")
          str <- Constrained.attempt(SimpleTypes.fromInox(rhs.getType(store.getSymbols)), "TODO: Error")
        } yield ((stl, str), Eventual.pure(p))
      }
      case Pair(lhs, rhs) => for {
        (stl, evl) <- ExprE.elaborate(lhs)
        (str, evr) <- ExprE.elaborate(rhs)
      } yield ((stl, str), Eventual.withUnifier { implicit unifier => (evl.get, evr.get) })
    }
  }

  object ExprPairSeqE extends HSeqE[ExprPair, (trees.Expr, trees.Expr), ((SimpleTypes.Type, SimpleTypes.Type), Eventual[(trees.Expr, trees.Expr)])] {
    override val elaborator = ExprPairE
    override def wrap(pair: (trees.Expr, trees.Expr))(implicit store: Store):
        Constrained[((SimpleTypes.Type, SimpleTypes.Type), Eventual[(trees.Expr, trees.Expr)])] = for {
      stl <- Constrained.attempt(SimpleTypes.fromInox(pair._1.getType(store.getSymbols)), "TODO: Error")
      str <- Constrained.attempt(SimpleTypes.fromInox(pair._2.getType(store.getSymbols)), "TODO: Error")
    } yield ((stl, str), Eventual.pure(pair))
  }
}