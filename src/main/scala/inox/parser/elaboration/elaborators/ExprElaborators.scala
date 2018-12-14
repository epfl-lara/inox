package inox
package parser
package elaboration
package elaborators

trait ExprElaborators { self: Elaborators =>

  import Exprs._

  class ExprE extends Elaborator[Expr, (SimpleTypes.Type, Eventual[trees.Expr])] {
    override def elaborate(template: Expr)(implicit store: Store): Constrained[(SimpleTypes.Type, Eventual[trees.Expr])] = template match {
      case ExprHole(index) => Constrained.attempt(store.getHole[trees.Expr](index), template, invalidHoleType("Expr")).flatMap { expr =>
        Constrained.attempt(SimpleTypes.fromInox(expr.getType(store.getSymbols)).map(_.setPos(template.pos)), template, invalidInoxExpr(expr)).map { st =>
          (st, Eventual.pure(expr))
        }
      }
      case Variable(id) => for {
        i <- ExprUseIdE.elaborate(id)
        (st, et) <- Constrained.attempt(store.getVariable(i), template, functionUsedAsVariable(i.name))
      } yield (st.withPos(template.pos), et.map(trees.Variable(i, _, Seq())))
      case UnitLiteral() =>
        Constrained.pure((SimpleTypes.UnitType().setPos(template.pos), Eventual.pure(trees.UnitLiteral())))
      case BooleanLiteral(value) =>
        Constrained.pure((SimpleTypes.BooleanType().setPos(template.pos), Eventual.pure(trees.BooleanLiteral(value))))
      case IntegerLiteral(value) => {
        val u = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val v = Eventual.withUnifier { unifier =>
          unifier.get(u) match {
            case SimpleTypes.BitVectorType(true, size) => trees.BVLiteral(true, value, size)
            case SimpleTypes.BitVectorType(false, size) => {
              if (value >= 0) {
                trees.BVLiteral(false, value, size)
              }
              else {
                val complement = value.mod(BigInt(2).pow(size))
                trees.BVLiteral(false, complement, size)
              }
            }
            case SimpleTypes.IntegerType() => trees.IntegerLiteral(value)
            case SimpleTypes.RealType() => trees.FractionLiteral(value, 1)
            case _ => throw new IllegalStateException("Unifier returned unexpected value.")
          }
        }
        Constrained.pure((u, v)).addConstraint(Constraint.isNumeric(u))
      }
      case FractionLiteral(numerator, denominator) =>
        Constrained.pure((SimpleTypes.RealType().setPos(template.pos), Eventual.pure(trees.FractionLiteral(numerator, denominator))))
      case StringLiteral(string) =>
        Constrained.pure((SimpleTypes.StringType().setPos(template.pos), Eventual.pure(trees.StringLiteral(string))))
      case CharLiteral(value) =>
        Constrained.pure((SimpleTypes.CharType().setPos(template.pos), Eventual.pure(trees.CharLiteral(value))))
      case SetConstruction(optTypes, elems) => for {
        (st, et) <- optTypes
          .map(TypeSeqE.elaborate(_))
          .getOrElse(Constrained.sequence(Seq.fill(1) {
            OptTypeE.elaborate(Left(template.pos))
          }))
          .checkImmediate(_.size == 1, template, xs => wrongNumberOfTypeArguments("Set", 1, xs.size))
          .map(_.head)
        (sts, evs) <- ExprSeqE.elaborate(elems).map(_.unzip)
        _ <- Constrained(sts.map(Constraint.equal(_, st)) : _*)
      } yield (SimpleTypes.SetType(st).setPos(template.pos), Eventual.withUnifier { implicit unifier =>
        trees.FiniteSet(evs.map(_.get), et.get)
      })
      case BagConstruction(optTypes, elems) => for {
        (st, et) <- optTypes
          .map(TypeSeqE.elaborate(_))
          .getOrElse(Constrained.sequence(Seq.fill(1) {
            OptTypeE.elaborate(Left(template.pos))
          }))
          .checkImmediate(_.size == 1, template, xs => wrongNumberOfTypeArguments("Set", 1, xs.size))
          .map(_.head)
        (stps, evps) <- ExprPairSeqE.elaborate(elems).map(_.unzip)
        (sks, sts) = stps.unzip
        _ <- Constrained(sks.map(Constraint.equal(_, st)) : _*)
        _ <- Constrained(sts.map(Constraint.equal(_, SimpleTypes.IntegerType().setPos(template.pos))) : _*)
      } yield (SimpleTypes.BagType(st).setPos(template.pos), Eventual.withUnifier { implicit unifier =>
        trees.FiniteBag(evps.map(_.get), et.get)
      })
      case MapConstruction(optTypes, elems, default) => for {
        (Seq(stf, stt), Seq(etf, ett)) <- optTypes
          .map(TypeSeqE.elaborate(_))
          .getOrElse(Constrained.sequence(Seq.fill(2) {
            OptTypeE.elaborate(Left(template.pos))
          }))
          .checkImmediate(_.size == 2, template, xs => wrongNumberOfTypeArguments("Map", 2, xs.size))
          .map(_.unzip)
        (stps, evps) <- ExprPairSeqE.elaborate(elems).map(_.unzip)
        (sks, sts) = stps.unzip
        (std, ed) <- ExprE.elaborate(default)
          .addConstraints(sks.map(Constraint.equal(_, stf)))
          .addConstraints(sts.map(Constraint.equal(_, stt)))
        _ <- Constrained(Constraint.equal(std, stt))
      } yield (SimpleTypes.MapType(stf, stt).setPos(template.pos), Eventual.withUnifier { implicit unifier =>
        trees.FiniteMap(evps.map(_.get), ed.get, etf.get, ett.get)
      })
      case Abstraction(quantifier, bindings, body) => for {
        bs <- BindingSeqE.elaborate(bindings)
        (stb, evb) <- ExprE.elaborate(body)(store.addBindings(bs))
      } yield quantifier match {
        case Lambda =>
          (SimpleTypes.FunctionType(bs.map(_.tpe), stb).setPos(template.pos), Eventual.withUnifier { implicit unifier =>
            trees.Lambda(bs.map(_.evValDef.get), evb.get)
          })
        case Forall =>
          (SimpleTypes.BooleanType().setPos(template.pos), Eventual.withUnifier { implicit unifier =>
            trees.Forall(bs.map(_.evValDef.get), evb.get)
          })
      }
      case Application(callee, args) => {
        val u = SimpleTypes.Unknown.fresh.setPos(template.pos)
        for {
          (stc, evc) <- ExprE.elaborate(callee)
          (sts, evs) <- ExprSeqE.elaborate(args).map(_.unzip)
          _ <- Constrained(Constraint.equal(SimpleTypes.FunctionType(sts, u).setPos(template.pos), stc))
        } yield (u, Eventual.withUnifier { implicit unifier =>
          trees.Application(evc.get, evs.map(_.get))
        })
      }
      case Assume(condition, body) => for {
        (stc, evc) <- ExprE.elaborate(condition)
        (stb, evb) <- ExprE.elaborate(body).addConstraint(Constraint.equal(stc, SimpleTypes.BooleanType().setPos(template.pos)))
      } yield (stb, Eventual.withUnifier { implicit unifier =>
        trees.Assume(evc.get, evb.get)
      })
      case Cast(Casts.Widen, expr, size) => for {
        (st, ev) <- ExprE.elaborate(expr)
        _ <- Constrained(Constraint.isBits(st, upper=Some(size - 1)))
      } yield (SimpleTypes.BitVectorType(true, size).setPos(template.pos), ev.map(trees.BVWideningCast(_, trees.BVType(true, size))))
      case Cast(Casts.Narrow, expr, size) => for {
        (st, ev) <- ExprE.elaborate(expr)
        _ <- Constrained(Constraint.isBits(st, lower=Some(size + 1)))
      } yield (SimpleTypes.BitVectorType(true, size).setPos(template.pos), ev.map(trees.BVNarrowingCast(_, trees.BVType(true, size))))
      case Choose(binding, body) => for {
        sb <- BindingE.elaborate(binding)
        (st, evb) <- ExprE.elaborate(body)(store.addBinding(sb))
        _ <- Constrained(Constraint.equal(st, SimpleTypes.BooleanType().setPos(template.pos)))
      } yield (sb.tpe.withPos(template.pos), Eventual.withUnifier { implicit unifier =>
        trees.Choose(sb.evValDef.get, evb.get)
      })
      case If(condition, thenn, elze) => for {
        (stc, evc) <- ExprE.elaborate(condition)
        (stt, evt) <- ExprE.elaborate(thenn).addConstraint(Constraint.equal(stc, SimpleTypes.BooleanType().setPos(template.pos)))
        (ste, eve) <- ExprE.elaborate(elze)
        _ <- Constrained(Constraint.equal(stt, ste))
      } yield (stt, Eventual.withUnifier { implicit unifier =>
        trees.IfExpr(evc.get, evt.get, eve.get)
      })

      case Exprs.Invocation(id, optTypeArgs, args) =>
        val identUnknownType = SimpleTypes.Unknown.fresh.setPos(id.pos)
        val resType = SimpleTypes.Unknown.fresh.setPos(template.pos)
        for {
          // get a sequence of identifiers
          identifierSequence: Seq[inox.Identifier] <- ExprUseIDOverloadE.elaborate(id)
          // if there are any type parameters elaborate them
          (sts, ets) <- optTypeArgs.map(TypeSeqE.elaborate(_)).getOrElse(
            Constrained.sequence(Seq.empty[Constrained[(SimpleTypes.Type, Eventual[trees.Type])]])).map(_.unzip)
          // elaborate all of the arguments
          (stas, evas) <- ExprSeqE.elaborate(args).map(_.unzip)
          // get all mappings from type eventual tree which invokes the need function, constructor or callable variable
          mapped: Seq[Constrained[(SimpleTypes.Type, SimpleTypes.Type, Eventual[trees.Expr])]] = identifierSequence.flatMap(ident => {
            store.getFunction(ident).map(x => Left((x, true)))
              .orElse(store.getConstructor(ident).map(x => Left((x, false))))
              .orElse(store.getVariable(ident).map(x => Right(x))).map {
              case Left(((n, f), true)) =>
                if (sts.isEmpty) {
                  val dummyUnknown = Seq.fill(n) {SimpleTypes.Unknown.fresh.setPos(template.pos)}
                  val pair = f(dummyUnknown)
                  if (pair._1.size == stas.size)
                    Some(
                      for {
                        (sts, ets) <- Constrained.sequence(Seq.fill(n) {
                          val unknown = SimpleTypes.Unknown.fresh.setPos(template.pos)
                          Constrained.pure(unknown, Eventual.withUnifier { implicit unifier =>
                            SimpleTypes.toInox(unifier.get(unknown))
                          })
                        }).map(_.unzip)
                        (ests, rst) = f(sts)
                        _ <- Constrained(ests.zip(stas).map { case (est, ast) => Constraint.equal(est, ast) }: _*)
                      } yield (rst, SimpleTypes.FunctionType(ests, rst), Eventual.withUnifier { implicit unifier =>
                        trees.FunctionInvocation(ident, ets.map(_.get), evas.map(_.get))
                      }))
                  else
                    None
                } else if (sts.size == n) {
                  val (ests, rst) = f(sts)
                  Some(Constrained.pure((rst, SimpleTypes.FunctionType(ests, rst), Eventual.withUnifier { implicit unifier =>
                    trees.FunctionInvocation(ident, ets.map(_.get), evas.map(_.get))
                  })).addConstraints(ests.zip(stas).map { case (est, ast) => Constraint.equal(est, ast) }))
                } else
                  None
              case Left(((n, f), false)) =>
                if (sts.isEmpty) {
                  Some(
                    for {
                      (sts, ets) <- Constrained.sequence(Seq.fill(n) {
                        val unknown = SimpleTypes.Unknown.fresh.setPos(template.pos)
                        Constrained.pure(unknown, Eventual.withUnifier { implicit unifier =>
                          SimpleTypes.toInox(unifier.get(unknown))
                        })
                      }).map(_.unzip)
                      (ests, rst) = f(sts)
                      if stas.size == ests.size
                      _ <- Constrained(ests.zip(stas).map { case (est, ast) => Constraint.equal(est, ast) }: _*)
                    } yield (rst, rst, Eventual.withUnifier { implicit unifier =>
                      trees.ADT(ident, ets.map(_.get), evas.map(_.get))
                    }))
                } else if (sts.size == n) {
                  val (ests, rst) = f(sts)
                  Some(Constrained.pure((rst, rst, Eventual.withUnifier { implicit unifier =>
                    trees.ADT(ident, ets.map(_.get), evas.map(_.get))
                  })).addConstraints(ests.zip(stas).map { case (est, ast) => Constraint.equal(est, ast) }))
                } else
                  None
              case Right((st, et)) => {
                val retTpe = SimpleTypes.Unknown.fresh.setPos(template.pos)
                Some(for {
                  _ <- Constrained(Constraint.equal(st, SimpleTypes.FunctionType(stas, retTpe)))
                    .checkImmediate(optTypeArgs.isEmpty, template, functionValuesCanNotHaveTypeParameters(ident.name))
                } yield (retTpe, SimpleTypes.FunctionType(stas, retTpe), Eventual.withUnifier { implicit unifier =>
                  trees.Application(trees.Variable(ident, et.get, Seq()), evas.map(_.get))
                }))
              }
            }
          }).flatten
          options <- Constrained.sequence(mapped)
          resOptions = options.map(_._1)
          idOptions = options.map(_._2)
          _ <- Constrained(Constraint.oneOf(resType, resOptions), Constraint.oneOf(identUnknownType, idOptions))
        } yield (resType, Eventual.withUnifier { implicit unifier =>
          val unifiedFinal = unifier.get(resType)
          val unfierIdType = unifier.get(identUnknownType)
          val eventualOption = options.find(option => unifier(option._1) == unifiedFinal && unifier(option._2) == unfierIdType)
          eventualOption match {
            case None => throw new Exception("Should not happen that unification finished")
            case Some(eventual) => eventual._3.get
          }
        })
//      case Invocation(id, optTypeArgs, args) => {
//
//        ExprUseIdE.elaborate(id).flatMap { i =>
//          Constrained.attempt(
//            store.getFunction(i).map(x => Left((x, true)))
//              .orElse(store.getConstructor(i).map(x => Left((x, false))))
//              .orElse(store.getVariable(i).map(x => Right(x))),
//            template,
//            identifierNotCallable(i.name)
//          ).flatMap {
//
//            case Left(((n, f), isFun)) => for {
//              (sts, ets) <- optTypeArgs
//                .map(TypeSeqE.elaborate(_))
//                .getOrElse(Constrained.sequence(Seq.fill(n) {
//                  OptTypeE.elaborate(Left(template.pos))
//                }))
//                .checkImmediate(_.size == n, template, xs => wrongNumberOfTypeArguments(i.name, n, xs.size))
//                .map(_.unzip)
//              (ests, rst) = f(sts)
//              (stas, evas) <- ExprSeqE.elaborate(args)
//                .checkImmediate(_.size == ests.size, template, xs => wrongNumberOfArguments(i.name, ests.size, xs.size))
//                .map(_.unzip)
//              _ <- Constrained(ests.zip(stas).map { case (est, ast) => Constraint.equal(est, ast) } : _*)
//            } yield (rst, Eventual.withUnifier { implicit unifier =>
//              if (isFun) {
//                trees.FunctionInvocation(i, ets.map(_.get), evas.map(_.get))
//              }
//              else {
//                trees.ADT(i, ets.map(_.get), evas.map(_.get))
//              }
//            })
//            case Right((st, et)) => {
//              val retTpe = SimpleTypes.Unknown.fresh.setPos(template.pos)
//              for {
//                (stas, evas) <- ExprSeqE.elaborate(args)
//                  .checkImmediate(optTypeArgs.isEmpty, template, functionValuesCanNotHaveTypeParameters(i.name))
//                  .map(_.unzip)
//                _ <- Constrained(Constraint.equal(st, SimpleTypes.FunctionType(stas, retTpe)))
//              } yield (retTpe, Eventual.withUnifier { implicit unifier =>
//                trees.Application(trees.Variable(i, et.get, Seq()), evas.map(_.get))
//              })
//            }
//          }
//        }
//      }
      case PrimitiveInvocation(fun, optTypeArgs, args) => {
        import Primitive._

        optTypeArgs
          .map(TypeSeqE.elaborate(_))
          .getOrElse(Constrained.sequence(Seq.fill(fun.typeArgs) {
            OptTypeE.elaborate(Left(template.pos))
          }))
          .checkImmediate(_.size == fun.typeArgs, template, xs => wrongNumberOfTypeArguments(fun.name, fun.typeArgs, xs.size))
          .map(_.map(_._1))
          .flatMap { (typeArgs) =>

          ExprSeqE
            .elaborate(args)
            .checkImmediate(_.size == fun.args, template, xs => wrongNumberOfArguments(fun.name, fun.args, xs.size))
            .map(_.unzip)
            .flatMap { case (sts, evs) => fun match {
              case SetAdd =>
                Constrained
                  .pure((SimpleTypes.SetType(typeArgs(0)).setPos(template.pos), Eventual.withUnifier { implicit unifier =>
                    trees.SetAdd(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.SetType(typeArgs(0)).setPos(template.pos)))
                  .addConstraint(Constraint.equal(sts(1), typeArgs(0)))
              case ElementOfSet =>
                Constrained
                  .pure((SimpleTypes.BooleanType().setPos(template.pos), Eventual.withUnifier { implicit unifier =>
                    trees.ElementOfSet(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), typeArgs(0)))
                  .addConstraint(Constraint.equal(sts(1), SimpleTypes.SetType(typeArgs(0)).setPos(template.pos)))
              case SetIntersection =>
                Constrained
                  .pure((SimpleTypes.SetType(typeArgs(0)).setPos(template.pos), Eventual.withUnifier { implicit unifier =>
                    trees.SetIntersection(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.SetType(typeArgs(0)).setPos(template.pos)))
                  .addConstraint(Constraint.equal(sts(1), SimpleTypes.SetType(typeArgs(0)).setPos(template.pos)))
              case SetUnion =>
                Constrained
                  .pure((SimpleTypes.SetType(typeArgs(0)).setPos(template.pos), Eventual.withUnifier { implicit unifier =>
                    trees.SetUnion(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.SetType(typeArgs(0)).setPos(template.pos)))
                  .addConstraint(Constraint.equal(sts(1), SimpleTypes.SetType(typeArgs(0)).setPos(template.pos)))
              case SetDifference =>
                Constrained
                  .pure((SimpleTypes.SetType(typeArgs(0)).setPos(template.pos), Eventual.withUnifier { implicit unifier =>
                    trees.SetUnion(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.SetType(typeArgs(0)).setPos(template.pos)))
                  .addConstraint(Constraint.equal(sts(1), SimpleTypes.SetType(typeArgs(0)).setPos(template.pos)))
              case Subset =>
                Constrained
                  .pure((SimpleTypes.BooleanType().setPos(template.pos), Eventual.withUnifier { implicit unifier =>
                    trees.SubsetOf(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.SetType(typeArgs(0)).setPos(template.pos)))
                  .addConstraint(Constraint.equal(sts(1), SimpleTypes.SetType(typeArgs(0)).setPos(template.pos)))
              case BagAdd =>
                Constrained
                  .pure((SimpleTypes.BagType(typeArgs(0)).setPos(template.pos), Eventual.withUnifier { implicit unifier =>
                    trees.BagAdd(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.BagType(typeArgs(0)).setPos(template.pos)))
                  .addConstraint(Constraint.equal(sts(1), typeArgs(0)))
              case MultiplicityInBag =>
                Constrained
                  .pure((SimpleTypes.IntegerType().setPos(template.pos), Eventual.withUnifier { implicit unifier =>
                    trees.MultiplicityInBag(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), typeArgs(0)))
                  .addConstraint(Constraint.equal(sts(1), SimpleTypes.BagType(typeArgs(0)).setPos(template.pos)))
              case BagIntersection =>
                Constrained
                  .pure((SimpleTypes.BagType(typeArgs(0)).setPos(template.pos), Eventual.withUnifier { implicit unifier =>
                    trees.BagIntersection(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.BagType(typeArgs(0)).setPos(template.pos)))
                  .addConstraint(Constraint.equal(sts(1), SimpleTypes.BagType(typeArgs(0)).setPos(template.pos)))
              case BagUnion =>
                Constrained
                  .pure((SimpleTypes.BagType(typeArgs(0)).setPos(template.pos), Eventual.withUnifier { implicit unifier =>
                    trees.BagUnion(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.BagType(typeArgs(0)).setPos(template.pos)))
                  .addConstraint(Constraint.equal(sts(1), SimpleTypes.BagType(typeArgs(0)).setPos(template.pos)))
              case BagDifference =>
                Constrained
                  .pure((SimpleTypes.BagType(typeArgs(0)).setPos(template.pos), Eventual.withUnifier { implicit unifier =>
                    trees.BagUnion(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.BagType(typeArgs(0)).setPos(template.pos)))
                  .addConstraint(Constraint.equal(sts(1), SimpleTypes.BagType(typeArgs(0)).setPos(template.pos)))
              case MapApply =>
                Constrained
                  .pure((typeArgs(1), Eventual.withUnifier { implicit unifier =>
                    trees.MapApply(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.MapType(typeArgs(0), typeArgs(1)).setPos(template.pos)))
                  .addConstraint(Constraint.equal(sts(1), typeArgs(0)))
              case MapUpdated =>
                Constrained
                  .pure((SimpleTypes.MapType(typeArgs(0), typeArgs(1)).setPos(template.pos), Eventual.withUnifier { implicit unifier =>
                    trees.MapUpdated(evs(0).get, evs(1).get, evs(2).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.MapType(typeArgs(0), typeArgs(1)).setPos(template.pos)))
                  .addConstraint(Constraint.equal(sts(1), typeArgs(0)))
                  .addConstraint(Constraint.equal(sts(2), typeArgs(1)))
              case StringConcat =>
                Constrained
                  .pure((SimpleTypes.StringType().setPos(template.pos), Eventual.withUnifier { implicit unifier =>
                    trees.StringConcat(evs(0).get, evs(1).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.StringType().setPos(template.pos)))
                  .addConstraint(Constraint.equal(sts(1), SimpleTypes.StringType().setPos(template.pos)))
              case SubString =>
                Constrained
                  .pure((SimpleTypes.StringType().setPos(template.pos), Eventual.withUnifier { implicit unifier =>
                    trees.SubString(evs(0).get, evs(1).get, evs(2).get)
                  }))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.StringType().setPos(template.pos)))
                  .addConstraint(Constraint.equal(sts(1), SimpleTypes.IntegerType().setPos(template.pos)))
                  .addConstraint(Constraint.equal(sts(2), SimpleTypes.IntegerType().setPos(template.pos)))
              case StringLength =>
                Constrained
                  .pure((SimpleTypes.IntegerType().setPos(template.pos), evs(0).map(trees.StringLength(_))))
                  .addConstraint(Constraint.equal(sts(0), SimpleTypes.StringType().setPos(template.pos)))
            }
          }
        }
      }
      case IsConstructor(expr, id) => for {
        (st, ev) <- ExprE.elaborate(expr)
        i <- ExprUseIdE.elaborate(id)
        s <- Constrained.attempt(store.getSortOfConstructor(i), template, identifierNotConstructor(i.name))
        n = store.getTypeConstructor(s).getOrElse { throw new IllegalStateException("Inconsistent store.") }
        _ <- Constrained(Constraint.equal(st, SimpleTypes.ADTType(s, Seq.fill(n)(SimpleTypes.Unknown.fresh.setPos(template.pos))).setPos(template.pos)))
      } yield (SimpleTypes.BooleanType().setPos(template.pos), ev.map(trees.IsConstructor(_, i)))
      case Let(binding, value, expr) => for {
        sb <- BindingE.elaborate(binding)
        (stv, ev) <- ExprE.elaborate(value)
        (ste, ee) <- ExprE.elaborate(expr)(store.addBinding(sb))
          .addConstraint(Constraint.equal(sb.tpe, stv))
      } yield (ste, Eventual.withUnifier { implicit unifier =>
        trees.Let(sb.evValDef.get, ev.get, ee.get)
      })
      case Tuple(exprs) => for {
        (sts, evs) <- ExprSeqE.elaborate(exprs).map(_.unzip)
      } yield (SimpleTypes.TupleType(sts).setPos(template.pos), Eventual.withUnifier { implicit unifier =>
        trees.Tuple(evs.map(_.get))
      })
      case TupleSelection(expr, index) => for {
        (st, ev) <- ExprE.elaborate(expr)
        u = SimpleTypes.Unknown.fresh.setPos(template.pos)
        _ <- Constrained(Constraint.atIndexIs(st, index, u))
      } yield (u, ev.map(trees.TupleSelect(_, index)))
      case Selection(expr, id) => for {
        (st, ev) <- ExprE.elaborate(expr)
        (name, pis) <- FieldIdE.elaborate(id)
        _ <- Constrained.checkImmediate(pis.size > 0, id, noFieldNamed(name))
        adtType = SimpleTypes.Unknown.fresh.setPos(template.pos)
        retType = SimpleTypes.Unknown.fresh.setPos(template.pos)
        _ <- Constrained(Constraint.hasFields(st, pis.map(_._2.name).toSet, pis.map {
          case (sortId, fieldId) => (sortId, (tpe: SimpleTypes.Type) => {
            val n = store.getTypeConstructor(sortId).getOrElse {
              throw new IllegalStateException("Inconsistent store.")
            }
            val as = Seq.fill(n)(SimpleTypes.Unknown.fresh.setPos(template.pos))
            val r = store.getTypeOfField(fieldId)(as)
            Seq(
              Constraint.equal(adtType, tpe),
              Constraint.equal(r, retType),
              Constraint.equal(tpe, SimpleTypes.ADTType(sortId, as).setPos(template.pos)))
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
              .addConstraint(Constraint.equal(st, SimpleTypes.BooleanType().setPos(template.pos)))
          case BVNot =>
            Constrained
              .pure((st, ev.map(trees.BVNot(_))))
              .addConstraint(Constraint.isBits(st))
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
                .pure((SimpleTypes.BooleanType().setPos(template.pos), Eventual.withUnifier { implicit unifier => trees.Implies(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, SimpleTypes.BooleanType().setPos(template.pos)))
                .addConstraint(Constraint.equal(st2, SimpleTypes.BooleanType().setPos(template.pos)))
            case Equals =>
              Constrained
                .pure((SimpleTypes.BooleanType().setPos(template.pos), Eventual.withUnifier { implicit unifier => trees.Equals(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, st2))
            case LessEquals =>
              Constrained
                .pure((SimpleTypes.BooleanType().setPos(template.pos), Eventual.withUnifier { implicit unifier => trees.LessEquals(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, st2))
                .addConstraint(Constraint.isComparable(st1))
            case LessThan =>
              Constrained
                .pure((SimpleTypes.BooleanType().setPos(template.pos), Eventual.withUnifier { implicit unifier => trees.LessThan(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, st2))
                .addConstraint(Constraint.isComparable(st1))
            case GreaterEquals =>
              Constrained
                .pure((SimpleTypes.BooleanType().setPos(template.pos), Eventual.withUnifier { implicit unifier => trees.GreaterEquals(ev1.get, ev2.get) }))
                .addConstraint(Constraint.equal(st1, st2))
                .addConstraint(Constraint.isComparable(st1))
            case GreaterThan =>
              Constrained
                .pure((SimpleTypes.BooleanType().setPos(template.pos), Eventual.withUnifier { implicit unifier => trees.GreaterThan(ev1.get, ev2.get) }))
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
          }
        }
      }
      case NaryOperation(op, args) => ExprSeqE.elaborate(args).map(_.unzip).flatMap { case (sts, evs) =>
        import NAry._

        op match {
          case And =>
            Constrained
              .pure((SimpleTypes.BooleanType().setPos(template.pos), Eventual.sequence(evs).map(trees.And(_))))
              .addConstraints(sts.map(Constraint.equal(_, SimpleTypes.BooleanType().setPos(template.pos))))
          case Or =>
            Constrained
              .pure((SimpleTypes.BooleanType().setPos(template.pos), Eventual.sequence(evs).map(trees.Or(_))))
              .addConstraints(sts.map(Constraint.equal(_, SimpleTypes.BooleanType().setPos(template.pos))))
        }
      }
    }
  }
  val ExprE = new ExprE

  class ExprSeqE extends HSeqE[Expr, trees.Expr, (SimpleTypes.Type, Eventual[trees.Expr])]("Expr") {
    override val elaborator = ExprE
    override def wrap(expr: trees.Expr, where: IR)(implicit store: Store): Constrained[(SimpleTypes.Type, Eventual[trees.Expr])] =
      Constrained.attempt(SimpleTypes.fromInox(expr.getType(store.getSymbols)).map { st =>
        (st.setPos(where.pos), Eventual.pure(expr))
      }, where, invalidInoxExpr(expr))
  }
  val ExprSeqE = new ExprSeqE

  class ExprPairE extends Elaborator[ExprPair, ((SimpleTypes.Type, SimpleTypes.Type), Eventual[(trees.Expr, trees.Expr)])] {
    override def elaborate(pair: ExprPair)(implicit store: Store):
        Constrained[((SimpleTypes.Type, SimpleTypes.Type), Eventual[(trees.Expr, trees.Expr)])] = pair match {
      case PairHole(index) => Constrained.attempt(store.getHole[(trees.Expr, trees.Expr)](index), pair, invalidHoleType("(Expr, Expr)")).flatMap {
        case p@(lhs, rhs) => for {
          stl <- Constrained.attempt(SimpleTypes.fromInox(lhs.getType(store.getSymbols)).map(_.setPos(pair.pos)), pair, invalidInoxExpr(lhs))
          str <- Constrained.attempt(SimpleTypes.fromInox(rhs.getType(store.getSymbols)).map(_.setPos(pair.pos)), pair, invalidInoxExpr(rhs))
        } yield ((stl, str), Eventual.pure(p))
      }
      case Pair(lhs, rhs) => for {
        (stl, evl) <- ExprE.elaborate(lhs)
        (str, evr) <- ExprE.elaborate(rhs)
      } yield ((stl, str), Eventual.withUnifier { implicit unifier => (evl.get, evr.get) })
    }
  }
  val ExprPairE = new ExprPairE

  class ExprPairSeqE extends HSeqE[ExprPair, (trees.Expr, trees.Expr), ((SimpleTypes.Type, SimpleTypes.Type), Eventual[(trees.Expr, trees.Expr)])]("(Expr, Expr)") {
    override val elaborator = ExprPairE
    override def wrap(pair: (trees.Expr, trees.Expr), where: IR)(implicit store: Store):
        Constrained[((SimpleTypes.Type, SimpleTypes.Type), Eventual[(trees.Expr, trees.Expr)])] = for {
      stl <- Constrained.attempt(SimpleTypes.fromInox(pair._1.getType(store.getSymbols)).map(_.setPos(where.pos)), where, invalidInoxExpr(pair._1))
      str <- Constrained.attempt(SimpleTypes.fromInox(pair._2.getType(store.getSymbols)).map(_.setPos(where.pos)), where, invalidInoxExpr(pair._2))
    } yield ((stl, str), Eventual.pure(pair))
  }
  val ExprPairSeqE = new ExprPairSeqE
}