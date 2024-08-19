/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package parsing

import scala.util.parsing.input._

import Utils.plural

trait ExpressionElaborators { self: Elaborators =>
  import trees._

  trait ExpressionElaborator { self0: Elaborator =>
    import symbols.given
    import ExprIR._

    //---- Errors ----//

    def functionArity(name: String, expected: Int, actual: Int, kind: String = "Function"): String =
      kind + " `" + name + "` takes " + expected + " argument" + plural(expected, "", "s") + ", " +
        actual + " " + plural(actual, "was", "were") + " given."

    def functionTypeArity(name: String, expected: Int, actual: Int, kind: String = "Function"): String =
      if (expected == 0) {
        kind + " `" + name + "` doesn't have any type parameters."
      } else {
        kind + " `" + name + "` takes " + expected + " type argument" + plural(expected, "", "s") + ", " +
          actual + " " + plural(actual, "was", "were") + " given."
      }

    lazy val expectedArrowBinding: String = "Expected binding of the form `key -> value`."

    lazy val unexpectedBinding: String = "Unexpected binding. Bindings can only appear in bags and maps constructors."

    lazy val unknownConstruct: String = "Unexpected construct."

    lazy val tupleInsufficientLength: String = "Tuples should be of length greater or equal to 2."

    lazy val warningSetOrBag: String = "Not all elements are of the same shape. " +
      "Use bindings of the form `key -> value` for bag literals and naked values for set literals."

    lazy val wrongNumberOfArguments: String = "Wrong number of arguments."

    object LocalFunction {
      def unapply(expression: Expression)(using store: Store): Option[(trees.FunDef, Option[Seq[Type]])] = expression match {
        case TypeApplication(Variable(id), targs) if store `isFunction` id.getName => Some((store `getFunction` id.getName, Some(targs)))
        case Variable(id) if store `isFunction` id.getName => Some((store `getFunction` id.getName, None))
        case _ => None
      }
    }

    object LocalConstructor {
      def unapply(expression: Expression)(using store: Store): Option[(trees.ADTSort, trees.ADTConstructor, Option[Seq[Type]])] = expression match {
        case TypeApplication(Variable(id), targs) if store `isConstructor` id.getName =>
          val (sort, cons) = store `getConstructor` id.getName
          Some((sort, cons, Some(targs)))
        case Variable(id) if store `isConstructor` id.getName =>
          val (sort, cons) = store `getConstructor` id.getName
          Some((sort, cons, None))
        case _ => None
      }
    }

    object TypedDefinition {
      def unapply(expression: Expression)(using store: Store): Option[(
        inox.Identifier,
        Seq[trees.TypeParameter],
        Seq[trees.ValDef],
        trees.Type,
        Boolean,
        Option[Seq[Type]]
      )] = expression match {
        case LocalFunction(fd, otpe) =>
          Some((fd.id, fd.typeArgs, fd.params, fd.getType, true, otpe))
        case LocalConstructor(sort, cons, otpe) =>
          Some((cons.id, sort.typeArgs, cons.fields, trees.ADTType(sort.id, sort.typeArgs), false, otpe))
        case TypedFunDef(fd, otps) =>
          Some((fd.id, fd.typeArgs, fd.params, fd.getType, true, otps))
        case TypedConsDef(cons, otps) =>
          val sort = cons.getSort
          Some((cons.id, sort.typeArgs, cons.fields, trees.ADTType(sort.id, sort.typeArgs), false, otps))
        case _ => None
      }
    }

    object IsConstructor {
      def unapply(expr: Expression)(using store: Store): Option[(Expression, trees.ADTSort, trees.ADTConstructor)] = expr match {
        case IsConstructorOperation(expr, cons) => Some((expr, cons.getSort, cons))
        case Operation("is", Seq(lhs, LocalConstructor(sort, cons, None))) => Some((lhs, sort, cons))
        case _ => None
      }
    }

    object Fields {
      def unapply(field: Field)(using store: Store): Option[Seq[(trees.ADTSort, trees.ValDef)]] =
        Field.unapplySeq(field)
          .filter(_.nonEmpty)
          .map(_.map { case (cons, vd) => (cons.getSort, vd) })
          .orElse(field match {
            case FieldName(name) if store `isField` name =>
              Some((store `getFields` name).map { case (sort, cons, vd) => (sort, vd) })

            case FieldIdentifier(id) =>
              val matchingCons = (store `getFields` id.name).filter {
                case (sort, cons, vd) => cons.fields.exists(_.id == id)
              }

              if (matchingCons.nonEmpty) {
                Some(matchingCons.map { case (sort, cons, vd) => (sort, vd) })
              } else {
                None
              }

            case _ => None
          })
    }

    def getExprBindings(es: Seq[(ExprIR.Identifier, Option[TypeIR.Expression])])
                               (using store0: Store, pos: Position): (Store, Seq[trees.Type], Constrained[Seq[trees.ValDef]]) = {
      val (newStore, tps, vds) = es.foldLeft((store0, Seq[trees.Type](), Seq[Constrained[trees.ValDef]]())) {
        case ((store, tps, vds), (ident, otpe)) =>
          val id = getIdentifier(ident)

          val (tpe, ctpe) = otpe match {
            case None =>
              val tpe = Unknown.fresh
              (tpe, Constrained.unify(u ?=> u(tpe)))
            case Some(tpe) =>
              (getSimpleType(tpe)(using store), getType(tpe, bound = Some(ident.getName))(using store))
          }

          ctpe match {
            case unsat: Unsatisfiable => (store, tps :+ tpe, vds :+ unsat)
            case c @ WithConstraints(ev, cs) =>
              val newStore = store + (ident.getName, id, tpe, ev)
              val newVds = vds :+ c.transform(tp => trees.ValDef(id, tp))
              (newStore, tps :+ tpe, newVds)
          }
      }

      (newStore, tps, Constrained.sequence(vds))
    }

    /** Type inference and expression elaboration.
     *
     * @param expr     The expression to typecheck.
     * @param expected The type the expression is expected to have.
     * @param store    Mappings of variables.
     * @return A sequence of constraints and a way to build an Inox expression given a solution to the constraints.
     */
    def getExpr(expr: Expression, expected: Unknown)(using store: Store): Constrained[trees.Expr] = {
      given position: Position = expr.pos

      expr match {

        //---- Literals ----//

        // Boolean literals.
        case Literal(BooleanLiteral(value)) => Constrained.pure({
          trees.BooleanLiteral(value)
        }).addConstraint({
          Constraint.equal(expected, trees.BooleanType())
        })

        // Unit literal.
        case Literal(UnitLiteral) => Constrained.pure({
          trees.UnitLiteral()
        }).addConstraint({
          Constraint.equal(expected, trees.UnitType())
        })

        // String literal.
        case Literal(StringLiteral(string)) => Constrained.pure({
          trees.StringLiteral(string)
        }).addConstraint({
          Constraint.equal(expected, trees.StringType())
        })

        // Char literal.
        case Literal(CharLiteral(character)) => Constrained.pure({
          trees.CharLiteral(character)
        }).addConstraint({
          Constraint.equal(expected, trees.CharType())
        })

        // Numeric literal.
        case Literal(NumericLiteral(string)) => Constrained.unify({ unifier ?=>
          unifier(expected) match {
            case trees.IntegerType() => trees.IntegerLiteral(BigInt(string))
            case trees.BVType(signed, n) => trees.BVLiteral(signed, BigInt(string), n)
            case trees.RealType() => trees.FractionLiteral(BigInt(string), 1)
            case tpe => throw new Exception("getExpr: Unexpected type during elaboration: " + tpe)
          }
        }).addConstraint({
          Constraint.isNumeric(expected)
        })

        // Decimal literal.
        case Literal(DecimalLiteral(whole, trailing, repeating)) => Constrained.pure({
          val (n, d) = Utils.toFraction(whole, trailing, repeating)
          trees.FractionLiteral(n, d)
        }).addConstraint({
          Constraint.equal(expected, trees.RealType())
        })

        // Empty set literal.
        // TODO: Also accept it as a Bag literal.
        case Operation("Set", Seq()) => {
          val elementType = Unknown.fresh
          Constrained.unify({ u ?=>
            trees.FiniteSet(Seq(), u(elementType))
          }).addConstraint({
            Constraint.equal(expected, trees.SetType(elementType))
          })
        }

        //---- Variables ----//

        // Variable.
        case Variable(variable) => Constrained.unify({
          val (i, _, tpe) = store `getVariable` variable.getName
          trees.Variable(i, tpe, Seq.empty)
        }).checkImmediate(
          store `isVariable` variable.getName, "Unknown variable " + variable.getName + ".", expr.pos
        ).addConstraint({
          Constraint.equal((store `getVariable` variable.getName)._2, expected)
        })

        //---- Embedded values ----//

        // Embedded expressions.
        case Literal(EmbeddedExpr(e)) => Constrained.pure({
          e
        }).addConstraint({
          Constraint.equal(e.getType(using symbols), expected)
        }).checkImmediate(
          e.getType(using symbols) != trees.Untyped, "Untyped embedded expression.", expr.pos
        )

        // Embedded Scala values.
        case Literal(EmbeddedValue(value)) => value match {
          case b : Boolean =>
            Constrained.pure({
              trees.BooleanLiteral(b)
            }).addConstraint({
              Constraint.equal(expected, trees.BooleanType())
            })
          case n : Int =>
            Constrained.pure({
              trees.Int32Literal(n)
            }).addConstraint({
              Constraint.equal(expected, trees.Int32Type())
            })
          case n : BigInt =>
            Constrained.pure({
              trees.IntegerLiteral(n)
            }).addConstraint({
              Constraint.equal(expected, trees.IntegerType())
            })
          case c : Char =>
            Constrained.pure({
              trees.CharLiteral(c)
            }).addConstraint({
              Constraint.equal(expected, trees.CharType())
            })
          case s : String =>
            Constrained.pure({
              trees.StringLiteral(s)
            }).addConstraint({
              Constraint.equal(expected, trees.StringType())
            })
          case _ : Unit =>
            Constrained.pure({
              trees.UnitLiteral()
            }).addConstraint({
              Constraint.equal(expected, trees.UnitType())
            })
          case _ => Constrained.fail("Unsupported embedded value: " + value + ".", expr.pos)
        }

        //---- Operators ----//

        // Unary minus.
        case Operation("-", Seq(arg)) => {
          getExpr(arg, expected).transform(trees.UMinus(_)).addConstraint({
            Constraint.isNumeric(expected)
          })
        }

        // Unary plus.
        case Operation("+", Seq(arg)) => {
          getExpr(arg, expected).addConstraint({
            Constraint.isNumeric(expected)
          })
        }

        // Binary operation defined on numeric types.
        case Operation(NumericBinOp(op), args) => {

          Constrained.sequence({
            args.map(getExpr(_, expected))
          }).transform({
            case Seq(a, b) => op(a, b)
          }).checkImmediate(
            args.length == 2, wrongNumberOfArguments, expr.pos
          ).addConstraint({
            Constraint.isNumeric(expected)
          })
        }

        // Binary operation defined on integral types.
        case Operation(IntegralBinOp(op), args) => {

          Constrained.sequence({
            args.map(getExpr(_, expected))
          }).transform({
            case Seq(a, b) => op(a, b)
          }).checkImmediate(
            args.length == 2, wrongNumberOfArguments, expr.pos
          ).addConstraint({
            Constraint.isIntegral(expected)
          })
        }

        // Unary negation.
        case Operation("!", Seq(arg)) => {
          getExpr(arg, expected).transform(trees.Not(_)).addConstraint({
            Constraint.equal(expected, trees.BooleanType())
          })
        }

        // Bitwise negation.
        case Operation("~", Seq(arg)) => {
          getExpr(arg, expected).transform(trees.BVNot(_)).addConstraint({
            Constraint.isBitVector(expected)
          })
        }

        // Binary operation defined on comparable types.
        case Operation(ComparableBinOp(op), args) => {

          val expectedArg = Unknown.fresh

          Constrained.sequence({
            args.map(getExpr(_, expectedArg))
          }).transform({
            case Seq(a, b) => op(a, b)
          }).checkImmediate(
            args.length == 2, wrongNumberOfArguments, expr.pos
          ).addConstraint({
            Constraint.isComparable(expectedArg)
          }).addConstraint({
            Constraint.equal(expected, trees.BooleanType())
          })
        }

        // Binary operation defined on bit vectors.
        case Operation(BitVectorBinOp(op), args) => {
          Constrained.sequence({
            args.map(getExpr(_, expected))
          }).transform({
            case Seq(a, b) => op(a, b)
          }).checkImmediate(
            args.length == 2, wrongNumberOfArguments, expr.pos
          ).addConstraint({
            Constraint.isBitVector(expected)
          })
        }

        // Equality.
        case Operation("==", args) => {

          val expectedArg = Unknown.fresh

          Constrained.sequence({
            args.map(getExpr(_, expectedArg))
          }).transform({
            case Seq(a, b) => trees.Equals(a, b)
          }).checkImmediate(
            args.length == 2, wrongNumberOfArguments, expr.pos
          ).addConstraint({
            Constraint.equal(expected, trees.BooleanType())
          })
        }

        // Inequality.
        case Operation("!=", args) => {

          val expectedArg = Unknown.fresh

          Constrained.sequence({
            args.map(getExpr(_, expectedArg))
          }).transform({
            case Seq(a, b) => trees.Not(trees.Equals(a, b))
          }).checkImmediate(
            args.length == 2, wrongNumberOfArguments, expr.pos
          ).addConstraint({
            Constraint.equal(expected, trees.BooleanType())
          })
        }

        // Binary operations defined on booleans.
        case Operation(BooleanBinOp(op), args) => {

          Constrained.sequence({
            args.map(getExpr(_, expected))
          }).transform({
            case Seq(a, b) => op(a, b)
          }).checkImmediate(
            args.length == 2, wrongNumberOfArguments, expr.pos
          ).addConstraint({
            Constraint.equal(expected, trees.BooleanType())
          })
        }

        // NAry operations defined on booleans.
        case BooleanNAryOperation(op, args) => {

          Constrained.sequence({
            args.map(getExpr(_, expected))
          }).transform(
            op(_)
          ).checkImmediate(
            args.length >= 2, wrongNumberOfArguments, expr.pos
          ).addConstraint({
            Constraint.equal(expected, trees.BooleanType())
          })
        }

        //---- Arity Errors on Primitive Functions and Constructors ----//

        case PrimitiveFunction(builtIn, name, args, otpes) if
            ((builtIn.params.isDefined && args.length != builtIn.params.get) || (otpes.isDefined && otpes.get.length != builtIn.tparams)) => {

          val kind = if (builtIn.isConstructor) "Primitive constructor" else "Primitive function"

          val argsError = if (builtIn.params.isDefined && args.length != builtIn.params.get) Seq {
            functionArity(name, builtIn.params.get, args.length, kind)
          } else Seq()

          val typesError = if (otpes.isDefined && otpes.get.length != builtIn.tparams) Seq {
            functionTypeArity(name, builtIn.tparams, otpes.get.length, kind)
          } else Seq()

          Constrained.fail((argsError ++ typesError).map({ case error => (error, expr.pos) }))
        }

        //---- Syntax Error on Set or Bags Literals ----//

        case Operation("Set", Bindings(es, bs)) if (!es.isEmpty && !bs.isEmpty) => {
          Constrained.fail(warningSetOrBag, expr.pos)
        }

        //---- Operations on Strings ----//

        // String concatenation.
        case ConcatenateOperation(str1, str2) => {
          (for {
            s1 <- getExpr(str1, expected)
            s2 <- getExpr(str2, expected)
          } yield {
            trees.StringConcat(s1, s2)
          }).addConstraint({
            Constraint.equal(expected, trees.StringType())
          })
        }

        // Substring.
        case SubstringOperation(str, start, end) => {
          val indexExpected = Unknown.fresh

          (for {
            s <- getExpr(str, expected)
            a <- getExpr(start, indexExpected)
            b <- getExpr(end, indexExpected)
          } yield {
            trees.SubString(s, a, b)
          }).addConstraint({
            Constraint.equal(expected, trees.StringType())
          }).addConstraint({
            Constraint.equal(indexExpected, trees.IntegerType())
          })
        }

        // String length.
        case StringLengthOperation(s) => {
          val stringExpected = Unknown.fresh
          getExpr(s, stringExpected).transform({
            trees.StringLength(_)
          }).addConstraint({
            Constraint.equal(stringExpected, trees.StringType())
          }).addConstraint({
            Constraint.equal(expected, trees.IntegerType())
          })
        }

        //---- Operations on Bags ----//

        case BagConstruction(Bindings(fs, _), _) if (!fs.isEmpty) => {
          Constrained.fail(fs.map {
            (e: Expression) => (expectedArrowBinding, e.pos)
          })
        }

        case BagConstruction(Bindings(_, bs), otpe) => {
          val (et, elementType) = otpe match {
            case None =>
              val et = Unknown.fresh
              (et, Constrained.unify(u ?=> u(et)))
            case Some(tpe) =>
              (getSimpleType(tpe), getType(tpe))
          }

          val freshs = Seq.fill(bs.length)(Unknown.fresh)
          val countType = Unknown.fresh

          val bindingsExpr = Constrained.sequence({
            bs.zip(freshs).map({ case ((k, v), t) =>
              (for {
                key <- getExpr(k, t)
                value <- getExpr(v, countType)
              } yield {
                (key, value): (Expr, Expr)
              }).addConstraint({
                Constraint.equal(t, et)
              })
            })
          })

          (for {
            bindings <- bindingsExpr
            base <- elementType
          } yield {
            trees.FiniteBag(bindings, base)
          }).addConstraint({
            Constraint.equal(countType, trees.IntegerType())
          }).addConstraint({
            Constraint.equal(expected, trees.BagType(et))
          })
        }

        // Bag multiplicity.
        case BagMultiplicityOperation(map, key, otpe) => {
          val elementType = otpe.map(getSimpleType).getOrElse(Unknown.fresh)
          val keyExpected = Unknown.fresh
          val mapExpected = Unknown.fresh

          (for {
            m <- getExpr(map, mapExpected)
            k <- getExpr(key, keyExpected)
          } yield {
            trees.MultiplicityInBag(k, m)
          }).addConstraint({
            Constraint.equal(expected, trees.IntegerType())
          }).addConstraint({
            Constraint.equal(keyExpected, elementType)
          }).addConstraint({
            Constraint.equal(mapExpected, trees.BagType(elementType))
          })
        }

        // Bag binary operation.
        case BagBinaryOperation(map1, map2, op, otpe) => {
          val elementType = otpe.map(getSimpleType).getOrElse(Unknown.fresh)
          val mapExpected = Unknown.fresh

          (for {
            m1 <- getExpr(map1, mapExpected)
            m2 <- getExpr(map2, mapExpected)
          } yield {
            op(m1, m2)
          }).addConstraint({
            Constraint.equal(mapExpected, trees.BagType(elementType))
          })
        }

        // Bag add operation.
        case BagAddOperation(bag, elem, otpe) => {
          val elementExpected = Unknown.fresh
          val elementType = otpe.map(getSimpleType).getOrElse(Unknown.fresh)

          (for {
            b <- getExpr(bag, expected)
            e <- getExpr(elem, elementExpected)
          } yield {
            trees.BagAdd(b, e)
          }).addConstraint({
            Constraint.equal(expected, trees.BagType(elementType))
          }).addConstraint({
            Constraint.equal(elementExpected, elementType)
          })
        }

        //---- Operations on Maps ----//

        case MapConstruction(_, Bindings(fs, _), _) if (!fs.isEmpty) => {
          Constrained.fail(fs.map {
            (e: Expression) => (expectedArrowBinding, e.pos)
          })
        }

        case MapConstruction(dflt, Bindings(_, bs), optEitherKeyAll) => {
          val (kt, keyType, vt, valueType) = optEitherKeyAll match {
            case None =>
              val (kt, vt) = (Unknown.fresh, Unknown.fresh)
              (kt, Constrained.unify(u ?=> u(kt)), vt, Constrained.unify(u ?=> u(vt)))
            case Some(Left(t)) =>
              val vt = Unknown.fresh
              (getSimpleType(t), getType(t), vt, Constrained.unify(u ?=> u(vt)))
            case Some(Right((t1, t2))) =>
              (getSimpleType(t1), getType(t1), getSimpleType(t2), getType(t2))
          }

          val mappingsFresh = Seq.fill(bs.length)((Unknown.fresh, Unknown.fresh))
          val mappingsExpr = Constrained.sequence(bs.zip(mappingsFresh).map({
            case ((k, v), (tk, tv)) =>
              (for {
                key <- getExpr(k, tk)
                value <- getExpr(v, tv)
              } yield {
                (key, value): (Expr, Expr)
              }).addConstraint({
                Constraint.equal(tk, kt)
              }).addConstraint({
                Constraint.equal(tv, vt)
              })
          }))

          val defaultFresh = Unknown.fresh
          val defaultExpr = getExpr(dflt, defaultFresh).addConstraint({
            Constraint.equal(defaultFresh, vt)
          })

          (for {
            mappings <- mappingsExpr
            default <- defaultExpr
            key <- keyType
            value <- valueType
          } yield {
            trees.FiniteMap(mappings, default, key, value)
          }).addConstraint({
            Constraint.equal(expected, trees.MapType(kt, vt))
          })
        }

        // Map apply.
        case MapApplyOperation(map, key, otpes) => {
          val mapExpected = Unknown.fresh
          val keyExpected = Unknown.fresh

          val (keyType, valueType) = otpes.map({
            case (t1, t2) => (getSimpleType(t1), getSimpleType(t2))
          }).getOrElse((Unknown.fresh, Unknown.fresh))

          (for {
            m <- getExpr(map, mapExpected)
            k <- getExpr(key, keyExpected)
          } yield {
            trees.MapApply(m, k)
          }).addConstraint({
            Constraint.equal(keyExpected, keyType)
          }).addConstraint({
            Constraint.equal(expected, valueType)
          }).addConstraint({
            Constraint.equal(mapExpected, trees.MapType(keyType, valueType))
          })
        }

        // Map updated.
        case MapUpdatedOperation(map, key, value, otpes) => {
          val keyExpected = Unknown.fresh
          val valueExpected = Unknown.fresh

          val (keyType, valueType) = otpes.map({
            case (t1, t2) => (getSimpleType(t1), getSimpleType(t2))
          }).getOrElse((Unknown.fresh, Unknown.fresh))

          (for {
            m <- getExpr(map, expected)
            k <- getExpr(key, keyExpected)
            v <- getExpr(value, valueExpected)
          } yield {
            trees.MapUpdated(m, k, v)
          }).addConstraint({
            Constraint.equal(expected, trees.MapType(keyType, valueType))
          }).addConstraint({
            Constraint.equal(keyExpected, keyType)
          }).addConstraint({
            Constraint.equal(valueExpected, valueType)
          })
        }

        //---- Operations on Set ----//

        // Call to the Set constructor.
        case SetConstruction(es, otpe) => {
          val lowers = Seq.fill(es.length) { Unknown.fresh }
          val (upper, elementType) = otpe match {
            case None =>
              val et = Unknown.fresh
              (et, Constrained.unify(u ?=> u(et)))
            case Some(tpe) =>
              (getSimpleType(tpe), getType(tpe))
          }

          val constrainedEs = Constrained.sequence(es.zip(lowers).map {
            case (e, lower) => getExpr(e, lower).addConstraint({
              Constraint.equal(lower, upper)
            })
          })

          (for {
            es <- constrainedEs
            base <- elementType
          } yield {
            trees.FiniteSet(es, base)
          }).addConstraint({
            Constraint.equal(expected, trees.SetType(upper))
          })
        }

        // Call to contains.
        case ContainsOperation(set, elem, otpe) => {
          val setType = Unknown.fresh
          val elementExpected = Unknown.fresh
          val elementType = otpe.map(getSimpleType).getOrElse(Unknown.fresh)

          (for {
            s <- getExpr(set, setType)
            e <- getExpr(elem, elementExpected)
          } yield {
            trees.ElementOfSet(e, s)
          }).addConstraint({
            Constraint.equal(expected, trees.BooleanType())
          }).addConstraint({
            Constraint.equal(setType, trees.SetType(elementType))
          }).addConstraint({
            Constraint.equal(elementExpected, elementType)
          })
        }

        // Call to subset.
        case SubsetOperation(set1, set2, otpe) => {
          val setType = Unknown.fresh
          val elementType = otpe.map(getSimpleType).getOrElse(Unknown.fresh)

          (for {
            s1 <- getExpr(set1, setType)
            s2 <- getExpr(set2, setType)
          } yield {
            trees.SubsetOf(s1, s2)
          }).addConstraint({
            Constraint.equal(expected, trees.BooleanType())
          }).addConstraint({
            Constraint.equal(setType, trees.SetType(elementType))
          })
        }

        // Binary operations on set that return sets.
        case SetBinaryOperation(set1, set2, f, otpe) => {
          val elementType = otpe.map(getSimpleType).getOrElse(Unknown.fresh)

          (for {
            s1 <- getExpr(set1, expected)
            s2 <- getExpr(set2, expected)
          } yield {
            f(s1, s2)
          }).addConstraint({
            Constraint.equal(expected, trees.SetType(elementType))
          })
        }

        // Set add operation.
        case SetAddOperation(set, elem, otpe) => {
          val elementExpected = Unknown.fresh
          val elementType = otpe.map(getSimpleType).getOrElse(Unknown.fresh)

          (for {
            s <- getExpr(set, expected)
            e <- getExpr(elem, elementExpected)
          } yield {
            trees.SetAdd(s, e)
          }).addConstraint({
            Constraint.equal(expected, trees.SetType(elementType))
          }).addConstraint({
            Constraint.equal(elementExpected, elementType)
          })
        }

        //---- Conditionals ----//

        // Conditional expression.
        case Operation("IfThenElse", Seq(cond, thenn, elze)) => {
          val expectedCond = Unknown.fresh

          (for {
            c <- getExpr(cond, expectedCond)
            t <- getExpr(thenn, expected)
            e <- getExpr(elze, expected)
          } yield {
            trees.IfExpr(c, t, e)
          }).addConstraint({
            Constraint.equal(expectedCond, trees.BooleanType())
          })
        }

        // Assumptions
        case Operation("Assume", Seq(pred, rest)) => {
          val booleanExpected = Unknown.fresh
          (for {
            p <- getExpr(pred, booleanExpected)
            r <- getExpr(rest, expected)
          } yield {
            trees.Assume(p, r)
          }).addConstraint({
            Constraint.equal(booleanExpected, trees.BooleanType())
          })
        }

        //---- Functions ----//

        // Function and constructor invocation.
        case Application(TypedDefinition(id, tparams, params, resultType, isFun, optTpeArgs), args) => {

          val freshs = args.map({ a => Unknown.fresh(using a.pos) })
          val tfreshs = tparams.map({ tp => Unknown.fresh })

          val constrainedArgs = Constrained.sequence({
            args.zip(freshs).map({ case (e, t) => getExpr(e, t) })
          })

          val constrainedTpArgs = optTpeArgs match {
            case None =>
              Constrained.sequence(tfreshs.map(tp => Constrained.unify(u ?=> u(tp))))
            case Some(tpeArgs) => {
              Constrained.sequence({
                tpeArgs.map(getType(_))
              }).addConstraints({
                // The annotated types should correspond to the type of the parameters.
                tpeArgs.zip(tfreshs).map({ case (a, b) => Constraint.equal(getSimpleType(a), b) })
              }).checkImmediate(
                // Their should be the same number of type applied than type parameters of the function.
                tpeArgs.length == tparams.length,
                functionTypeArity(id.name, tparams.length, tpeArgs.length),
                expr.pos
              )
            }
          }

          val instantiator = new typeOps.TypeInstantiator((tparams zip tfreshs).toMap)
          val paramTypes = params.map(vd => instantiator.transform(vd.getType))

          (for {
            tpArgs <- constrainedTpArgs
            args <- constrainedArgs
          } yield {
            if (isFun) trees.FunctionInvocation(id, tpArgs, args)
            else trees.ADT(id, tpArgs, args)
          }).checkImmediate(
            // There should be the same number of argument applied than parameters of the function.
            args.length == params.length,
            functionArity(id.name, params.length, args.length),
            expr.pos
          ).addConstraints({
            // The types of arguments should be equal to the type of the parameters.
            freshs.zip(paramTypes).map({ case (a, b) => Constraint.equal(a, b)(using a.pos) }) ++
            // The type parameter unknown must exist or we won't assign anything to them
            tfreshs.map(Constraint.exist)
          }).addConstraint({
            // The return type of the function should be what is expected.
            Constraint.equal(instantiator.transform(resultType), expected)
          })
        }

        // Tuple Construction.
        case Operation("Tuple", args) => {
          val argsTypes = Seq.fill(args.size)(Unknown.fresh)

          Constrained.sequence(args.zip(argsTypes).map({
            case (e, t) => getExpr(e, t)
          })).transform({
            trees.Tuple(_)
          }).checkImmediate(
            args.size >= 2,
            tupleInsufficientLength,
            expr.pos
          ).addConstraint({
            // This assumes that Tuples are invariant. Is this really the case in Inox ?
            Constraint.equal(expected, trees.TupleType(argsTypes))
          })
        }

        //---- Bindings ----//

        // Let binding.
        case Let(bs, body) if (!bs.isEmpty) => {

          val (ident, otype, value) = bs.head
          val rest = if (bs.tail.isEmpty) body else Let(bs.tail, body)

          val id = getIdentifier(ident)

          val (lt, letType) = otype match {
            case None =>
              val lt = Unknown.fresh
              (lt, Constrained.unify(u ?=> u(lt)))
            case Some(tpe) =>
              (getSimpleType(tpe), getType(tpe, bound = Some(ident.getName)))
          }

          val valueType = Unknown.fresh

          (for {
            v <- getExpr(value, valueType)
            tpe <- letType
            r <- getExpr(rest, expected)(using store + (ident.getName, id, lt, tpe))
          } yield {
            trees.Let(trees.ValDef(id, tpe), v, r)
          }).addConstraint({
            Constraint.equal(valueType, lt)
          })
        }

        // Lambda abstraction.
        case Abstraction(Lambda, bindings, body) => {
          val expectedBody = Unknown.fresh

          val (newStore, tps, cvds) = getExprBindings(bindings)

          (for {
            params <- cvds
            b <- getExpr(body, expectedBody)(using newStore)
          } yield {
            trees.Lambda(params, b)
          }).addConstraint({
            // The expected type should be a function.
            Constraint.equal(expected, trees.FunctionType(tps, expectedBody))
          })
        }

        // Forall-Quantification.
        case Abstraction(Forall, bindings, body) => {
          val (newStore, tps, cvds) = getExprBindings(bindings)

          (for {
            params <- cvds
            b <- getExpr(body, expected)(using newStore)
          } yield {
            trees.Forall(params, b)
          }).addConstraint({
            // The expected type should be boolean.
            Constraint.equal(expected, trees.BooleanType())
          }).addConstraints({
            // The fresh parameter types must exist in the final solution.
            tps.collect { case u: Unknown => Constraint.exist(u) }
          })
        }

        // Exists-Quantification.
        case Abstraction(Exists, bindings, body) => {
          val (newStore, tps, cvds) = getExprBindings(bindings)

          (for {
            params <- cvds
            b <- getExpr(body, expected)(using newStore)
          } yield {
            trees.Not(trees.Forall(params, trees.Not(b)))
          }).addConstraint({
            // The expected type should be boolean.
            Constraint.equal(expected, trees.BooleanType())
          }).addConstraints({
            // The fresh parameter types must exist in the final solution.
            tps.collect { case u: Unknown => Constraint.exist(u) }
          })
        }

        case Abstraction(Choose, bindings @ Seq((id, otype)), body) => {
          val predType = Unknown.fresh

          val (newStore, Seq(tp), cvds) = getExprBindings(bindings)

          (for {
            res <- cvds
            b <- getExpr(body, predType)(using newStore)
          } yield {
            trees.Choose(res.head, b)
          }).addConstraint({
            Constraint.equal(predType, trees.BooleanType())
          }).addConstraint({
            Constraint.equal(tp, expected)
          })
        }

        //---- Type Casting ----//

        // Annotation.
        case TypeAnnotationOperation(expr, tpe) => {
          val inoxTpe = getSimpleType(tpe)

          getExpr(expr, expected).addConstraint({
            Constraint.equal(expected, inoxTpe)
          })
        }

        // Instance checking.
        case IsConstructor(expr, sort, cons) => {
          val tpe = Unknown.fresh
          val tps = sort.tparams.map(_ => Unknown.fresh)

          getExpr(expr, tpe).transform({
            trees.IsConstructor(_, cons.id)
          }).addConstraint({
            // The expected type should be Boolean.
            Constraint.equal(expected, trees.BooleanType())
          }).addConstraint({
            // The expression's type should be an ADT type (with free type parameters)
            Constraint.equal(tpe, trees.ADTType(sort.id, tps))
          })
        }

        //---- Accessors ----//

        // Tuple Selection.
        case Selection(expr, TupleField(i)) => {
          val tupleType = Unknown.fresh
          val memberType = Unknown.fresh

          getExpr(expr, tupleType).transform({
            trees.TupleSelect(_, i)
          }).addConstraint({
            Constraint.equal(memberType, expected)
          }).addConstraint({
            Constraint.atIndex(tupleType, memberType, i)
          })
        }

        // Field Selection.
        case Selection(expr, f @ Fields(fields)) => {
          val expectedExpr = Unknown.fresh

          (for {
            e <- getExpr(expr, expectedExpr)
          } yield { u ?=>
            val trees.ADTType(id, tps) = u(expectedExpr): @unchecked
            val sort = symbols.lookupSort(id).getOrElse(store `getSort` id.name)
            val vd = sort.constructors.flatMap(_.fields).find(vd => f match {
              case FieldName(name) => vd.id.name == name
              case FieldIdentifier(id) => vd.id == id
              case _ => false
            }).getOrElse {
              throw new Exception("getExpr: Unexpected unification result for field: " + f)
            }

            trees.ADTSelector(e, vd.id)
          }).addConstraint({
            Constraint.hasSortIn(expectedExpr, fields.map { case (sort, vd) =>
              sort -> { (tpe: trees.Type) =>
                val ADTType(_, tps) = tpe: @unchecked
                val instantiator = new typeOps.TypeInstantiator((sort.typeArgs zip tps).toMap)
                Seq(Constraint.equal(instantiator.transform(vd.getType), expected))
              }
            }*)
          })
        }

        //---- Function application ----//
        // This is matched last since other constructs have the same shape.

        // Function application.
        case Application(callee, args) => {
          val expectedCallee = Unknown.fresh
          val expectedArgs = Seq.fill(args.length)(Unknown.fresh)

          val constrainedArgs = Constrained.sequence({
            (args zip expectedArgs).map { case (arg, tpe) => getExpr(arg, tpe) }
          })

          (for {
            c <- getExpr(callee, expectedCallee)
            as <- constrainedArgs
          } yield {
            trees.Application(c, as)
          }).addConstraint({
            Constraint.equal(expectedCallee, trees.FunctionType(expectedArgs, expected))
          })
        }

        //---- Others ----//

        case Binding(_, _) => {
          Constrained.fail(unexpectedBinding, expr.pos)
        }

        case _ => {
          Constrained.fail(unknownConstruct, expr.pos)
        }
      }
    }
  }
}
