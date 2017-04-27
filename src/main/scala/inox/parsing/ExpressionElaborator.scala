/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

import scala.util.parsing.input._

import Utils.plural

trait ExpressionElaborators { self: Interpolator => 

  trait ExpressionElaborator { inner: ExprIR.type =>

    import TypeIR.getType

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

    /** Conversion to Inox expression. */
    def getExpr(expr: Expression): trees.Expr = {
      typeCheck(expr, Unknown.fresh(expr.pos))(Map()) match {
        case Unsatifiable(es) => throw new ExpressionElaborationException(es)
        case WithConstraints(elaborator, constraints) => {
          val unifier = Solver.solveConstraints(constraints)
          elaborator(unifier)
        }
      }
    }

    /** Type inference and expression elaboration.
     *
     * @param expr     The expression to typecheck.
     * @param expected The type the expression is expected to have.
     * @param store    Mappings of variables.
     * @return A sequence of constraints and a way to build an Inox expression given a solution to the constraints.
     */
    def typeCheck(expr: Expression, expected: Unknown)
                 (implicit store: Map[String, (inox.Identifier, trees.Type)]): Constrained[trees.Expr] = {
      implicit val position: Position = expr.pos

      expr match {

        //---- Literals ----//

        // Boolean literals.
        case Literal(BooleanLiteral(value)) => Constrained.pure({
          trees.BooleanLiteral(value)
        }).addConstraint({
          Constraint.equal(expected, trees.BooleanType)
        })

        // Unit literal.
        case Literal(UnitLiteral) => Constrained.pure({
          trees.UnitLiteral()
        }).addConstraint({
          Constraint.equal(expected, trees.UnitType)
        })

        // String literal.
        case Literal(StringLiteral(string)) => Constrained.pure({
          trees.StringLiteral(string)
        }).addConstraint({
          Constraint.equal(expected, trees.StringType)
        })

        // Char literal.
        case Literal(CharLiteral(character)) => Constrained.pure({
          trees.CharLiteral(character)
        }).addConstraint({
          Constraint.equal(expected, trees.CharType)
        })

        // Numeric literal.
        case Literal(NumericLiteral(string)) => Constrained.withUnifier({ (unifier: Unifier) =>

          unifier(expected) match {
            case trees.IntegerType => trees.IntegerLiteral(BigInt(string))
            case trees.Int32Type => trees.IntLiteral(string.toInt)
            case trees.BVType(n) => trees.BVLiteral(BigInt(string), n)
            case trees.RealType => {
              val (n, d) = Utils.toFraction(string)
              trees.FractionLiteral(n, d)
            }
            case tpe => throw new Exception("typeCheck: Unexpected type during elaboration: " + tpe)
          }
        }).addConstraint(if (string.contains(".")) {
          Constraint.equal(expected, trees.RealType)
        } else {
          Constraint.isNumeric(expected)
        })

        // Empty set literal.
        // TODO: Also accept it as a Bag literal.
        case Operation("Set", Seq()) => {
          val elementType = Unknown.fresh(expr.pos)
          Constrained.withUnifier({
            (unifier: Unifier) => trees.FiniteSet(Seq(), unifier(elementType))
          }).addConstraint({
            Constraint.equal(expected, trees.SetType(elementType))
          })
        }

        //---- Variables ----//

        // Embedded identifier.
        case Literal(EmbeddedIdentifier(i)) => Constrained.withUnifier({ (unifier: Unifier) =>
          val (_, t) = store(i.uniqueName)
          trees.Variable(i, unifier(t), Set.empty)
        }).checkImmediate(
          store.contains(i.uniqueName), "Unknown identifier " + i + ".", expr.pos
        ).addConstraint({
          Constraint.equal(store(i.uniqueName)._2, expected)
        })

        // Variable.
        case Variable(variable) => Constrained.withUnifier({ (unifier: Unifier) =>
          val (i, t) = store(variable.getName)
          trees.Variable(i, unifier(t), Set.empty)
        }).checkImmediate(
          store.contains(variable.getName), "Unknown variable " + variable.getShortName + ".", expr.pos
        ).addConstraint({
          Constraint.equal(store(variable.getName)._2, expected)
        })

        //---- Embedded values ----//

        // Embedded expressions.
        case Literal(EmbeddedExpr(e)) => Constrained.pure({
          e
        }).addConstraint({
          Constraint.equal(e.getType(symbols), expected)
        }).checkImmediate(
          e.getType(symbols) != trees.Untyped, "Untyped embedded expression.", expr.pos
        )

        // Embedded Scala values.
        case Literal(EmbeddedValue(value)) => value match {
          case b : Boolean =>
            Constrained.pure({
              trees.BooleanLiteral(b)
            }).addConstraint({
              Constraint.equal(expected, trees.BooleanType)
            })
          case n : Int => 
            Constrained.pure({
              trees.IntLiteral(n)
            }).addConstraint({
              Constraint.equal(expected, trees.Int32Type)
            })
          case n : BigInt =>
            Constrained.pure({
              trees.IntegerLiteral(n)
            }).addConstraint({
              Constraint.equal(expected, trees.IntegerType)
            })
          case c : Char =>
            Constrained.pure({
              trees.CharLiteral(c)
            }).addConstraint({
              Constraint.equal(expected, trees.CharType)
            })
          case s : String =>
            Constrained.pure({
              trees.StringLiteral(s)
            }).addConstraint({
              Constraint.equal(expected, trees.StringType)
            })
          case _ : Unit =>
            Constrained.pure({
              trees.UnitLiteral()
            }).addConstraint({
              Constraint.equal(expected, trees.UnitType)
            })
          case _ => Constrained.fail("Unsupported embedded value: " + value + ".", expr.pos)
        }

        //---- Operators ----//

        // Unary minus.
        case Operation("-", Seq(arg)) => {
          typeCheck(arg, expected).map(trees.UMinus(_)).addConstraint({
            Constraint.isNumeric(expected)
          })
        }

        // Unary plus.
        case Operation("+", Seq(arg)) => {
          typeCheck(arg, expected).addConstraint({
            Constraint.isNumeric(expected)
          })
        }

        // Binary operation defined on numeric types.
        case Operation(NumericBinOp(op), args) => {

          Constrained.sequence({
            args.map(typeCheck(_, expected))
          }).map({
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
            args.map(typeCheck(_, expected))
          }).map({
            case Seq(a, b) => op(a, b)
          }).checkImmediate(
            args.length == 2, wrongNumberOfArguments, expr.pos
          ).addConstraint({
            Constraint.isIntegral(expected)
          })
        }

        // Unary negation.
        case Operation("!", Seq(arg)) => {
          typeCheck(arg, expected).map(trees.Not(_)).addConstraint({
            Constraint.equal(expected, trees.BooleanType)
          })
        }

        // Bitwise negation.
        case Operation("~", Seq(arg)) => {
          typeCheck(arg, expected).map(trees.BVNot(_)).addConstraint({
            Constraint.isBitVector(expected)
          })
        }

        // Binary operation defined on comparable types.
        case Operation(ComparableBinOp(op), args) => {

          val expectedArg = Unknown.fresh
          
          Constrained.sequence({
            args.map(typeCheck(_, expectedArg))
          }).map({
            case Seq(a, b) => op(a, b)
          }).checkImmediate(
            args.length == 2, wrongNumberOfArguments, expr.pos
          ).addConstraint({
            Constraint.isComparable(expectedArg)
          }).addConstraint({
            Constraint.equal(expected, trees.BooleanType)
          })
        }

        // Binary operation defined on bit vectors.
        case Operation(BitVectorBinOp(op), args) => {
          Constrained.sequence({
            args.map(typeCheck(_, expected))
          }).map({
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
            args.map(typeCheck(_, expectedArg))
          }).map({
            case Seq(a, b) => trees.Equals(a, b)
          }).checkImmediate(
            args.length == 2, wrongNumberOfArguments, expr.pos
          ).addConstraint({
            Constraint.equal(expected, trees.BooleanType)
          })
        }

        // Inequality.
        case Operation("!=", args) => {
          
          val expectedArg = Unknown.fresh

          Constrained.sequence({
            args.map(typeCheck(_, expectedArg))
          }).map({
            case Seq(a, b) => trees.Not(trees.Equals(a, b))
          }).checkImmediate(
            args.length == 2, wrongNumberOfArguments, expr.pos
          ).addConstraint({
            Constraint.equal(expected, trees.BooleanType)
          })
        }

        // Binary operations defined on booleans.
        case Operation(BooleanBinOp(op), args) => {
          
          Constrained.sequence({
            args.map(typeCheck(_, expected))
          }).map({
            case Seq(a, b) => op(a, b)
          }).checkImmediate(
            args.length == 2, wrongNumberOfArguments, expr.pos
          ).addConstraint({
            Constraint.equal(expected, trees.BooleanType)
          })
        }

        // NAry operations defined on booleans.
        case BooleanNAryOperation(op, args) => {
          
          Constrained.sequence({
            args.map(typeCheck(_, expected))
          }).map(
            op(_)
          ).checkImmediate(
            args.length >= 2, wrongNumberOfArguments, expr.pos
          ).addConstraint({
            Constraint.equal(expected, trees.BooleanType)
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
          Constrained.sequence({
            Seq(str1, str2).map(typeCheck(_, expected))
          }).map({
            case Seq(s1, s2) => trees.StringConcat(s1, s2)
          }).addConstraint({
            Constraint.equal(expected, trees.StringType)
          })
        }

        // Substring.
        case SubstringOperation(str, start, end) => {
          val indexExpected = Unknown.fresh

          Constrained.sequence(Seq(
            typeCheck(str, expected),
            typeCheck(start, indexExpected),
            typeCheck(end, indexExpected)
          )).map({
            case Seq(s, a, b) => trees.SubString(s, a, b)
          }).addConstraint({
            Constraint.equal(expected, trees.StringType)
          }).addConstraint({
            Constraint.equal(indexExpected, trees.IntegerType)
          })
        }

        // String length.
        case StringLengthOperation(s) => {
          val stringExpected = Unknown.fresh
          typeCheck(s, stringExpected).map({
            case e => trees.StringLength(e) 
          }).addConstraint({
            Constraint.equal(stringExpected, trees.StringType)
          }).addConstraint({
            Constraint.equal(expected, trees.IntegerType)
          })
        }

        //---- Operations on Bags ----//

        case BagConstruction(Bindings(fs, _), _) if (!fs.isEmpty) => {
          Constrained.fail(fs.map {
            (e: Expression) => (expectedArrowBinding, e.pos)
          })
        }

        case BagConstruction(Bindings(_, bs), otpe) => {
          val elementType: trees.Type = otpe.map(getType).getOrElse(Unknown.fresh)
          val freshs = Seq.fill(bs.length)(Unknown.fresh)
          val countType = Unknown.fresh

          Constrained.withUnifier({ (unifier: Unifier) =>
            (es: Seq[(trees.Expr, trees.Expr)]) => trees.FiniteBag(es, unifier(elementType))
          }).app({
            Constrained.sequence({
              bs.zip(freshs).map({
                case ((k, v), t) => {
                  typeCheck(k, t).combine(typeCheck(v, countType))({
                    (a: trees.Expr, b: trees.Expr) => (a, b)
                  }).addConstraint({
                    Constraint.subtype(t, elementType)
                  })
                }
              })
            })
          }).addConstraint({
            Constraint.equal(countType, trees.IntegerType)
          }).addConstraint({
            Constraint.equal(expected, trees.BagType(elementType))
          })
        }

        // Bag multiplicity.
        case BagMultiplicityOperation(map, key, otpe) => {
          val elementType = otpe.map(getType).getOrElse(Unknown.fresh)
          val keyExpected = Unknown.fresh
          val mapExpected = Unknown.fresh

          typeCheck(map, mapExpected).combine(typeCheck(key, keyExpected))({
            case (m, k) => trees.MultiplicityInBag(k, m)
          }).addConstraint({
            Constraint.equal(expected, trees.IntegerType)
          }).addConstraint({
            Constraint.subtype(keyExpected, elementType)
          }).addConstraint({
            Constraint.equal(mapExpected, trees.BagType(elementType))
          })
        }

        // Bag binary operation.
        case BagBinaryOperation(map1, map2, op, otpe) => {
          val elementType = otpe.map(getType).getOrElse(Unknown.fresh)
          val mapExpected = Unknown.fresh

          typeCheck(map1, mapExpected).combine(typeCheck(map2, mapExpected))({
            case (m1, m2) => op(m1, m2)
          }).addConstraint({
            Constraint.equal(mapExpected, trees.BagType(elementType))
          })
        }

        // Bag add operation.
        case BagAddOperation(bag, elem, otpe) => {
          val elementExpected = Unknown.fresh
          val elementType = otpe.map(getType).getOrElse(Unknown.fresh)

          typeCheck(bag, expected).map({ (b: trees.Expr) => 
            (e: trees.Expr) => trees.BagAdd(b, e)
          }).app({
            typeCheck(elem, elementExpected)
          }).addConstraint({
            Constraint.equal(expected, trees.BagType(elementType))
          }).addConstraint({
            Constraint.subtype(elementExpected, elementType)
          })
        }

        //---- Operations on Maps ----//

        case MapConstruction(_, Bindings(fs, _), _) if (!fs.isEmpty) => {
          Constrained.fail(fs.map {
            (e: Expression) => (expectedArrowBinding, e.pos)
          })
        }

        case MapConstruction(default, Bindings(_, bs), optEitherKeyAll) => {

          val (oKeyType, oValueType) = optEitherKeyAll match {
            case None => (None, None)
            case Some(Left(t)) => (Some(getType(t)), None)
            case Some(Right((t1, t2))) => (Some(getType(t1)), Some(getType(t2)))
          } 

          val keyType = oKeyType.getOrElse(Unknown.fresh)
          val valueType = oValueType.getOrElse(Unknown.fresh)
          val defaultFresh = Unknown.fresh
          val freshs = Seq.fill(bs.length)((Unknown.fresh, Unknown.fresh))

          Constrained.withUnifier((unifier: Unifier) => {
            (t: (trees.Expr, Seq[(trees.Expr, trees.Expr)])) => 
              trees.FiniteMap(t._2, t._1, unifier(keyType), unifier(valueType))
          }).app({
            Constrained.sequence({
              bs.zip(freshs).map({
                case ((k, v), (tk, tv)) => {
                  typeCheck(k, tk).combine(typeCheck(v, tv))({
                    (a: trees.Expr, b: trees.Expr) => (a, b)
                  }).addConstraint({
                    Constraint.subtype(tk, keyType)
                  }).addConstraint({
                    Constraint.subtype(tv, valueType)
                  })
                }
              })
            }).combine({
              typeCheck(default, defaultFresh).addConstraint({
                Constraint.subtype(defaultFresh, valueType)
              })
            })({
              case (es, e) => (e, es)
            })
          }).addConstraint({
            Constraint.equal(expected, trees.MapType(keyType, valueType))
          })
        }

        // Map apply.
        case MapApplyOperation(map, key, otpes) => {
          val (keyType, valueType) = otpes.map({
            case (t1, t2) => (getType(t1), getType(t2))
          }).getOrElse((Unknown.fresh, Unknown.fresh))
          val keyExpected = Unknown.fresh
          val mapExpected = Unknown.fresh

          typeCheck(map, mapExpected).combine(typeCheck(key, keyExpected))({
            case (m, k) => trees.MapApply(m, k)
          }).addConstraint({
            Constraint.subtype(keyExpected, keyType)
          }).addConstraint({
            Constraint.equal(expected, valueType)
          }).addConstraint({
            Constraint.equal(mapExpected, trees.MapType(keyType, valueType))
          })
        }

        // Map updated.
        case MapUpdatedOperation(map, key, value, otpes) => {
          val (keyType, valueType) = otpes.map({
            case (t1, t2) => (getType(t1), getType(t2))
          }).getOrElse((Unknown.fresh, Unknown.fresh))
          val keyExpected = Unknown.fresh
          val valueExpected = Unknown.fresh

          Constrained.sequence(Seq(
            typeCheck(map, expected),
            typeCheck(key, keyExpected),
            typeCheck(value, valueExpected)
          )).map({
            case Seq(m, k, v) => trees.MapUpdated(m, k, v)
          }).addConstraint({
            Constraint.equal(expected, trees.MapType(keyType, valueType))
          }).addConstraint({
            Constraint.subtype(keyExpected, keyType)
          }).addConstraint({
            Constraint.subtype(valueExpected, valueType)
          })
        }

        //---- Operations on Set ----//

        // Call to the Set constructor.
        case SetConstruction(es, otpe) => {
          val upper = otpe.map(getType).getOrElse(Unknown.fresh)
          val lowers = Seq.fill(es.length) { Unknown.fresh }

          Constrained.withUnifier({ (unifier: Unifier) => 
            (elems: Seq[trees.Expr]) => trees.FiniteSet(elems, unifier(upper))
          }).app({
            Constrained.sequence(es.zip(lowers).map{
              case (e, lower) => typeCheck(e, lower).addConstraint({
                Constraint.subtype(lower, upper)
              })
            })
          }).addConstraint({
            Constraint.equal(expected, trees.SetType(upper))
          })
        }

        // Call to contains.
        case ContainsOperation(set, elem, otpe) => {
          val setType = Unknown.fresh
          val elementExpected = Unknown.fresh
          val elementType = otpe.map(getType).getOrElse(Unknown.fresh)

          typeCheck(set, setType).map({ (s: trees.Expr) => 
            (e: trees.Expr) => trees.ElementOfSet(e, s)
          }).app({
            typeCheck(elem, elementExpected)
          }).addConstraint({
            Constraint.equal(expected, trees.BooleanType)
          }).addConstraint({
            Constraint.equal(setType, trees.SetType(elementType))
          }).addConstraint({
            Constraint.subtype(elementExpected, elementType)
          })
        }

        // Call to subset.
        case SubsetOperation(set1, set2, otpe) => {
          val setType = Unknown.fresh
          val elementType = otpe.map(getType).getOrElse(Unknown.fresh)

          typeCheck(set1, setType).map({ (s1: trees.Expr) => 
            (s2: trees.Expr) => trees.SubsetOf(s1, s2)
          }).app({
            typeCheck(set2, setType)
          }).addConstraint({
            Constraint.equal(expected, trees.BooleanType)
          }).addConstraint({
            Constraint.equal(setType, trees.SetType(elementType))
          })
        }

        // Binary operations on set that return sets.
        case SetBinaryOperation(set1, set2, f, otpe) => {
          val elementType = otpe.map(getType).getOrElse(Unknown.fresh)

          typeCheck(set1, expected).map({ (s1: trees.Expr) => 
            (s2: trees.Expr) => f(s1, s2)
          }).app({
            typeCheck(set2, expected)
          }).addConstraint({
            Constraint.equal(expected, trees.SetType(elementType))
          })
        }

        // Set add operation.
        case SetAddOperation(set, elem, otpe) => {
          val elementExpected = Unknown.fresh
          val elementType = otpe.map(getType).getOrElse(Unknown.fresh)

          typeCheck(set, expected).map({ (s: trees.Expr) => 
            (e: trees.Expr) => trees.SetAdd(s, e)
          }).app({
            typeCheck(elem, elementExpected)
          }).addConstraint({
            Constraint.equal(expected, trees.SetType(elementType))
          }).addConstraint({
            Constraint.subtype(elementExpected, elementType)
          })
        }

        //---- Conditionals ----//

        // Conditional expression.
        case Operation("IfThenElse", Seq(cond, thenn, elze)) => {
          
          val expectedCond = Unknown.fresh

          Constrained.sequence(Seq(
            typeCheck(cond, expectedCond),
            typeCheck(thenn, expected),
            typeCheck(elze, expected)
          )).map({
            case Seq(condExpr, thennExpr, elzeExpr) => trees.IfExpr(condExpr, thennExpr, elzeExpr)
          }).addConstraint({
            Constraint.equal(expectedCond, trees.BooleanType)
          })
        }

        // Assumptions
        case Operation("Assume", Seq(p, e)) => {
          val booleanExpected = Unknown.fresh
          typeCheck(p, booleanExpected).combine(typeCheck(e, expected))({
            case (pred, body) => trees.Assume(pred, body)
          }).addConstraint({
            Constraint.equal(booleanExpected, trees.BooleanType)
          })
        }

        //---- Functions ----//

        // Function invocation.
        case Application(TypedFunDef(fd, optTpeArgs), args) => {

          val freshs = args.map({ case a => Unknown.fresh(a.pos) })

          val constrainedArgs = Constrained.sequence {
            args.zip(freshs).map({ case (e, t) => typeCheck(e, t) })
          }

          val typeParamToFresh = fd.tparams.map({
            (t: trees.TypeParameterDef) => t.tp -> Unknown.fresh
          })

          val instantiator = new symbols.TypeInstantiator(typeParamToFresh.toMap)

          val paramTypes = fd.params.map({
            (vd: trees.ValDef) => instantiator.transform(vd.tpe)
          })

          val invok = Constrained.withUnifier({ (unifier: Unifier) =>
            (realArgs: Seq[trees.Expr]) => trees.FunctionInvocation(fd.id, typeParamToFresh.map({
              case (_, u) => unifier(u)
            }), realArgs)
          })
          
          val constrained = invok.app({
            constrainedArgs
          }).checkImmediate(
            // Their should be the same number of argument applied than parameters of the function.
            args.length == fd.params.length,
            functionArity(fd.id.name, fd.params.length, args.length),
            expr.pos
          ).addConstraints({
            // The types of arguments should be subtype of the type of the parameters.
            freshs.zip(paramTypes).map({ case (a, b) => Constraint.subtype(a, b)(a.pos) })
          }).addConstraint({
            // The return type of the function should be what is expected.
            Constraint.equal(instantiator.transform(fd.returnType), expected)
          })

          optTpeArgs match {
            case None => constrained
            case Some(tpeArgs) => {
              constrained.addConstraints({
                // The annotated types should correspond to the type of the parameters.
                tpeArgs.zip(typeParamToFresh.map(_._2)).map({ case (a, b) => Constraint.equal(getType(a), b) })
              }).checkImmediate(
                // Their should be the same number of type applied than type parameters of the function.
                tpeArgs.length == fd.tparams.length,
                functionTypeArity(fd.id.name, fd.tparams.length, tpeArgs.length),
                expr.pos
              )
            }
          }
        }
        
        // Constructor invocation.
        case Application(TypedConsDef(cons, optTpeArgs), args) => {

          val freshs = args.map({ case a => Unknown.fresh(a.pos) })

          val constrainedArgs = Constrained.sequence {
            args.zip(freshs).map({ case (e, t) => typeCheck(e, t) })
          }

          val typeParamToFresh = cons.tparams.map({
            (t: trees.TypeParameterDef) => t.tp -> Unknown.fresh
          })

          val instantiator = new symbols.TypeInstantiator(typeParamToFresh.toMap)

          val paramTypes = cons.fields.map({
            (vd: trees.ValDef) => instantiator.transform(vd.tpe)
          })

          val invok = Constrained.withUnifier({ (unifier: Unifier) =>
            (realArgs: Seq[trees.Expr]) => trees.ADT(cons.typed(typeParamToFresh.map({
              case (_, u) => unifier(u)
            }))(symbols).toType, realArgs)
          })
          
          val constrained = invok.app({
            constrainedArgs
          }).checkImmediate(
            // Their should be the same number of argument applied than parameters of the constructor.
            args.length == cons.fields.length,
            functionArity(cons.id.name, cons.fields.length, args.length, "Constructor"),
            expr.pos
          ).addConstraints({
            // The types of arguments should be subtypes of the parameters.
            freshs.zip(paramTypes).map({ case (a, b) => Constraint.subtype(a, b)(a.pos) })
          }).addConstraint({
            // The return type of the constructor application should be what is expected.
            Constraint.equal(cons.typed(typeParamToFresh.map(_._2))(symbols).toType, expected)
          })

          optTpeArgs match {
            case None => constrained
            case Some(tpeArgs) => {
              constrained.addConstraints({
                // The annotated types should correspond to the type of the parameters.
                tpeArgs.zip(typeParamToFresh.map(_._2)).map({ case (a, b) => Constraint.equal(getType(a), b) })
              }).checkImmediate(
                // Their should be the same number of type applied than type parameters of the function.
                tpeArgs.length == cons.tparams.length,
                functionTypeArity(cons.id.name, cons.tparams.length, tpeArgs.length, "Constructor"),
                expr.pos
              )
            }
          }
        }

        // Tuple Construction.
        case Operation("Tuple", args) => {
          val argsTypes = Seq.fill(args.size)(Unknown.fresh)

          Constrained.sequence(args.zip(argsTypes).map({
            case (e, t) => typeCheck(e, t)
          })).map({
            case es => trees.Tuple(es)
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
          val rest = if (bs.tail.isEmpty) {
            body
          }
          else {
            Let(bs.tail, body)
          }

          val inoxIdent = ident match {
            case IdentifierName(name) => inox.FreshIdentifier(name)
            case IdentifierIdentifier(i) => i
            case IdentifierHole(_) => throw new Error("Expression contains holes.")
          }

          val identType = Unknown.fresh
          val valueType = Unknown.fresh

          val toLet = Constrained.withUnifier { (unifier: Unifier) =>
            (es: Seq[trees.Expr]) => trees.Let(trees.ValDef(inoxIdent, unifier(identType)), es(0), es(1))
          }

          val args = Constrained.sequence(Seq(
            typeCheck(value, valueType),
            typeCheck(rest, expected)(store + ((ident.getName, (inoxIdent, identType))))
          ))

          val constrained = toLet.app({
            args
          }).addConstraint({
            Constraint.subtype(valueType, identType)
          })

          if (otype.isEmpty) {
            constrained
          }
          else {
            constrained.addConstraint({
              Constraint.equal(identType, getType(otype.get))
            })
          }
        }

        // Lambda abstraction.
        case Abstraction(Lambda, bindings, body) => {
          val expectedBody = Unknown.fresh

          val bs = bindings.map({
            case (IdentifierName(name), _) => (inox.FreshIdentifier(name), Unknown.fresh)
            case (IdentifierIdentifier(i), _) => (i, Unknown.fresh)
            case (IdentifierHole(_), _) => throw new Error("Expression contains holes.")
          })

          val subTypes = Seq.fill(bindings.size)(Unknown.fresh)
          val superType = Unknown.fresh

          Constrained.withUnifier({ (unifier: Unifier) => 
            val vds = bs.map({ case (i, t) => trees.ValDef(i, unifier(t)) })

            (bodyExpr: trees.Expr) => trees.Lambda(vds, bodyExpr)
          }).app({
            typeCheck(body, expectedBody)(store ++ bindings.map(_._1.getName).zip(bs))
          }).addConstraints({
            // Type of variable should correspond to those annotated.
            bindings.zip(bs).flatMap({
              case ((_, oType), (_, tpe)) => oType.map((t: Type) => Constraint.equal(getType(t), tpe))
            })
          }).addConstraint({
            // The expected type should be a function.
            Constraint.equal(expected, trees.FunctionType(subTypes, superType))
          }).addConstraints({
            // Type of arguments should be super types of expected type arguments.
            bs.map(_._2).zip(subTypes).map({
              case (sup, sub) => Constraint.subtype(sub, sup)
            })
          }).addConstraint({
            // Return type of the function should be a subtype of the expected return type.
            Constraint.subtype(expectedBody, superType)
          })
        }

        // Forall-Quantification.
        case Abstraction(Forall, bindings, body) => {

          val bs = bindings.map({
            case (IdentifierName(name), _) => (inox.FreshIdentifier(name), Unknown.fresh)
            case (IdentifierIdentifier(i), _) => (i, Unknown.fresh)
            case (IdentifierHole(_), _) => throw new Error("Expression contains holes.")
          })

          Constrained.withUnifier({ (unifier: Unifier) => 
            val vds = bs.map({ case (i, t) => trees.ValDef(i, unifier(t)) })

            (bodyExpr: trees.Expr) => trees.Forall(vds, bodyExpr)
          }).app({
            typeCheck(body, expected)(store ++ bindings.map(_._1.getName).zip(bs))
          }).addConstraints({
            // Type of variable should correspond to those annotated.
            bindings.zip(bs).flatMap({
              case ((_, oType), (_, tpe)) => oType.map((t: Type) => Constraint.equal(getType(t), tpe))
            })
          }).addConstraint({
            // The expected type should be boolean.
            Constraint.equal(expected, trees.BooleanType)
          })
        }

        // Exists-Quantification.
        case Abstraction(Exists, bindings, body) => {

          val bs = bindings.map({
            case (IdentifierName(name), _) => (inox.FreshIdentifier(name), Unknown.fresh)
            case (IdentifierIdentifier(i), _) => (i, Unknown.fresh)
            case (IdentifierHole(_), _) => throw new Error("Expression contains holes.")
          })

          Constrained.withUnifier({ (unifier: Unifier) => 
            val vds = bs.map({ case (i, t) => trees.ValDef(i, unifier(t)) })

            (bodyExpr: trees.Expr) => trees.Not(trees.Forall(vds, trees.not(bodyExpr)))
          }).app({
            typeCheck(body, expected)(store ++ bindings.map(_._1.getName).zip(bs))
          }).addConstraints({
            // Type of variable should correspond to those annotated.
            bindings.zip(bs).flatMap({
              case ((_, oType), (_, tpe)) => oType.map((t: Type) => Constraint.equal(getType(t), tpe))
            })
          }).addConstraint({
            // The expected type should be boolean.
            Constraint.equal(expected, trees.BooleanType)
          })
        }

        case Abstraction(Choose, Seq((id, otype)), body) => {
          val identType = Unknown.fresh
          val predType = Unknown.fresh
          val inoxIdent = id match {
            case IdentifierIdentifier(i) => i
            case IdentifierName(name) => inox.FreshIdentifier(name)
            case IdentifierHole(_) => throw new Error("Expression contains holes.")
          }
          
          val constrained = Constrained.withUnifier({ (unifier: Unifier) =>
            (pred: trees.Expr) => trees.Choose(trees.ValDef(inoxIdent, unifier(identType)), pred)
          }).app({
            typeCheck(body, predType)(store + (id.getName -> ((inoxIdent, identType))))
          }).addConstraint({
            Constraint.equal(predType, trees.BooleanType)
          }).addConstraint({
            Constraint.subtype(identType, expected)
          })

          otype match {
            case Some(tpe) => constrained.addConstraint({
              Constraint.equal(identType, getType(tpe))
            })
            case _ => constrained
          }
        } 

        //---- Type Casting ----//

        // Annotation.
        case TypeAnnotationOperation(expr, tpe) => {
          val inoxTpe = getType(tpe)
          val sub = Unknown.fresh

          typeCheck(expr, sub).addConstraint({
            Constraint.equal(expected, inoxTpe)
          }).addConstraint({
            Constraint.subtype(sub, inoxTpe)
          })
        }

        // Casting.
        case AsInstanceOfOperation(expr, tpe) => {
          val inoxTpe = getType(tpe)

          val sup = Unknown.fresh
          val sub = Unknown.fresh
          typeCheck(expr, sub).map({
            (e: trees.Expr) => trees.AsInstanceOf(e, inoxTpe)
          }).addConstraint({
            // The type of the casted expression is the expected type.
            Constraint.equal(inoxTpe, expected)
          }).addConstraint({
            // There should exist a type which is a (non-strict) super type of the annotated type...
            Constraint.subtype(inoxTpe, sup)
          }).addConstraint({
            // ... and a super type of the type of the expression being cast. 
            Constraint.subtype(sub, sup)
          })
        }

        // Instance checking.
        case IsInstanceOfOperation(expr, tpe) => {
          val inoxTpe = getType(tpe)

          val sup = Unknown.fresh
          val sub = Unknown.fresh
          typeCheck(expr, sub).map({
            (e: trees.Expr) => trees.IsInstanceOf(e, inoxTpe)
          }).addConstraint({
            // The expected type should be Boolean.
            Constraint.equal(expected, trees.BooleanType)
          }).addConstraint({
            // There should exist a type which is a (non-strict) super type of the annotated type...
            Constraint.subtype(inoxTpe, sup)
          }).addConstraint({
            // ... and a super type of the type of the expression being checked. 
            Constraint.subtype(sub, sup)
          })
        }

        //---- Accessors ----//

        // Tuple Selection.
        case Selection(expr, TupleField(i)) => {
          val tupleType = Unknown.fresh
          val memberType = Unknown.fresh

          typeCheck(expr, tupleType).map({
            case tuple => trees.TupleSelect(tuple, i)
          }).addConstraint({
            Constraint.equal(memberType, expected)
          }).addConstraint({
            Constraint.atIndex(tupleType, memberType, i)
          })
        }

        // Field Selection.
        case Selection(expr, Field((cons, vd))) => {
          val expectedExpr = Unknown.fresh

          val typeParamToFresh = cons.tparams.map({
            (t: trees.TypeParameterDef) => t.tp -> Unknown.fresh
          })

          val instantiator = new symbols.TypeInstantiator(typeParamToFresh.toMap)

          val fieldType = instantiator.transform(vd.tpe)
          val adtType = instantiator.transform(cons.typed(symbols).toType)

          typeCheck(expr, expectedExpr).map({
            (e: trees.Expr) => trees.ADTSelector(e, vd.id)
          }).addConstraint({
            // The field type should be what is expected.
            Constraint.equal(fieldType, expected)
          }).addConstraint({
            // The type of the expression being selected should be exactly
            // that of the ADT constructor.
            Constraint.equal(adtType, expectedExpr)
          })
        }

        //---- Function application ----//
        // This is matched last since other constructs have the same shape.

        // Function application.
        case Application(callee, args) => {
          val expectedCallee = Unknown.fresh
          val argsUpperBounds = Seq.fill(args.length)(Unknown.fresh)
          val expectedArgs = Seq.fill(args.length)(Unknown.fresh)
          val retType = Unknown.fresh

          Constrained.sequence({
            typeCheck(callee, expectedCallee) +: args.zip(expectedArgs).map({
              case (arg, expectedArg) => typeCheck(arg, expectedArg)
            })
          }).map({
            case exprs => trees.Application(exprs.head, exprs.tail)
          }).addConstraint({
            Constraint.equal(expectedCallee, trees.FunctionType(argsUpperBounds, retType))
          }).addConstraints({
            expectedArgs.zip(argsUpperBounds).map({
              case (e, u) => Constraint.subtype(e, u)
            })
          }).addConstraint({
            Constraint.subtype(retType, expected)
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
