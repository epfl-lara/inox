/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package princess

//
// Interface file between Inox and Princess
// Currently work in progress. Only supports subset
// of the features from Inox. Needs a special version
// of Princess supporting ADT:s.
//
// Author: Peter Backeman, Uppsala University <peter.backeman@it.uu.se>
//

import ap._
import ap.parser.{Context => _, _}
import ap.basetypes._
import ap.theories.{ADT => PADT, _}
import ap.theories.{ModuloArithmetic => Mod}
import ap.types.UninterpretedSortTheory

import utils._
import SolverResponses._

import scala.collection.mutable.{ListBuffer, Map => MutableMap}

abstract class AbstractPrincessSolver(override val program: Program,
                                      override val context: Context)
                                     (using protected val semantics: program.Semantics)
  extends AbstractSolver with ADTManagers {
  import scala.language.postfixOps
  import IExpression._

  case class PrincessSolverException(msg: String)
      extends Exception("handle PrincessSolver: " + msg)

  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  val name = "Princess"

  interruptManager.registerForInterrupts(this)

  type Trees = IExpression
  type Model = ap.api.PartialModel

  private val enableAssertions = reporter.isDebugEnabled

  ap.util.Debug enableAllAssertions enableAssertions
  protected[princess] val p = SimpleAPI(
    enableAssert = enableAssertions,
    dumpScala = false,
    scalaDumpBasename = options.findOptionOrDefault(Main.optFiles).headOption.map(_.getName).getOrElse("NA") + "-",
    dumpSMT = enableAssertions,
    dumpDirectory = if (enableAssertions) {
      val dir = new java.io.File("pri-sessions")
      dir.mkdirs()
      dir
    } else {
      null
    }
  )

  // Internal maps storing created Constant, Variables, ADT and Function symbols
  private[princess] val variables = new IncrementalBijection[Variable, IExpression]
  private[princess] val functions = new IncrementalBijection[TypedFunDef, IFunction]
  private[princess] val lambdas = new IncrementalBijection[FunctionType, IFunction]

  private[princess] val constructors = new IncrementalBijection[ConsType, IFunction]
  private[princess] val selectors    = new IncrementalBijection[(ConsType, Int), IFunction]
  private[princess] val testers      = new IncrementalBijection[ConsType, (PADT, Int)]

  private[princess] val sorts = new IncrementalMap[Type, Sort]

  private[princess] val adtManager = new ADTManager

  def typeToSort(tpe: Type): Sort = tpe match {
    case tpe @ (_: ADTType | _: TupleType | _: TypeParameter | UnitType()) =>
      if (!sorts.contains(tpe)) declareStructuralSort(tpe)
      sorts(tpe)
    case BooleanType() => sorts.cached(tpe)(Sort.Bool)
    case IntegerType() => sorts.cached(tpe)(Sort.Integer)
    case ft: FunctionType => sorts.cached(ft)(Sort.createInfUninterpretedSort(ft.toString))
    case CharType() => sorts.cached(tpe)(Mod.UnsignedBVSort(16))
    case BVType(true, size) => sorts.cached(tpe)(Mod.SignedBVSort(size))
    case BVType(false, size) => sorts.cached(tpe)(Mod.UnsignedBVSort(size))
    case _ => unsupported(tpe)
  }

  private def declareStructuralSort(tpe: Type): Unit = {
    adtManager.declareADTs(tpe, (adts: Seq[(Type, DataType)]) => {
      val indexMap: Map[Type, Int] = adts.map(_._1).zipWithIndex.toMap

      def typeToSortRef(tpe: Type): PADT.CtorArgSort = {
        if (indexMap contains tpe) {
          PADT.ADTSort(indexMap(tpe))
        } else tpe match {
          // Terms of signed bit-vectors are built in the unsigned range (see `parseTerm`), so
          // fields of signed bit-vectors must have the unsigned sort to hold negative values
          case BVType(true, size) => PADT.OtherSort(Mod.UnsignedBVSort(size))
          case _ => PADT.OtherSort(typeToSort(tpe))
        }
      }

      val adt = new PADT(
        adts.map(p => p._2.sym.uniqueName),
        adts.flatMap(p => p._2.cases.map { c =>
          c.sym.uniqueName -> PADT.CtorSignature(c.fields.map {
            case (id, tpe) => id.uniqueName -> typeToSortRef(tpe)
          }, PADT.ADTSort(indexMap(p._1)))
        })
      )

      for (((tpe, _), sort) <- (adts zip adt.sorts)) sorts += tpe -> sort

      for ((cse, i) <- adts.flatMap(_._2.cases).zipWithIndex) {
        constructors += cse.tpe -> adt.constructors(i)
        testers += cse.tpe -> (adt -> i)

        for ((sel, i) <- adt.selectors(i).zipWithIndex) selectors += (cse.tpe, i) -> sel
      }
    })

    sorts(tpe)
  }

  object inoxToPrincess {

    def parseFormula(expr: Expr)(using bindings: Map[Variable, IExpression]): IFormula = expr match {
      case BooleanLiteral(value) =>
        value

      case v: Variable =>
        bindings.getOrElse(v, declareVariable(v)).asInstanceOf[IFormula]

      case Let(vd, e, b) =>
        parseFormula(b)(using bindings + (vd.toVariable -> (vd.getType match {
          case BooleanType() => parseFormula(e)
          case _ => parseTerm(e)
        })))

      // BOOLEAN CONNECTIVES
      case Not(expr) =>
        !parseFormula(expr)

      case And(exprs) =>
        val subExprs = for (e <- exprs) yield parseFormula(e)
        subExprs.tail.foldLeft(subExprs.head)((p, q) => p & q)

      case Or(exprs) =>
        val subExprs = for (e <- exprs) yield parseFormula(e)
        subExprs.tail.foldLeft(subExprs.head)((p, q) => p | q)

      case Implies(lhs, rhs) =>
        val pLhs = parseFormula(lhs)
        val pRhs = parseFormula(rhs)
        pLhs ==> pRhs

      // EQUALITY
      case Equals(lhs, rhs) => lhs.getType match {
        case BooleanType() => parseFormula(lhs) <=> parseFormula(rhs)
        case _ => parseTerm(lhs) === parseTerm(rhs)
      }

      // INTEGER COMPARISON
      case LessThan(lhs, rhs) => lhs.getType match {
        case BVType(true, _) => Mod.bvslt(parseTerm(lhs), parseTerm(rhs))
        case BVType(false, _) => Mod.bvult(parseTerm(lhs), parseTerm(rhs))
        case CharType() => Mod.bvult(parseTerm(lhs), parseTerm(rhs))
        case IntegerType() => parseTerm(lhs) < parseTerm(rhs)
        case _ => unsupported(expr)
      }

      case GreaterThan(lhs, rhs) => lhs.getType match {
        case BVType(true, _) => Mod.bvsgt(parseTerm(lhs), parseTerm(rhs))
        case BVType(false, _) => Mod.bvugt(parseTerm(lhs), parseTerm(rhs))
        case CharType() => Mod.bvugt(parseTerm(lhs), parseTerm(rhs))
        case IntegerType() => parseTerm(lhs) > parseTerm(rhs)
        case _ => unsupported(expr)
      }

      case LessEquals(lhs, rhs) => lhs.getType match {
        case BVType(true, _) => Mod.bvsle(parseTerm(lhs), parseTerm(rhs))
        case BVType(false, _) => Mod.bvule(parseTerm(lhs), parseTerm(rhs))
        case CharType() => Mod.bvule(parseTerm(lhs), parseTerm(rhs))
        case IntegerType() => parseTerm(lhs) <= parseTerm(rhs)
        case _ => unsupported(expr)
      }

      case GreaterEquals(lhs, rhs) => lhs.getType match {
        case BVType(true, _) => Mod.bvsge(parseTerm(lhs), parseTerm(rhs))
        case BVType(false, _) => Mod.bvuge(parseTerm(lhs), parseTerm(rhs))
        case CharType() => Mod.bvuge(parseTerm(lhs), parseTerm(rhs))
        case IntegerType() => parseTerm(lhs) >= parseTerm(rhs)
        case _ => unsupported(expr)
      }

      // ADT INSTANCE OF
      case IsConstructor(expr, id) =>
        val tpe @ ADTType(_, tps) = expr.getType: @unchecked
        typeToSort(tpe)
        val (sort, tester) = testers.toB(ADTCons(id, tps))
        sort.hasCtor(parseTerm(expr), tester)

      case (_: FunctionInvocation) | (_: Application) | (_: ADTSelector) | (_: TupleSelect) =>
        parseTerm(expr) === 0

      case IfExpr(cond, thenn, elze) =>
        IFormulaITE(parseFormula(cond), parseFormula(thenn), parseFormula(elze))

      case _ => unsupported(expr, "Unexpected formula " + expr)
    }

    def parseTerm(expr: Expr)(using bindings: Map[Variable, IExpression]): ITerm = {
      val res: ITerm = expr match {
        case FunctionInvocation(id, tps, args) =>
          val f = functions.cachedB(getFunction(id, tps.map(_.getType))) {
            declared(p.createFunction(id.uniqueName, args.size))(p.addFunction(_))
          }
          val pArgs = for (a <- args) yield parseTerm(a)
          IFunApp(f, pArgs)

        case Application(caller, args) =>
          val f = lambdas.cachedB(caller.getType.asInstanceOf[FunctionType]) {
            declared(p.createFunction(FreshIdentifier("dynLambda").uniqueName, args.size + 1))(p.addFunction(_))
          }
          val pArgs = for (a <- caller +: args) yield parseTerm(a)
          IFunApp(f, pArgs)

        // ADT | Tuple
        case (_: ADT) | (_: Tuple) | (_: GenericValue) | (_: UnitLiteral) =>
          val tpe = expr.getType
          typeToSort(tpe)
          val (cons, args) = expr match {
            case ADT(id, tps, args) => (ADTCons(id, tps.map(_.getType)), args)
            case Tuple(args) => (TupleCons(args.map(_.getType)), args)
            case GenericValue(tp, i) => (TypeParameterCons(tp), Seq(IntegerLiteral(i)))
            case UnitLiteral() => (UnitCons, Seq.empty)
          }
          val constructor = constructors.toB(cons)
          constructor(args.map(parseTerm)*)

        case (_: ADTSelector) | (_: TupleSelect) =>
          val (cons, rec, i) = expr match {
            case s @ ADTSelector(adt, _) =>
              val tpe = adt.getType.asInstanceOf[ADTType]
              (ADTCons(s.constructor.id, tpe.tps), adt, s.selectorIndex)
            case TupleSelect(tpl, i) =>
              val TupleType(tps) = tpl.getType: @unchecked
              (TupleCons(tps), tpl, i - 1)
          }

          val tpe = rec.getType
          typeToSort(tpe)
          val selector = selectors.toB(cons -> i)
          selector(parseTerm(rec))

        case BooleanLiteral(true) => i(0)
        case BooleanLiteral(false) => i(1)

        // @nv: this MUST come at least after having dealt with FunctionInvocation,
        //      Application and ADTSelectors which can return booleans
        case IsTyped(_, BooleanType()) =>
          ITermITE(parseFormula(expr), i(0), i(1))

        case v: Variable =>
          bindings.getOrElse(v, declareVariable(v)).asInstanceOf[ITerm]

        case Let(vd, e, b) =>
          parseTerm(b)(using bindings + (vd.toVariable -> (vd.getType match {
            case BooleanType() => parseFormula(e)
            case _ => parseTerm(e)
          })))

        case IfExpr(cond, thenn, elze) =>
          ITermITE(parseFormula(cond), parseTerm(thenn), parseTerm(elze))

        // LITERALS
        case IntegerLiteral(value) => IdealInt(value.bigInteger)

        case bv @ BVLiteral(signed, bits, size) =>
          if (signed) Mod.cast2SignedBV(size, IdealInt(bv.toBigInt.bigInteger))
          else Mod.cast2UnsignedBV(size, IdealInt(bv.toBigInt.bigInteger))

        case CharLiteral(c) =>
          Mod.cast2UnsignedBV(16, c.toInt)

        // INTEGER ARITHMETIC
        case Plus(lhs, rhs) => lhs.getType match {
          case BVType(_, _) => Mod.bvadd(parseTerm(lhs), parseTerm(rhs))
          case IntegerType() => parseTerm(lhs) + parseTerm(rhs)
          case _ => unsupported(expr)
        }

        case Minus(lhs, rhs) => lhs.getType match {
          case BVType(_, _) => Mod.bvsub(parseTerm(lhs), parseTerm(rhs))
          case IntegerType() => parseTerm(lhs) - parseTerm(rhs)
          case _ => unsupported(expr)
        }

        case Times(lhs, rhs) => lhs.getType match {
          case BVType(_, _) => Mod.bvmul(parseTerm(lhs), parseTerm(rhs))
          case IntegerType() => p.mult(parseTerm(lhs), parseTerm(rhs))
          case _ => unsupported(expr)
        }

        case UMinus(e) => e.getType match {
          case BVType(_, _) => Mod.bvneg(parseTerm(e))
          case IntegerType() => - parseTerm(e)
          case _ => unsupported(expr)
        }

        case Division(lhs, rhs) => lhs.getType match {
          case BVType(true, _) => Mod.bvsdiv(parseTerm(lhs), parseTerm(rhs))
          case BVType(false, _) => Mod.bvudiv(parseTerm(lhs), parseTerm(rhs))
          case IntegerType() => p.mulTheory.eDiv(parseTerm(lhs), parseTerm(rhs))
          case _ => unsupported(expr)
        }

        case Remainder(lhs, rhs) => lhs.getType match {
          case BVType(true, _) => Mod.bvsrem(parseTerm(lhs), parseTerm(rhs))
          case BVType(false, _) => Mod.bvurem(parseTerm(lhs), parseTerm(rhs))
          // the remainder of the euclidean division
          case IntegerType() => p.mulTheory.eMod(parseTerm(lhs), parseTerm(rhs))
        }

        case Modulo(lhs, rhs) => lhs.getType match {
          case BVType(true, _) => Mod.bvsmod(parseTerm(lhs), parseTerm(rhs))
          case BVType(false, _) => Mod.bvurem(parseTerm(lhs), parseTerm(rhs))
          case IntegerType() => p.mulTheory.eMod(parseTerm(lhs), parseTerm(rhs))
        }

        // BITVECTOR OPERATIONS
        case BVNot(e) =>
          Mod.bvnot(parseTerm(e))

        case BVAnd(lhs, rhs) =>
          Mod.bvand(parseTerm(lhs), parseTerm(rhs))

        case BVOr(lhs, rhs) =>
          Mod.bvor(parseTerm(lhs), parseTerm(rhs))

        case BVXor(lhs, rhs) =>
          Mod.bvxor(parseTerm(lhs), parseTerm(rhs))

        case BVShiftLeft(lhs, rhs) =>
          Mod.bvshl(parseTerm(lhs), parseTerm(rhs))

        case BVAShiftRight(lhs, rhs) =>
          Mod.bvashr(parseTerm(lhs), parseTerm(rhs))

        case BVLShiftRight(lhs, rhs) =>
          Mod.bvlshr(parseTerm(lhs), parseTerm(rhs))

        case c @ BVWideningCast(e, _) =>
          val Some((from, to)) = c.cast: @unchecked
          val BVType(signed, _) = e.getType: @unchecked
          if (signed) Mod.sign_extend(to - from, parseTerm(e))
          else Mod.zero_extend(to - from, parseTerm(e))

        case c @ BVNarrowingCast(e, _) =>
          val Some((from, to)) = c.cast: @unchecked
          Mod.extract(to - 1, 0, parseTerm(e))

        case BVUnsignedToSigned(e) =>
          parseTerm(e)

        case BVSignedToUnsigned(e) =>
          parseTerm(e)

        case BVToInt(e) => e.getType match {
          case BVType(true, size) => Mod.cast2Int(Mod.cast2SignedBV(size, parseTerm(e)))
          case BVType(false, _) => Mod.cast2Int(parseTerm(e))
        }

        case IntToBV(size, signed, e) =>
          if (signed) Mod.cast2SignedBV(size, parseTerm(e))
          else Mod.cast2UnsignedBV(size, parseTerm(e))

        case _ => unsupported(expr, "Unexpected formula " + expr)
      }
      expr.getType match {
        case BVType(true, bits) => Mod.cast2UnsignedBV(bits, res)
        case _ => res
      }
    }

    // Tries to convert Inox Expression to Princess IFormula
    def apply(expr: Expr)(using bindings: Map[Variable, IExpression]): IExpression =
      expr.getType match {
        case BooleanType() => parseFormula(expr)
        case _ => parseTerm(expr)
      }
  }

  // The uninterpreted functions of the closures of models, by function value (see `uniquateClosure`)
  private val closureIds: MutableMap[(BigInt, FunctionType), Identifier] = MutableMap.empty

  object princessToInox {
    protected class Context(
      val model: Model,
      val seen: Set[BigInt] = Set.empty,
      // the uninterpreted constants that stand for the functions that are being extracted
      private[AbstractPrincessSolver] val interpretations: MutableMap[BigInt, UninterpretedCall] = MutableMap.empty,
      private[AbstractPrincessSolver] val lambdas: MutableMap[BigInt, Lambda] = MutableMap.empty,
      private[AbstractPrincessSolver] val closures: MutableMap[Identifier, Lambda] = MutableMap.empty
    ) {
      def withSeen(n: BigInt): Context = new Context(model, seen + n, interpretations, lambdas, closures)
    }

    // For some reason, various trees are not evaluated in the resulting Princess model,
    // so we traverse the term and replace all such trees with ground sub-trees by the
    // appropriate simplified value
    private[princess] def simplify(iexpr: IExpression)(model: Model): IExpression = {
      val visitor = new CollectingVisitor[Unit, IExpression] {
        def postVisit(t: IExpression, arg: Unit, subres: Seq[IExpression]) : IExpression =
          IExpression.updateAndSimplify(t, subres) match {
            case app @ IFunApp(fun, Seq(arg)) if selectors `containsB` fun =>
              evalToTerm(arg)(model) match {
                case Some(IFunApp(_, args)) => args(selectors.toA(fun)._2)
                case _ => app
              }
            // The model interprets applications in terms of the integer representations of
            // functions, which it doesn't use when evaluating function-typed terms
            case IFunApp(fun, args) if lambdas `containsB` fun =>
              val ft = lambdas.toA(fun)
              IFunApp(fun, (args zip (ft +: ft.from)).map {
                case (arg, argType: FunctionType) =>
                  functionIndex(arg, argType)(model).map(IIntLit(_)).getOrElse(arg)
                case (arg, _) => arg
              })
            case e => e
          }
      }

      visitor.visit(iexpr, ())
    }

    /* Obtains the internal integer representation of the function `iterm` in two manners.
     * The first is to simply call model.eval on iterm. If it succeeds, we obtain the integer
     * representation of the function. Otherwise, it could happen that iterm evaluates to some
     * constant, in which case the representation of the function can be retrieved by traversing
     * the `individuals` fields of the InfUninterpretedSort of the constant in question. */
    private def functionIndex(iterm: ITerm, ft: FunctionType)(model: Model): Option[IdealInt] =
      model.eval(iterm).orElse(model.evalExpression(iterm) match {
        case Some(ct: IConstant) =>
          typeToSort(ft) match {
            case sort: UninterpretedSortTheory.InfUninterpretedSort =>
              // Constants are numbered, it suffices to apply the reverse operation done in
              // InfUninterpretedSort#decodeToTerm.
              val idx = IdealInt(ct.c.name.substring(ct.c.name.lastIndexOf('!') + 1))
              if (idx % 2 == IdealInt(0)) Some(idx / 2)
              else Some(-(idx + 1) / 2)
            case _ => None // Should not happen, but if it does, we simply return None
          }
        case _ => None
      })

    private def evalToTerm(iexpr: IExpression)(model: Model): Option[IExpression] = iexpr match {
      case app @ IFunApp(_, _) => Some(app)
      case it: ITerm => model.evalToTerm(it)
      case _ => None
    }

    def parseExpr(iexpr: IExpression, tpe: Type)(using ctx: Context): Option[Expr] = {

      def rec(iexpr: IExpression, tpe: Type)(using ctx: Context): Option[Expr] = tpe match {
        case BooleanType() => iexpr match {
          case iterm: ITerm => ctx.model.eval(iterm).map(i => BooleanLiteral(i.intValue == 0))
          case iformula: IFormula => ctx.model.eval(iformula).map(BooleanLiteral.apply)
        }

        case IntegerType() =>
          ctx.model.eval(iexpr.asInstanceOf[ITerm]).map(i => IntegerLiteral(i.bigIntValue))

        case BVType(signed, size) => evalToTerm(iexpr)(ctx.model).collect {
          case IFunApp(Mod.mod_cast, Seq(_, _, IIntLit(i))) => BVLiteral(signed, i.bigIntValue, size)
          case IIntLit(i) => BVLiteral(signed, i.bigIntValue, size)
        }

        case CharType() => evalToTerm(iexpr)(ctx.model).collect {
          case IFunApp(Mod.mod_cast, Seq(_, _, IIntLit(i))) => CharLiteral(i.intValue.toChar)
          case IIntLit(i) => CharLiteral(i.intValue.toChar)
        }

        case tpe @ ((_: ADTType) | (_: TupleType) | (_: TypeParameter) | UnitType()) =>
          evalToTerm(iexpr)(ctx.model).collect { case IFunApp(fun, args) if constructors `containsB` fun =>
            val (fieldsTypes: Seq[Type], recons: (Seq[Expr] => Expr)) = constructors.toA(fun) match {
              case ADTCons(id, tps) => (getConstructor(id, tps).fields.map(_.getType), ADT(id, tps, _))
              case TupleCons(tps) => (tps, Tuple(_))
              case TypeParameterCons(tp) => (Seq(IntegerType()), (es: Seq[Expr]) => {
                GenericValue(tp, es.head.asInstanceOf[IntegerLiteral].value.toInt)
              })
              case UnitCons => (Seq(), (_: Seq[Expr]) => UnitLiteral())
            }

            val optArgs = (args zip fieldsTypes).map { case (arg, tpe) => rec(arg, tpe) }

            if (optArgs.forall(_.isDefined)) {
              Some(recons(optArgs.map(_.get)))
            } else {
              None
            }
          }.flatten.orElse {
            ctx.model.eval(iexpr.asInstanceOf[ITerm]).map(n => constructExpr(n.intValue, tpe))
          }

        case ft: FunctionType =>
          val iterm = iexpr.asInstanceOf[ITerm]
          functionIndex(iterm, ft)(ctx.model).map { ideal =>
            val n = BigInt(ideal.bigIntValue)
            if (ctx.seen(n)) {
              ctx.interpretations.getOrElse(n, {
                val res = UninterpretedCall(FreshIdentifier("x", true), Seq.empty, Seq.empty, FunctionType(Seq.empty, ft))
                ctx.interpretations(n) = res
                res
              })
            } else {
              ctx.lambdas.getOrElse(n, {
                val newCtx = ctx.withSeen(n)
                val params = ft.from.map(tpe => ValDef.fresh("x", tpe, true))
                val lambda = (lambdas.getB(ft)
                  .flatMap { fun =>
                    val interps = ctx.model.interpretation.flatMap {
                      case (IFunApp(`fun`, ptr +: args), res: IIntLit) =>
                        if (ctx.model.eval(ptr === IIntLit(ideal) | iterm === ptr) contains true) {
                          val optArgs = (args zip ft.from).map(p => rec(p._1, p._2)(using newCtx))
                          val optRes = rec(res, ft.to)(using newCtx)

                          if (optArgs.forall(_.isDefined) && optRes.isDefined) {
                            Some(optArgs.map(_.get) -> optRes.get)
                          } else {
                            None
                          }
                        } else {
                          None
                        }

                      case _ => None
                    }.toSeq.sortBy(_.toString)

                    if (interps.nonEmpty) Some(interps) else None
                  }.map { interps =>
                    Lambda(params, interps.foldRight(interps.head._2) { case ((args, res), elze) =>
                      IfExpr(andJoin((params zip args).map(p => Equals(p._1.toVariable, p._2))), res, elze)
                    })
                  }.getOrElse(try {
                    simplestValue(ft, allowSolver = false).asInstanceOf[Lambda]
                  } catch {
                    case _: NoSimpleValue =>
                      Lambda(params, exprOps.freshUninterpretedCall("default", params, ft.to))
                  }))
                  val id = closureIds.getOrElseUpdate(n -> ft, FreshIdentifier("f", true))
                  val res = uniquateClosure(id, lambda)
                  ctx.closures(id) = lambda
                  ctx.lambdas(n) = res
                  res
              })
            }
          }
      }

      rec(simplify(iexpr)(ctx.model), tpe)
    }

    def asGround(iexpr: IExpression, tpe: Type): Option[Expr] = {
      case class UnsoundException(iexpr: IExpression, msg: String)
        extends Exception("Can't extract " + iexpr + " : " + msg)

      def rec(iexpr: IExpression, tpe: Type): Expr = (iexpr, tpe) match {
        case _ if variables `containsB` iexpr => variables.toA(iexpr)
        case (Conj(a, b), BooleanType()) => And(rec(a, BooleanType()), rec(b, BooleanType()))
        case (Disj(a, b), BooleanType()) => Or(rec(a, BooleanType()), rec(b, BooleanType()))
        case (IBoolLit(b), _) => BooleanLiteral(b)
        case (IIntLit(i), BooleanType()) => BooleanLiteral(i.intValue == 0)
        case (IIntLit(i), IntegerType()) => IntegerLiteral(i.bigIntValue)
        case (IFunApp(fun, args), _) if functions `containsB` fun =>
          val tfd = functions.toA(fun)
          FunctionInvocation(tfd.id, tfd.tps, (args zip tfd.params).map(p => rec(p._1, p._2.getType)))
        case (IFunApp(fun, args), _) if lambdas `containsB` fun =>
          val ft @ FunctionType(from, _) = lambdas.toA(fun)
          Application(rec(args.head, ft), (args.tail zip from).map(p => rec(p._1, p._2)))
        case (IFunApp(fun, args), _) if constructors `containsB` fun => constructors.toA(fun) match {
          case ADTCons(id, tps) =>
            ADT(id, tps, (args zip getConstructor(id, tps).fields).map(p => rec(p._1, p._2.getType)))
          case TupleCons(tps) =>
            Tuple((args zip tps).map(p => rec(p._1, p._2)))
          case UnitCons =>
            UnitLiteral()
          case _ => throw UnsoundException(iexpr, "Unexpected constructor")
        }
        case (IFunApp(fun, Seq(arg)), _) if selectors `containsB` fun => selectors.toA(fun) match {
          case (ac @ ADTCons(id, tps), i) =>
            ADTSelector(rec(arg, ac.getType), getConstructor(id).fields(i).id)
          case (tc @ TupleCons(tps), i) =>
            TupleSelect(rec(arg, tc.getType), i + 1)
          case _ => throw UnsoundException(iexpr, "Unexpected selector")
        }
        case (ITermITE(c, t, e), _) => IfExpr(rec(c, BooleanType()), rec(t, tpe), rec(e, tpe))
        case _ => throw UnsoundException(iexpr, "Unexpected tree")
      }

      try {
        Some(rec(iexpr, tpe))
      } catch {
        case _: UnsoundException => None
      }
    }

    def apply(iexpr: IExpression, tpe: Type)(using model: Model) = {
      val ctx = new Context(model)
      val res = parseExpr(iexpr, tpe)(using ctx)
      (res, ctx.interpretations.map { case (n, c) => c.id -> (Lambda(Seq.empty, ctx.lambdas(n)): Expr) } ++ ctx.closures)
    }
  }

  def declareVariable(v: Variable): IExpression = variables.cachedB(v)(freshSymbol(v))

  def freshSymbol(v: Variable): IExpression = v.getType match {
    case BooleanType() => declared(p.createBooleanVariable(v.id.freshen.uniqueName))(p.addBooleanVariable(_))
    case tpe => declared(p.createConstant(v.id.freshen.uniqueName, typeToSort(tpe)))(p.addConstant(_))
  }

  def assertCnstr(formula: Trees): Unit = p !! formula.asInstanceOf[IFormula]

  // we interrupt asynchronously in portfolio mode, so this should be handled in a thread-safe manner.
  // The interruption is only cleared by `reset`: an interrupt that arrives between two checks
  // (e.g. while the unrolling solver unrolls) must still stop the following ones.
  private val interruptCheckSat = new java.util.concurrent.atomic.AtomicBoolean(false)

  private def internalCheck(config: Configuration): config.Response[Model, Assumptions] = {
    import SimpleAPI.ProverStatus

    if (interruptCheckSat.get) return config.cast(Unknown)

    p checkSat false

    while ((p getStatus 50) == ProverStatus.Running) {
      if (interruptCheckSat.get) p stop true
    }

    config.cast(p.getStatus(true) match {
      // FIXME @nv: for now, we treat Inconclusive as Sat, but this should
      //            be changed once Princess ensures soundness of models with ADTs
      case ProverStatus.Sat | ProverStatus.Inconclusive =>
        if (config.withModel) {
          SatWithModel(p.partialModel)
        } else {
          Sat
        }

      case ProverStatus.Unsat =>
        if (config.withUnsatAssumptions) {
          UnsatWithAssumptions(Set.empty)
        } else {
          Unsat
        }

      case ProverStatus.Unknown =>
        Unknown

      case r => throw new PrincessSolverException("Unexpected solver response: " + r)
    })
  }

  def check(config: CheckConfiguration): config.Response[Model, Assumptions] = internalCheck(config)

  // We use push/pop to simulate checking with assumptions
  def checkAssumptions(config: Configuration)(assumptions: Set[Trees]): config.Response[Model, Assumptions] = {
    push()
    for (a <- assumptions) assertCnstr(a)
    val res = internalCheck(config)
    pop()
    res
  }

  override def free() = {
    p.shutDown
  }

  // Princess forgets the symbols declared in a scope when the scope is popped, but the
  // unrolling templates are encoded once and reused across pops. The symbols therefore stay
  // in the maps above and are declared again after each pop of the scope that declared them.
  private var scopes: List[ListBuffer[() => Unit]] = Nil

  private def declared[T](symbol: T)(redeclare: T => Unit): T = {
    for (scope <- scopes.headOption) scope += (() => redeclare(symbol))
    symbol
  }

  override def pop() = {
    val popped = scopes.head
    scopes = scopes.tail
    p.pop()
    for (redeclare <- popped) redeclare()
    for (scope <- scopes.headOption) scope ++= popped
  }

  override def push() = {
    scopes = ListBuffer.empty[() => Unit] :: scopes
    p.push()
  }

  override def reset() = {
    adtManager.reset()
    variables.clear()
    functions.clear()
    lambdas.clear()

    constructors.clear()
    selectors.clear()
    testers.clear()

    sorts.clear()

    scopes = Nil
    p.reset
    interruptCheckSat.set(false)
  }

  def interrupt() = interruptCheckSat.set(true)
}
