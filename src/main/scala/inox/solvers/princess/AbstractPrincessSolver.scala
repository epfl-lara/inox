/* Copyright 2009-2016 EPFL, Lausanne */

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
import ap.parser._
import ap.theories.{ADT => PADT, _}

import utils._
import SolverResponses._

import scala.collection.mutable.{Map => MutableMap}

trait AbstractPrincessSolver extends AbstractSolver with ADTManagers {
  import scala.language.postfixOps
  import IExpression._

  case class PrincessSolverException(msg: String)
      extends Exception("handle PrincessSolver: " + msg)

  import context._
  import program._
  import program.trees._
  import program.symbols._

  protected implicit val semantics: program.Semantics

  val name = "Princess"

  interruptManager.registerForInterrupts(this)

  type Trees = IExpression
  type Model = SimpleAPI.PartialModel

  private val enableAssertions = reporter.isDebugEnabled

  ap.util.Debug enableAllAssertions enableAssertions
  protected[princess] val p = SimpleAPI(
    enableAssert = enableAssertions,
    dumpScala = enableAssertions,
    scalaDumpBasename = options.findOptionOrDefault(Main.optFiles).headOption.map(_.getName).getOrElse("NA") + "-",
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
  private[princess] val sorts = new IncrementalMap[Type, (PADT, Seq[(Type, DataType)])]

  private[princess] val adtManager = new ADTManager

  def typeToSort(tpe: Type): (PADT, Seq[(Type, DataType)]) = {
    val realType = bestRealType(tpe)
    adtManager.declareADTs(realType, (adts: Seq[(Type, DataType)]) => {
      val indexMap: Map[Type, Int] = adts.map(_._1).zipWithIndex.toMap

      def typeToSortRef(tt: Type): PADT.Sort = {
        val tpe = tt match {
          case adt: ADTType => adt.getADT.root.toType
          case _ => tt
        }

        if (indexMap contains tpe) {
          PADT.ADTSort(indexMap(tpe))
        } else {
          PADT.IntSort
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

      for ((tpe, _) <- adts) sorts += tpe -> ((adt, adts))
    })

    sorts(realType)
  }

  object inoxToPrincess {

    def parseFormula(expr: Expr)(implicit bindings: Map[Variable, IExpression]): IFormula = expr match {
      case BooleanLiteral(value) =>
        value

      case v: Variable =>
        bindings.getOrElse(v, declareVariable(v)).asInstanceOf[IFormula]

      case Let(vd, e, b) =>
        parseFormula(b)(bindings + (vd.toVariable -> (vd.tpe match {
          case BooleanType => parseFormula(e)
          case _ => parseTerm(e)
        })))

      // BOOLEAN CONNECTIVES
      case Not(expr) =>
        !parseFormula(expr)

      case And(exprs) =>
        val subExprs = for (e <- exprs) yield parseFormula(e)
        (subExprs.head /: subExprs.tail)((p, q) => p & q)

      case Or(exprs) => {
        val subExprs = for (e <- exprs) yield parseFormula(e)
        (subExprs.head /: subExprs.tail)((p, q) => p | q)
      }

      case Implies(lhs, rhs) => {
        val pLhs = parseFormula(lhs)
        val pRhs = parseFormula(rhs)
        pLhs ==> pRhs
      }

      // EQUALITY
      case Equals(lhs, rhs) => lhs.getType match {
        case BooleanType => parseFormula(lhs) <=> parseFormula(rhs)
        case _ => parseTerm(lhs) === parseTerm(rhs)
      }

      // INTEGER COMPARISON
      case LessThan(lhs, rhs) => {
        val pLhs = parseTerm(lhs)
        val pRhs = parseTerm(rhs)
        pLhs < pRhs
      }

      case GreaterThan(lhs, rhs) => {
        val pLhs = parseTerm(lhs)
        val pRhs = parseTerm(rhs)
        pLhs > pRhs
      }

      case LessEquals(lhs, rhs) => {
        val pLhs = parseTerm(lhs)
        val pRhs = parseTerm(rhs)
        pLhs <= pRhs
      }

      case GreaterEquals(lhs, rhs) => {
        val pLhs = parseTerm(lhs)
        val pRhs = parseTerm(rhs)
        pLhs >= pRhs
      }

      // ADT INSTANCE OF
      case IsInstanceOf(expr, ADTType(id, tps)) =>
        val tpe = ADTType(id, tps.map(bestRealType))
        val root = tpe.getADT.root

        if (root.toType == tpe) {
          true
        } else {
          val (sort, adts) = typeToSort(tpe)
          val constructors = adts.flatMap(_._2.cases)
          sort.hasCtor(parseTerm(expr), constructors.indexWhere(_.tpe == tpe))
        }

      case (_: FunctionInvocation) | (_: Application) | (_: ADTSelector) | (_: TupleSelect) =>
        parseTerm(expr) === 0

      case IfExpr(cond, thenn, elze) =>
        IFormulaITE(parseFormula(cond), parseFormula(thenn), parseFormula(elze))

      case _ => unsupported(expr, "Unexpected formula " + expr)
    }

    def parseTerm(expr: Expr)(implicit bindings: Map[Variable, IExpression]): ITerm = expr match {
      case FunctionInvocation(id, tps, args) =>
        val f = functions.cachedB(getFunction(id, tps)) {
          p.createFunction(id.uniqueName, args.size)
        }
        val pArgs = for (a <- args) yield parseTerm(a)
        IFunApp(f, pArgs)

      case Application(caller, args) =>
        val realType = bestRealType(caller.getType).asInstanceOf[FunctionType]
        val f = lambdas.cachedB(realType) {
          p.createFunction(FreshIdentifier("dynLambda").uniqueName, args.size + 1)
        }
        val pArgs = for (a <- caller +: args) yield parseTerm(a)
        IFunApp(f, pArgs)

      // ADT | Tuple
      case (_: ADT) | (_: Tuple) | (_: GenericValue) | (_: UnitLiteral) =>
        val tpe = bestRealParameters(expr.getType)
        val args = expr match {
          case ADT(_, args) => args
          case Tuple(args) => args
          case GenericValue(_, i) => Seq(IntegerLiteral(i))
          case UnitLiteral() => Seq.empty
        }
        val (sort, adts) = typeToSort(tpe)
        val constructors = adts.flatMap(_._2.cases)
        val constructor = (constructors zip sort.constructors).collectFirst {
          case (cons, fun) if cons.tpe == tpe => fun
        }.getOrElse(throw PrincessSolverException(s"Undefined constructor for $tpe!?"))
        constructor(args.map(parseTerm) : _*)

      case (_: ADTSelector) | (_: TupleSelect) =>
        val (rec, i) = expr match {
          case s @ ADTSelector(adt, _) => (adt, s.selectorIndex)
          case TupleSelect(tpl, i) => (tpl, i - 1)
        }

        val tpe = bestRealParameters(rec.getType)
        val (sort, adts) = typeToSort(tpe)
        val constructors = adts.flatMap(_._2.cases)
        val selector = (constructors zip sort.selectors).collectFirst {
          case (cons, sels) if cons.tpe == tpe => sels(i)
        }.getOrElse(throw PrincessSolverException(s"Undefined selector for $expr!?"))
        selector(parseTerm(rec))

      // I think we can ignore this since we do not type our variables
      case AsInstanceOf(expr, tpe) =>
        parseTerm(expr)

      case BooleanLiteral(true) => i(0)
      case BooleanLiteral(false) => i(1)

      // @nv: this MUST come at least after having dealt with FunctionInvocation,
      //      Application and ADTSelectors which can return booleans
      case IsTyped(_, BooleanType) =>
        ITermITE(parseFormula(expr), i(0), i(1))

      case v: Variable =>
        bindings.getOrElse(v, declareVariable(v)).asInstanceOf[ITerm]

      case Let(vd, e, b) =>
        parseTerm(b)(bindings + (vd.toVariable -> (vd.tpe match {
          case BooleanType => parseFormula(e)
          case _ => parseTerm(e)
        })))

      case IfExpr(cond, thenn, elze) =>
        ITermITE(parseFormula(cond), parseTerm(thenn), parseTerm(elze))

      // LITERALS
      case IntegerLiteral(value) => value.toInt

      // INTEGER ARITHMETIC
      case Plus(lhs, rhs) => {
        val pLhs = parseTerm(lhs)
        val pRhs = parseTerm(rhs)
        pLhs + pRhs
      }

      case Minus(lhs, rhs) => {
        val pLhs = parseTerm(lhs)
        val pRhs = parseTerm(rhs)
        pLhs - pRhs
      }

      case Times(lhs, rhs) => {
        val pLhs = parseTerm(lhs)
        val pRhs = parseTerm(rhs)
        p.mult(pLhs, pRhs)
      }

      case UMinus(e) =>
        - parseTerm(e)

      case Division(lhs, rhs) =>
        p.mulTheory.tDiv(parseTerm(lhs), parseTerm(rhs))

      case Remainder(lhs, rhs) =>
        val q = parseTerm(Division(lhs, rhs))
        parseTerm(lhs) - (parseTerm(rhs) * q)

      case Modulo(lhs, rhs) =>
        p.mulTheory.eMod(parseTerm(lhs), parseTerm(rhs))

      case _ => unsupported(expr, "Unexpected formula " + expr)
    }

    // Tries to convert Inox Expression to Princess IFormula
    def apply(expr: Expr)(implicit bindings: Map[Variable, IExpression]): IExpression =
      expr.getType match {
        case BooleanType => parseFormula(expr)
        case _ => parseTerm(expr)
      }
  }

  object princessToInox {
    protected class Context(
      val model: Model,
      val seen: Set[BigInt] = Set.empty,
      private[AbstractPrincessSolver] val chooses: MutableMap[BigInt, Choose] = MutableMap.empty,
      private[AbstractPrincessSolver] val lambdas: MutableMap[BigInt, Lambda] = MutableMap.empty
    ) {
      def withSeen(n: BigInt): Context = new Context(model, seen + n, chooses, lambdas)
    }

    def parseExpr(iexpr: IExpression, tpe: Type)(implicit ctx: Context): Option[Expr] = tpe match {
      case BooleanType => iexpr match {
        case iterm: ITerm => ctx.model.eval(iterm).map(i => BooleanLiteral(i.intValue == 0))
        case iformula: IFormula => ctx.model.eval(iformula).map(BooleanLiteral)
      }

      case IntegerType =>
        ctx.model.eval(iexpr.asInstanceOf[ITerm]).map(i => IntegerLiteral(i.bigIntValue))

      case t @ ((_: ADTType) | (_: TupleType) | (_: TypeParameter) | UnitType) =>
        val tpe = bestRealType(t)
        val (sort, adts) = typeToSort(tpe)

        val optIndex = (adts.map(_._1) zip sort.ctorIds).collectFirst {
          case (`tpe`, fun) => ctx.model.eval(fun(iexpr.asInstanceOf[ITerm])).map(_.intValue)
        }.flatten

        optIndex.flatMap { index =>
          val constructors = adts.flatMap(_._2.cases)
          val (fieldsTypes, recons): (Seq[Type], Seq[Expr] => Expr) = constructors(index).tpe match {
            case adt: ADTType => (adt.getADT.toConstructor.fieldsTypes, ADT(adt, _))
            case TupleType(tps) => (tps, Tuple(_))
            case tp: TypeParameter => (Seq(IntegerType), (es: Seq[Expr]) => {
              GenericValue(tp, es.head.asInstanceOf[IntegerLiteral].value.toInt)
            })
            case UnitType => (Seq(), _ => UnitLiteral())
          }

          val optArgs = (sort.selectors(index) zip fieldsTypes).map {
            case (fun, tpe) => parseExpr(fun(iexpr.asInstanceOf[ITerm]), tpe)
          }

          if (optArgs.forall(_.isDefined)) {
            Some(recons(optArgs.map(_.get)))
          } else {
            None
          }
        }.orElse {
          ctx.model.eval(iexpr.asInstanceOf[ITerm]).map(n => constructExpr(n.intValue, tpe))
        }

      case ft: FunctionType =>
        val tpe @ FirstOrderFunctionType(from, to) = bestRealType(ft)
        val iterm = iexpr.asInstanceOf[ITerm]
        ctx.model.eval(iterm).flatMap { ideal =>
          val n = BigInt(ideal.bigIntValue)
          if (ctx.seen(n)) {
            Some(ctx.chooses.getOrElseUpdate(n, {
              Choose(Variable.fresh("x", ft, true).toVal, BooleanLiteral(true))
            }))
          } else {
            ctx.lambdas.get(n).orElse {
              for {
                fun <- lambdas.getB(tpe)
                newCtx = ctx.withSeen(n)
                interps = ctx.model.interpretation.flatMap {
                  case (SimpleAPI.IntFunctionLoc(`fun`, ptr +: args), SimpleAPI.IntValue(res)) =>
                    if (ctx.model.eval(iterm === ptr) contains true) {
                      val optArgs = (args zip from).map(p => parseExpr(p._1, p._2)(newCtx))
                      val optRes = parseExpr(res, to)(newCtx)

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
              } yield {
                val params = from.map(tpe => ValDef(FreshIdentifier("x", true), tpe))
                uniquateClosure(n.intValue, if (interps.isEmpty) {
                  try {
                    simplestValue(tpe, allowSolver = false).asInstanceOf[Lambda]
                  } catch {
                    case _: NoSimpleValue =>
                      mkLambda(params, Choose(ValDef(FreshIdentifier("res"), to), BooleanLiteral(true)), tpe)
                  }
                } else {
                  val body = interps.foldRight(interps.head._2) { case ((args, res), elze) =>
                    IfExpr(andJoin((params zip args).map(p => Equals(p._1.toVariable, p._2))), res, elze)
                  }
                  mkLambda(params, body, tpe)
                })
              }
            }
          }
        }
    }

    def apply(iexpr: IExpression, tpe: Type)(implicit model: Model) = {
      val ctx = new Context(model)
      val res = parseExpr(iexpr, tpe)(ctx)
      (res, ctx.chooses.map { case (n, c) => c -> ctx.lambdas(n) })
    }
  }

  def declareVariable(v: Variable): IExpression = variables.cachedB(v)(freshSymbol(v))

  def freshSymbol(v: Variable): IExpression = v.tpe match {
    case BooleanType => p.createBooleanVariable(v.id.freshen.uniqueName)
    case _ => p.createConstant(v.id.freshen.uniqueName)
  }

  def assertCnstr(formula: Trees): Unit = p !! formula.asInstanceOf[IFormula]

  private[this] var interruptCheckSat = false

  private def internalCheck(config: Configuration): config.Response[Model, Assumptions] = {
    import SimpleAPI.ProverStatus

    interruptCheckSat = false

    p checkSat false

    while ((p getStatus 50) == ProverStatus.Running) {
      if (interruptCheckSat) p stop true
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

  override def pop() = {
    adtManager.pop()
    variables.pop()
    functions.pop()
    lambdas.pop()
    sorts.pop()

    p.pop
  }

  override def push() = {
    adtManager.push()
    variables.push()
    functions.push()
    lambdas.push()
    sorts.push()

    p.push
  }

  override def reset() = {
    adtManager.reset()
    variables.clear()
    functions.clear()
    lambdas.clear()
    sorts.clear()

    p.reset
  }

  def interrupt() = interruptCheckSat = true
}
