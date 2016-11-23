
package inox
package solvers

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

trait AbstractPrincessSolver extends AbstractSolver with ADTManagers {
  import scala.language.postfixOps
  import IExpression._

  case class PrincessSolverException(msg: String)
      extends Exception("handle PrincessSolver: " + msg)

  import program._
  import program.trees._
  import program.symbols._

  val name = "Princess"

  ctx.interruptManager.registerForInterrupts(this)

  type Trees = IExpression
  type Model = SimpleAPI.PartialModel

  protected val p = SimpleAPI.spawnWithAssertions

  // Internal maps storing created Constant, Variables, ADT and Function symbols
  protected val variables = new IncrementalBijection[Variable, IExpression]
  protected val functions = new IncrementalBijection[TypedFunDef, IFunction]
  protected val lambdas = new IncrementalBijection[FunctionType, IFunction]
  protected val sorts = new IncrementalMap[Type, (PADT, Seq[(Type, DataType)])]

  protected val adtManager = new ADTManager

  def typeToSort(tpe: ADTType): (PADT, Seq[(Type, DataType)]) = {
    val realType = bestRealType(tpe).asInstanceOf[ADTType]
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

    sorts(realType.getADT.root.toType)
  }

  object inoxToPrincess {

    def parseFormula(expr: Expr)(implicit bindings: Map[Variable, IExpression]): IFormula = expr match {
      case BooleanLiteral(value) =>
        value

      case v: Variable =>
        bindings.getOrElse(v, declareVariable(v)).asInstanceOf[IFormula]

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

      case (_: FunctionInvocation) | (_: Application) | (_: ADTSelector) =>
        parseTerm(expr) === 0

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

      // ADT
      case ADT(ADTType(id, tps), args) =>
        val tpe = ADTType(id, tps.map(bestRealType))
        val (sort, adts) = typeToSort(tpe)
        val constructors = adts.flatMap(_._2.cases)
        val constructor = (constructors zip sort.constructors).collectFirst {
          case (cons, fun) if cons.tpe == tpe => fun
        }.getOrElse(throw PrincessSolverException(s"Undefined constructor for $tpe!?"))
        constructor(args.map(parseTerm) : _*)

      case s @ ADTSelector(IsTyped(adt, ADTType(id, tps)), _) =>
        val tpe = ADTType(id, tps.map(bestRealType))
        val (sort, adts) = typeToSort(tpe)
        val constructors = adts.flatMap(_._2.cases)
        val selector = (constructors zip sort.selectors).collectFirst {
          case (cons, sels) if cons.tpe == tpe => sels(s.selectorIndex)
        }.getOrElse(throw PrincessSolverException(s"Undefined selector for $s!?"))
        selector(parseTerm(adt))

      // I think we can ignore this since we do not type our variables
      case AsInstanceOf(expr, tpe) =>
        parseTerm(expr)

      // @nv: this MUST come at least after having dealt with FunctionInvocation,
      //      Application and ADTSelectors which can return booleans
      case IsTyped(_, BooleanType) =>
        ITermITE(parseFormula(expr), i(0), i(1))

      case v: Variable =>
        bindings.getOrElse(v, declareVariable(v)).asInstanceOf[ITerm]

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
        pLhs * pRhs
      }

      // TODO: We should support these
      case Division(lhs, rhs) => {
        val pLhs = parseTerm(lhs)
        val pRhs = parseTerm(rhs)
        throw new PrincessSolverException("DIVISION")
      }

      case Remainder(lhs, rhs) => {
        val pLhs = parseTerm(lhs)
        val pRhs = parseTerm(rhs)
        throw new PrincessSolverException("REMAINDER")
      }

      case Modulo(lhs, rhs) => {
        val pLhs = parseTerm(lhs)
        val pRhs = parseTerm(rhs)
        throw new PrincessSolverException("MODULO")
      }

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
    def parseExpr(iexpr: IExpression, tpe: Type)(implicit model: Model): Option[Expr] = tpe match {
      case BooleanType =>
        model.eval(iexpr.asInstanceOf[IFormula]).map(BooleanLiteral)

      case IntegerType =>
        model.eval(iexpr.asInstanceOf[ITerm]).map(i => IntegerLiteral(i.bigIntValue))

      case adt: ADTType =>
        val tpe = bestRealType(adt).asInstanceOf[ADTType]
        val (sort, adts) = typeToSort(tpe)

        val optIndex = (adts.map(_._1) zip sort.ctorIds).collectFirst {
          case (`tpe`, fun) => model.eval(fun(iexpr.asInstanceOf[ITerm])).map(_.intValue)
        }.flatten

        optIndex.flatMap { index =>
          val constructors = adts.flatMap(_._2.cases)
          val consType = constructors(index).tpe.asInstanceOf[ADTType]

          val optArgs = (consType.getADT.toConstructor.fields zip sort.selectors(index)).map {
            case (vd, fun) => parseExpr(fun(iexpr.asInstanceOf[ITerm]), vd.tpe)
          }

          if (optArgs.forall(_.isDefined)) {
            Some(ADT(consType, optArgs.map(_.get)))
          } else {
            None
          }
        }
    }

    def apply(iexpr: IExpression, tpe: Type)(implicit model: Model) = parseExpr(iexpr, tpe)
  }

  def declareVariable(v: Variable): IExpression = variables.cachedB(v)(freshSymbol(v))

  def freshSymbol(v: Variable): IExpression = v.tpe match {
    case BooleanType => p.createBooleanVariable(v.id.uniqueName)
    case _ => p.createConstant(v.id.uniqueName)
  }

  def assertCnstr(formula: Trees): Unit = p !! formula.asInstanceOf[IFormula]

  private def internalCheck(config: Configuration): config.Response[Model, Assumptions] = {
    import SimpleAPI.ProverStatus

    config.cast(p.??? match {
      case ProverStatus.Sat =>
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

      case ProverStatus.Inconclusive | ProverStatus.Unknown =>
        Unknown

      case r => throw new PrincessSolverException("Unexpected solver response: " + r)
    })
  }

  def check(config: CheckConfiguration): config.Response[Model, Assumptions] = internalCheck(config)

  // We use push/pop to simulate checking with assumptions
  def checkAssumptions(config: Configuration)(assumptions: Set[Trees]): config.Response[Model, Assumptions] = {
    p.push
    for (a <- assumptions) assertCnstr(a)
    val res = internalCheck(config)
    p.pop
    res
  }

  def extractModel(model: Model): Map[ValDef, Expr] = variables.aToB.flatMap {
    case (v, iexpr) => princessToInox(iexpr, v.tpe)(model).map(v.toVal -> _)
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

  override def interrupt() = p.stop
  override def recoverInterrupt() = ()
}
