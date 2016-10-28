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
import scala.collection.mutable.{Map => MMap}

import SolverResponses._
import inox.ast.Identifier

trait PrincessSolver extends Solver {
  import scala.language.postfixOps
  import IExpression._

  case class PrincessSolverException(msg : String)
      extends Exception("handle PrincessSolver: " + msg)

  import PrincessSolver.this.program.trees._

  def name = "Princess"

  val p = SimpleAPI.spawnWithAssertions

  // Internal maps storing created Constant, Variables, ADT and Function symbols
  val integerMap : MMap[Identifier, (ITerm, ValDef)] = MMap()
  val booleanMap : MMap[Identifier, (IAtom, ValDef)] = MMap()  
  val functionMap : MMap[Identifier, IFunction] = MMap()
  val adtMap : MMap[Identifier, ITerm] = MMap()

  object inoxToPrincess {
    def parseValDef(vdef : ValDef) = {
      vdef.tpe match {
        case IntegerType => integerMap(vdef.id)._1
        case BooleanType => booleanMap(vdef.id)._1
        case _ => throw new PrincessSolverException("ValDef TYPE")
      }
    }

    def parseExpr(expressions : Trees) : IExpression = {
      expressions match {
        case variable @ Variable(id, tpe) => {
          tpe match {
            case BooleanType => {
              if (!(booleanMap contains id))
                booleanMap += (id -> ((p.createBooleanVariable(id.toString).asInstanceOf[IAtom], variable.toVal)))
              booleanMap(id)._1
            }

            case IntegerType => {
              if (!(integerMap contains id))
                integerMap += (id -> ((p.createConstant(id.toString), variable.toVal)))
              integerMap(id)._1
            }

            case ADTType(adtName, adtTps) => {
              adtName.toString match {
                case "Nat" => {
                  if (!(adtMap contains id))
                    adtMap += (id -> p.createConstant(adtName.toString))
                  adtMap(id)
                }
                case "Z" => p.zero()
                case _ => throw new PrincessSolverException("ADT TYPE ||" + id + "||")
              }
            }              

            // TODO: Can we handle some of these types
            case UnitType    =>
              throw new PrincessSolverException("UNIT TYPE")
            case CharType    =>
              throw new PrincessSolverException("CHAR TYPE")              
            case RealType =>
              throw new PrincessSolverException("REAL TYPE")
            case StringType  =>
              throw new PrincessSolverException("STRING TYPE")
            case BVType(size)   =>
              throw new PrincessSolverException("BV TYPE")
            case TypeParameter(id)  =>
              throw new PrincessSolverException("TYPE PARAMETER")
            case TupleType(bases)  =>
              throw new PrincessSolverException("TYPLE TYPE")
            case SetType(base)  =>
              throw new PrincessSolverException("SET TYPE")
            case BagType(base)  =>
              throw new PrincessSolverException("BAG TYPE")
            case MapType(from, to)  =>
              throw new PrincessSolverException("MAP TYPE")
            case FunctionType(from, to) =>
              throw new PrincessSolverException("FUNCTION TYPE")
            case _ =>
              throw new Exception("Unhandled Variable type")
          }
        }

        // LITERALS
        case BooleanLiteral(value) => value
        case IntegerLiteral(value) => value.toInt


        // EQUALITY
        case Equals(lhs, rhs) => {
          val pLhs = parseExpr(lhs)
          val pRhs = parseExpr(rhs)
            (pLhs, pRhs) match {
            case (t1 : ITerm, t2 : ITerm) => t1 === t2
            case (a1 : IAtom, a2 : IAtom) => a1 <=> a2

            case (a1 : IAtom, f2 : IFormula) => a1 <=> f2
            case (f1 : IFormula, a2 : IAtom) => f1 <=> a2

            case (a1 : IAtom, fun2 : IFunApp) => a1 <=> (fun2 === 1)
            case (fun1 : IFunApp, a2 : IAtom) => a2 <=> (fun1 === 1)
            case (_, _) => throw new PrincessSolverException("Equality between types not supported: " + pLhs.getClass + " === " + pRhs.getClass)
          }
        }

        case FunctionInvocation(id, tps, args) => {
          if (!(functionMap contains id)) {
            val newFun = p.createFunction(id.toString, args.length)
            functionMap += (id -> newFun)
          }
          val pArgs = for (a <- args) yield parseExpr(a)
          IFunApp(functionMap(id), (pArgs.map(_.asInstanceOf[ITerm])))
        }

        // BOOLEAN CONNECTIVES
        case Not(expr) => ! (parseExpr(expr).asInstanceOf[IFormula])
        case And(exprs) => {
          val subExprs =
            for (e <- exprs) yield
              parseExpr(e).asInstanceOf[IFormula]
          (subExprs.head /: subExprs.tail)((p, q) => p & q)
        }

        case Or(exprs) => {
          val subExprs =
            for (e <- exprs) yield
              parseExpr(e).asInstanceOf[IFormula]
          (subExprs.head /: subExprs.tail)((p, q) => p | q)
        }          

        case Implies(lhs, rhs) => {
          val pLhs = parseExpr(lhs).asInstanceOf[IFormula]
          val pRhs = parseExpr(rhs).asInstanceOf[IFormula]
          pLhs ==> pRhs
        }


        // INTEGER COMPARISON
        case LessThan(lhs, rhs) => {
          val pLhs = parseExpr(lhs).asInstanceOf[ITerm]
          val pRhs = parseExpr(rhs).asInstanceOf[ITerm]
          pLhs < pRhs
        }

        case GreaterThan(lhs, rhs) => {
          val pLhs = parseExpr(lhs).asInstanceOf[ITerm]
          val pRhs = parseExpr(rhs).asInstanceOf[ITerm]
          pLhs > pRhs
        }

        case LessEquals(lhs, rhs) => {
          val pLhs = parseExpr(lhs).asInstanceOf[ITerm]
          val pRhs = parseExpr(rhs).asInstanceOf[ITerm]
          pLhs <= pRhs
        }

        case GreaterEquals(lhs, rhs) => {
          val pLhs = parseExpr(lhs).asInstanceOf[ITerm]
          val pRhs = parseExpr(rhs).asInstanceOf[ITerm]
          pLhs >= pRhs
        }

        // INTEGER ARITHMETIC
        case Plus(lhs, rhs) => {
          val pLhs = parseExpr(lhs).asInstanceOf[ITerm]
          val pRhs = parseExpr(rhs).asInstanceOf[ITerm]
          pLhs + pRhs
        }

        case Minus(lhs, rhs) => {
          val pLhs = parseExpr(lhs).asInstanceOf[ITerm]
          val pRhs = parseExpr(rhs).asInstanceOf[ITerm]
          pLhs - pRhs
        }

        case Times(lhs, rhs) => {
          val pLhs = parseExpr(lhs).asInstanceOf[ITerm]
          val pRhs = parseExpr(rhs).asInstanceOf[ITerm]
          pLhs * pRhs
        }

        // TODO: We should support these
        case Division(lhs, rhs) => {
          val pLhs = parseExpr(lhs).asInstanceOf[ITerm]
          val pRhs = parseExpr(rhs).asInstanceOf[ITerm]
          throw new PrincessSolverException("DIVISION")
        }

        case Remainder(lhs, rhs) => {
          val pLhs = parseExpr(lhs).asInstanceOf[ITerm]
          val pRhs = parseExpr(rhs).asInstanceOf[ITerm]
          throw new PrincessSolverException("REMAINDER")
        }

        case Modulo(lhs, rhs) => {
          val pLhs = parseExpr(lhs).asInstanceOf[ITerm]
          val pRhs = parseExpr(rhs).asInstanceOf[ITerm]
          throw new PrincessSolverException("MODULO")
        }


        // ADT
        // TODO: Extend ADT to general case
        case ADT(adt, args) => {
          adt.toString match {
            case "S" => {
              if (args.length > 1)
                throw new Exception("Too many arguments to succ")
              val pArg = parseExpr(args(0))
              p.succ(pArg.asInstanceOf[ITerm])
            }
            case "Z" => p.zero()
            case _ => throw new PrincessSolverException("ADT " + adt)
          }
        }

        case ADTSelector(adt, selector) => {
          if (selector.toString == "p") {
            // Hardcoded Nat.pred
            val pArg = parseExpr(adt)
            p.pred(pArg.asInstanceOf[ITerm])
          } else {
            throw new PrincessSolverException("ADTSelector")
          }
        }

        // I think we can ignore this since we do not type our variables
        case AsInstanceOf(expr, tpe) => {
          parseExpr(expr)
        }

        case IsInstanceOf(expr, tpe) => {
          if (tpe.toString == "Z") {
            // Hardcoded Nat.isZero
            val pArg = parseExpr(expr)
            p.isZero(pArg.asInstanceOf[ITerm])
          } else {
            throw new PrincessSolverException("AsInstanceOf")
          }
        }          

        // QUANTIFIERS
        // TODO: This is currently not used by Inox
        // Maybe we want to handle them by ourselves?
        case Forall(args, body) => {
          val pBody = parseExpr(body).asInstanceOf[IFormula]
          val pArgs =
            for (a <- args) yield {
              parseValDef(a)
            }
          // Let's do one quantifier!
          if (pArgs.length > 1)
            throw new PrincessSolverException("FORALL >1 QUANTIFIER")
          val a = pArgs.head
          all(a => pBody)
        }


        // LAMBDA
        case Lambda(args, body) => {
          parseExpr(body)
          throw new PrincessSolverException("LAMDA")
        }

        case exp => throw new Exception("Cannot handle type: " + exp.getClass)
      }
    }

    // Tries to convert Inox Expression to Princess IFormula
    // If fails, just return the true formula.
    def apply(expressions : Trees) : IFormula = {
      try {
        // TODO: Hack! How do we convert IAtom to isTrue(IAtom)?
        val pExp = parseExpr(expressions)
        (if (pExp.isInstanceOf[IAtom])
          pExp.asInstanceOf[IAtom] & pExp.asInstanceOf[IAtom]
        else
          pExp).asInstanceOf[IFormula]

      } catch {
        case e : PrincessSolverException => {
          println("PrincessSolver: " + e)
          // TODO: Change and don't catch this expression
          // when we have a more stable
          true
        }
      }
    }
  }


  import scala.collection.mutable.ListBuffer

  // These are only used for debugging purposes.
  // Maybe we can ask Princess to print asserted
  // constraints instead of keeping track of them.
  var constraints : ListBuffer[IFormula] = ListBuffer()
  var pushedConstraints : List[IFormula] = List()

  override def assertCnstr(expressions : Trees) : Unit = {
    val parsedExp = inoxToPrincess(expressions)
    constraints += parsedExp
    p !! parsedExp
  }

  private def internalCheck() : Option[Map[ValDef, Expr]] = {
    import SimpleAPI.ProverStatus    
    // println("//======================\\\\")
    // println("|| PrincessSolver.check ||")
    // println("||----------------------//")
    // for (c <- constraints)
    //   println("|| " + c)
    // println("||----------------------\\\\")
    if (constraints.map(_.toString) contains "true") {
      // println("|| (Exception encountered) Let's say UNSAT")
      None
    } else {
      val result = (p.???)
      // println("|| " + result)
      // TODO: What to we do with inconclusive results?
      if (result == ProverStatus.Sat || result == ProverStatus.Inconclusive) {
        val model = p.partialModel
        // println("||----------------------||")

        // Construct a Model for Inox
        val inoxMap = MMap() : MMap[ValDef, Expr]

        // Booleans
        for ((id, (iterm, valdef)) <- booleanMap; v = model.eval(iterm); if v.isDefined) {
          // println("|| " + iterm + "(" + id + ") = " + v)
          inoxMap += (valdef -> BooleanLiteral(v.get))
        }

        // Integers
        for ((id, (iterm, valdef)) <- integerMap; v = model.eval(iterm); if v.isDefined) {
          println("|| " + iterm + "(" + id + ") = " + v)
          inoxMap += (valdef -> IntegerLiteral(v.get.bigIntValue))
        }        

        // Let's convert model to something useful!
        // println("\\\\======================//\n\n")
        Some(inoxMap.toMap)
      } else if (result == ProverStatus.Unsat) {
        // println("\\\\======================//\n\n")
        None
      } else {
        // println("\\\\======================//\n\n")
        throw new PrincessSolverException("Neither SAT nor UNSAT result...")
      }
    }
  }

  override def check(config: CheckConfiguration): config.Response[Model, Assumptions] = {
    val result = internalCheck()
    result match {
      case Some(model) if config.withModel => config.cast(SatWithModel(Map() : Map[ValDef, Expr]))
      case Some(_) => config.cast(Sat)
      case None => config.cast(Unsat)
    }
  }

  // We use push/pop to simulate checking with assumptions
  override def checkAssumptions(config: Configuration)(assumptions: Set[Trees]): config.Response[Model, Assumptions] = {
    p.push
    pushedConstraints = constraints.toList

    for (a <- assumptions) {
      assertCnstr(a)
    }
    val result = internalCheck()
    p.pop
    constraints.clear()
    constraints ++= pushedConstraints
    result match {
      case Some(model) if config.withModel => config.cast(SatWithModel(Map() : Map[ValDef, Expr]))
      case Some(_) => config.cast(Sat)
      case None => config.cast(Unsat)
    }    
  }

  override def free() = {
    p.shutDown
  }

  // TODO: These should be implemented, some of the should be quite easy.
  override def pop() =
    throw new PrincessSolverException("POP not implemented")    
  override def push() =
    throw new PrincessSolverException("PUSH not implemented")    
  override def reset() =
    throw new PrincessSolverException("RESET not implemented")    
  override def interrupt() =
    throw new PrincessSolverException("INTERRUPT not implemented")
  def recoverInterrupt() =
    throw new PrincessSolverException("RECOVERINTERRUPT not implemented")
}
