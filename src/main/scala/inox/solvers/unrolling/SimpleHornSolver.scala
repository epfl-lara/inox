/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

import theories._
import evaluators._
import combinators._

import scala.collection.mutable.{Map => MutableMap, ListBuffer, Set => MutableSet}
import inox.solvers.smtlib.SMTLIBTarget

object AbstractSimpleHornSolver {

  private def computeProgramEncoder(prog: Program,
                                    enc: transformers.ProgramTransformer {val sourceProgram: prog.type},
                                    chooses: ChooseEncoder {val program: prog.type; val sourceEncoder: enc.type},
                                    theoriesCtor: transformers.ProgramTransformer {
                                      val sourceProgram: prog.type
                                      val targetProgram: chooses.targetProgram.type
                                    } => transformers.ProgramTransformer {
                                      val sourceProgram: chooses.targetProgram.type
                                      val targetProgram: Program {val trees: enc.targetProgram.trees.type}
                                    }):
  (transformers.ProgramTransformer {
    val sourceProgram: prog.type
    val targetProgram: Program {val trees: enc.targetProgram.trees.type}
  }) = {
    val fullEncoder = enc andThen chooses
    val theories = theoriesCtor(fullEncoder)
    fullEncoder andThen theories
  }
}

abstract class AbstractSimpleHornSolver private
  (override val program: Program,
   override val context: Context)
  // Alias for `program`, as there are some places where `program` is shadowed.
  (val prog: program.type)
  (val enc: transformers.ProgramTransformer {val sourceProgram: program.type})
  (val chooses: ChooseEncoder {val program: prog.type; val sourceEncoder: enc.type})
  (val programEncoder: transformers.ProgramTransformer {
    val sourceProgram: program.type
    val targetProgram: Program { val trees: enc.targetProgram.trees.type }
  })
  (using val semantics: program.Semantics,
   val targetSemantics: programEncoder.targetProgram.Semantics)
  extends Solver { self =>

  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}
  import SolverResponses._

  protected type Encoded

  private def this(prog: Program,
                   context: Context,
                   enc: transformers.ProgramTransformer {val sourceProgram: prog.type},
                   chooses: ChooseEncoder {val program: prog.type; val sourceEncoder: enc.type},
                   programEncoder: transformers.ProgramTransformer {
                     val sourceProgram: prog.type
                     val targetProgram: Program {val trees: enc.targetProgram.trees.type}
                   })
                  (using semantics: prog.Semantics,
                   semanticsProvider: SemanticsProvider {val trees: enc.targetProgram.trees.type}) =
    this(prog, context)(prog)(enc)(chooses)(programEncoder)(using semantics, programEncoder.targetProgram.getSemantics(using semanticsProvider))

  def this(prog: Program,
           context: Context,
           enc: transformers.ProgramTransformer {val sourceProgram: prog.type},
           chooses: ChooseEncoder {val program: prog.type; val sourceEncoder: enc.type})
          // Given a `fullEncoder` (constructed by `enc andThen chooses`), produce a theory
          (theoriesCtor: transformers.ProgramTransformer {
            val sourceProgram: prog.type
            val targetProgram: chooses.targetProgram.type
          } => transformers.ProgramTransformer {
            val sourceProgram: chooses.targetProgram.type
            val targetProgram: Program {val trees: enc.targetProgram.trees.type}
          })
          (using semantics: prog.Semantics,
           semanticsProvider: SemanticsProvider {val trees: enc.targetProgram.trees.type}) =
    this(prog, context, enc, chooses, AbstractSimpleHornSolver.computeProgramEncoder(prog, enc, chooses, theoriesCtor))

  protected final val s: programEncoder.sourceProgram.trees.type = programEncoder.sourceProgram.trees
  protected final val t: programEncoder.targetProgram.trees.type = programEncoder.targetProgram.trees
  protected final val targetProgram: programEncoder.targetProgram.type = programEncoder.targetProgram

  protected val templates: Templates {
    val program: targetProgram.type
    type Encoded = self.Encoded
  }

  protected val underlying: AbstractSolver {
    val program: targetProgram.type
    type Trees = Encoded
  } & SMTLIBTarget

  protected final def encode(vd: ValDef): t.ValDef = programEncoder.encode(vd)
  protected final def decode(vd: t.ValDef): ValDef = programEncoder.decode(vd)

  protected final def encode(v: Variable): t.Variable = programEncoder.encode(v)
  protected final def decode(v: t.Variable): Variable = programEncoder.decode(v)

  protected final def encode(e: Expr): t.Expr = programEncoder.encode(e)
  protected final def decode(e: t.Expr): Expr = programEncoder.decode(e)

  protected final def encode(tpe: Type): t.Type = programEncoder.encode(tpe)
  protected final def decode(tpe: t.Type): Type = programEncoder.decode(tpe)

  lazy val checkModels = options.findOptionOrDefault(optCheckModels)
  lazy val silentErrors = options.findOptionOrDefault(optSilentErrors)
  lazy val unrollBound = options.findOptionOrDefault(optUnrollBound)
  lazy val unrollFactor = options.findOptionOrDefault(optUnrollFactor)
  lazy val feelingLucky = options.findOptionOrDefault(optFeelingLucky)
  lazy val unrollAssumptions = options.findOptionOrDefault(optUnrollAssumptions)
  lazy val modelFinding = options.findOptionOrDefault(optModelFinding) > 0

  def check(config: CheckConfiguration): config.Response[Model, Assumptions] =
    checkAssumptions(config)(Set.empty)

  protected val freeVars  = new IncrementalMap[Variable, Encoded]()
  private val constraints = new IncrementalSeq[Expr]()
  private val encodedConstraints = new IncrementalSeq[Expr]()
  private val freeChooses = new IncrementalMap[Choose, Encoded]()

  protected var failures: ListBuffer[Throwable] = new ListBuffer
  protected var abort: Boolean = false
  protected var pause: Boolean = false

  def push(): Unit = {
    templates.push()
    constraints.push()
    freeVars.push()
  }

  def pop(): Unit = {
    templates.pop()
    constraints.pop()
    freeVars.pop()
  }

  def reset() = {
    failures.clear()
    abort = false
    pause = false

    templates.reset()
    constraints.reset()
    freeVars.reset()
    underlying.reset()
  }

  def interrupt(): Unit = { abort = true }

  def free(): Unit = context.interruptManager.unregisterForInterrupts(this)

  protected def declareVariable(v: t.Variable): Encoded

  private def removeChooses(expr: Expr): (Expr, Map[Variable, Encoded]) = {
    var chooseBindings: Map[Variable, Encoded] = Map.empty
    val withoutChooses = exprOps.postMap {
      case c: Choose =>
        val v = c.res.toVariable
        chooseBindings += v -> freeChooses.cached(c)(declareVariable(encode(v)))
        Some(Assume(c.pred, v))
      case _ => None
    } (expr)

    (withoutChooses, chooseBindings)
  }

  def declare(vd: ValDef): Unit = context.timers.solvers.declare.run(try {
    context.timers.solvers.declare.sanity.run {
      assert(vd.getType.isTyped)
    }

    // Multiple calls to registerForInterrupts are (almost) idempotent and acceptable
    context.interruptManager.registerForInterrupts(this)

    val freeBindings: Map[Variable, Encoded] = (typeOps.variablesOf(vd.tpe) + vd.toVariable).map {
      v => v -> freeVars.cached(v)(declareVariable(encode(v)))
    }.toMap

    val newClauses = context.timers.solvers.declare.clauses.run {
      templates.instantiateVariable(encode(vd.toVariable), freeBindings.map(p => encode(p._1) -> p._2))
    }

    context.timers.solvers.declare.underlying.run {
      for (cl <- newClauses) {
        underlying.assertCnstr(cl)
      }
    }
  } catch {
    case e @ (_: InternalSolverError | _: Unsupported) => failures += e
  })

  def assertCnstr(expression: Expr): Unit = context.timers.solvers.assert.run(try {
    context.timers.solvers.assert.sanity.run {
      symbols.ensureWellFormed // make sure that the current program is well-formed
      typeCheck(expression, BooleanType()) // make sure we've asserted a boolean-typed expression
    }

    println(s"ACTUALLY RECEIVED\n$expression")

    // Multiple calls to registerForInterrupts are (almost) idempotent and acceptable
    context.interruptManager.registerForInterrupts(this)

    constraints += expression

    val (withoutChooses, chooseBindings) = removeChooses(expression)

    val freeBindings: Map[Variable, Encoded] = exprOps.variablesOf(withoutChooses).map {
      v => v -> freeVars.cached(v)(declareVariable(encode(v)))
    }.toMap

    val newClauses = context.timers.solvers.assert.clauses.run {
      HornBuilder.encodeNegatedAssertion(withoutChooses)
    }

    encodedConstraints ++= newClauses

    context.timers.solvers.assert.underlying.run {
      for (cl <- newClauses) {
        underlying.assertCnstr(encode(cl).asInstanceOf)
      }
    }

  } catch {
    case e @ (_: InternalSolverError | _: Unsupported) => failures += e
  })

  object HornBuilder {
    case class UnexpectedMatchError(expr: Expr) extends Exception(s"Unexpected match error on $expr.")

    private def isSimpleValue(expr: Expr): Boolean = 
      expr match
        case Variable(_, tpe, _) => !tpe.isInstanceOf[FunctionType] 
        case Assume(_, _) => false
        case Let(_, _, _) => false
        case Application(_, _) => false
        case Lambda(_, _) => false 
        case Forall(_, _) => false
        case Choose(_, _) => false
        case IfExpr(_, _, _) => false
        case FunctionInvocation(_, _, args) => false // functions need to be replaced! // args.forall(isSimpleValue)
        case Operator(args, _) => args.forall(isSimpleValue)
        case _ => throw UnexpectedMatchError(expr)

    type Clauses = Seq[Expr]
    type Guards = Seq[Expr]

    private val funReplacements = MutableMap.empty[Identifier, Variable]

    val dependencies = MutableMap.empty[Identifier, Set[Identifier]]

    private def canonicalType(tpe: Type): Type =
      tpe match
        case FunctionType(_, _) => IntegerType()
        case _ => tpe      

    private def registerFun(id: Identifier): Expr = 
      val fd = symbols.getFunction(id)
      val inp = fd.params.map(_.tpe) :+ fd.returnType
      val out = BooleanType()
      val tpe = FunctionType(inp.map(canonicalType), canonicalType(out))
      val repl = funReplacements.getOrElseUpdate(id, {
        val repl = Variable.fresh(id.name, tpe, true)
        repl
      })
      registerPredicate(repl)
      val y = Variable.fresh("y", fd.returnType)
      val z = Variable.fresh("z", fd.returnType)
      val funClause = Implies(And(Seq(Application(repl, fd.params.map(_.toVariable) :+ y), Application(repl, fd.params.map(_.toVariable) :+ z))), Equals(y, z))
      funClause

    /**
      * Given an expression, construct a new predicate P and relevant clauses such that
      *
      * res == expr ==> P(res) (+ free variables)
      * 
      * Clauses may need recursive exploration and construction.
      * 
      * @return defining clauses and P(res)
      */
    private def makePredicate(expr: Expr, frees: Seq[Variable], res: Variable): (Clauses, Guards, Expr) =
      val args = frees :+ res
      val tpe = 
        val inp = args.map(_.tpe)
        val out = BooleanType()
        FunctionType(inp.map(canonicalType), canonicalType(out))
      val pred = Variable.fresh("H", tpe, true)
      registerPredicate(pred)
      val (clauses, guards, body) = mkExprClauses(expr)
      val aply = (x: Expr) => Application(pred, frees :+ x)
      
      // construct constraints
      val lhs = if guards.isEmpty then body(res) else And(guards :+ body(res))
      val predClause = Implies(lhs, aply(res))

      (clauses :+ predClause, Seq.empty, aply(res))

    private val constants = MutableSet[Variable]()

    def registerPredicate(id: Variable): Unit = 
      registerAsConstant(id)
      underlying.registerPredicate(encode(id))
    inline def registerAsConstant(id: Variable) = 
      constants += id

    inline def free(id: Variable): Boolean = constants.contains(id)

    def free(expr: Expr): Boolean = 
      expr match
        case v: Variable => free(v)
        case _ => false
    
    private val registeredLambdas = MutableMap[Lambda, (Clauses, Variable, Variable)]()
    private val uninterpretedLambdas = MutableMap[Variable, Variable]()
    private val applicationPredicates = MutableMap[Type, Variable]()

    private def registerLambda(l: Lambda): (Clauses, Variable, Variable) = 
      registeredLambdas.getOrElse(l, {
        val id = Variable.fresh("lambda", IntegerType())
        registerAsConstant(id)
        val tpe = FunctionType(IntegerType() +: l.params.map(_.tpe) :+ l.body.getType, BooleanType())
        val pred = getApplicationPredicate(tpe)
        val res = Variable.fresh("res", l.body.getType)
        val (bodyClauses, bodyGuards, bodyExpr) = mkExprClauses(l.body)
        val lhs = withGuards(bodyGuards, bodyExpr(res))
        val defClause = Implies(lhs, Application(pred, id +: l.params.map(_.toVariable) :+ res))
        val quantified = Forall(l.params :+ res.toVal, defClause)
        (bodyClauses :+ quantified, id, pred)
      })

    case class UnexpectedTypeError(tpe: Type) extends Exception(s"Unexpected match error on $tpe.")

    def getApplicationPredicate(tpe: Type): Variable = 
      applicationPredicates.getOrElse(tpe, {
        tpe match
          case FunctionType(from, to) =>
            val appType = IntegerType() +: from :+ to
            val app = Variable.fresh("DynApp", FunctionType(appType.map(canonicalType), BooleanType()))
            registerPredicate(app)
            app
          case _ => throw UnexpectedTypeError(tpe)
      })

    def registerHigherOrderVar(id: Variable): Variable = 
      // map this to a new Integer variable
      uninterpretedLambdas.getOrElse(id, Variable.fresh(id.id.name, IntegerType()))

    inline def withGuards(guards: Guards, body: Expr): Expr = 
      if guards.isEmpty then body else And(guards :+ body)

    private def mkExprClauses(expr: Expr): (Clauses, Guards, Expr => Expr) = 
      // println(s"MK EXPR CLAUSES $expr")
      // println(s"EXPR CLASS ${expr.getClass.getName}")
      // println(s"========================")
      val clauses = ListBuffer.empty[Expr]
      val guards = ListBuffer.empty[Expr]
      val freeVars = exprOps.variablesOf(expr).toSeq

      if isSimpleValue(expr) then
        (Seq.empty, Seq.empty, Equals(_, expr))
      else
        expr match
          case v @ Variable(id, FunctionType(_, _), _) =>
            // other variable cases are simple expression, and covered above
            (clauses.toSeq, guards.toSeq, Equals(_, registerHigherOrderVar(v)))
          case Assume(cond, body) => 
            // println("Matched assume")
            val newCond = 
              if isSimpleValue(cond) then
                cond
              else
                val (condClauses, condGuards, condPred) = makePredicate(cond, freeVars, Variable.fresh("Cond", BooleanType()))
                clauses ++= condClauses
                guards ++= condGuards
                condPred
            val newBody = 
                val (bodyClauses, bodyGuards, bodyPred) = makePredicate(body, freeVars, Variable.fresh("res", body.getType))
                clauses ++= bodyClauses
                guards ++= bodyGuards
                bodyPred

            val res = Variable.fresh("res", body.getType)
            // val lhs1 = if guards.isEmpty then newCond else And(guards.toSeq :+ newCond)
            // val lhs2 = And(guards.toSeq ++ Seq(Not(newCond), newBody))
            // val contra = Implies(lhs2, BooleanLiteral(false))

            val Application(pred, _) = (newBody: @unchecked)
            
            (clauses.toSeq, guards.toSeq :+ newCond, (e: Expr) => Application(pred, freeVars :+ e))
            
          case Choose(res, pred) => ??? // Unexpected
          case Let(vd, value, body) =>
            // println("Matched let")
            val cond = 
                val (valueClauses, valueGuards, valuePred) = mkExprClauses(value)
                clauses ++= valueClauses
                guards ++= valueGuards
                valuePred
            val bodyPred = 
                val (bodyClauses, bodyGuards, bodyPred) = mkExprClauses(body)
                clauses ++= bodyClauses
                guards ++= bodyGuards
                bodyPred
            (clauses.toSeq, guards.toSeq :+ cond(vd.toVariable), bodyPred)
          case IfExpr(cond, thenn, elze) => 
            // println("Matched if")
            val tpe = thenn.getType
            val newCond = 
              if isSimpleValue(cond) then
                cond
              else
                val (condClauses, condGuards, condPred) = makePredicate(cond, freeVars, Variable.fresh("Cond", BooleanType()))
                clauses ++= condClauses
                guards ++= condGuards
                condPred

            val condLabel = Variable.fresh("CondInner", tpe)
            val (thennClauses, thennGuards, thennExpr) = makePredicate(thenn, freeVars, condLabel)
            val (elzeClauses, elzeGuards, elzeExpr) = makePredicate(elze, freeVars, condLabel)
            clauses ++= thennClauses
            clauses ++= elzeClauses
            guards ++= thennGuards
            guards ++= elzeGuards
            
            val iftpe = 
              val inp = freeVars.map(_.tpe) :+ tpe
              val out = BooleanType()
              FunctionType(inp.map(canonicalType), out)
            val newPred = Variable.fresh("If", iftpe, true)
            registerPredicate(newPred)
            // TODO: check if these predicates need to be type polymorphic
            val res = Variable.fresh("res", tpe).toVal
            val newPredExpr = (res: Expr) => Application(newPred, freeVars :+ res)
            val newClauses = Seq(
              Implies(And(newCond, thennExpr), newPredExpr(condLabel)),
              Implies(And(Not(newCond), elzeExpr), newPredExpr(condLabel))
            )
            clauses ++= newClauses
            (clauses.toSeq, guards.toSeq, newPredExpr)
          case Application(l @ Lambda(params, body), args) =>
            // println("Matched app")
            val (lambdaClauses, repl, app) = registerLambda(l)
            val (bodyClauses, bodyGuards, bodyExpr) = mkExprClauses(body)
            clauses ++= lambdaClauses
            clauses ++= bodyClauses
            guards  ++= bodyGuards

            (clauses.toSeq, guards.toSeq, res => Application(app, repl +: args :+ res))

          case l @ Lambda(args, body) => 
            // eliminate it into an integer, and generate an applicative
            // predicate for it, if not already done
            val (definingClauses, identifier, _) = registerLambda(l)
            clauses ++= definingClauses
            (clauses.toSeq, guards.toSeq, Equals(_, l))
          case Forall(args, body) => ??? // Quantifier? Unexpected
          case FunctionInvocation(id, tps, args) if funReplacements.contains(id) =>
            // println("Matched func")
            val newID = funReplacements(id)
            val outType = expr.getType
            val newArgs = args.map { a =>
              if isSimpleValue(a) || a.getType.isInstanceOf[FunctionType] then
                a
              else
                // register a new guard
                val newArg = Variable.fresh("arg", a.getType)
                val (predClauses, predGuards, pred) = makePredicate(a, freeVars, newArg)
                guards ++= predGuards
                guards += pred
                clauses ++= predClauses
                newArg
            }
            (clauses.toSeq, guards.toSeq, e => Application(newID, newArgs :+ e))
          case Application(l : Variable, args) if l.tpe.isInstanceOf[FunctionType] =>
            val repl = registerHigherOrderVar(l)
            val app = getApplicationPredicate(l.tpe)
            (clauses.toSeq, guards.toSeq, res => Application(app, l +: args :+ res))
          case Operator(args, recons) => 
            // println("Matched op")
            // println(s"OPERATOR $expr")
            // println(s"ARGS\n\t ${args.mkString("\n\t")}")
            val guards = ListBuffer.empty[Expr]
            val newArgs = args.map { a =>
              if isSimpleValue(a) then
                a
              else
                // register a new guard
                val newArg = Variable.fresh("arg", a.getType, true)
                val (predClauses, predGuards, pred) = makePredicate(a, freeVars, newArg)
                guards ++= predGuards
                clauses ++= predClauses
                newArg
            }
            val newExpr = recons(newArgs)
            println(s"Constructed $newExpr")
            val body = (e: Expr) => withGuards(guards.toSeq, Equals(e, newExpr))
            (clauses.toSeq, guards.toSeq, body)
          case _ => throw UnexpectedMatchError(expr)

    
    def getFunction(id: Identifier): Variable = funReplacements(id)

    val funClauses = MutableSet.empty[Expr]

    private def quantify(clause: Expr): Forall = 
      val frees = exprOps
                  .variablesOf(clause)
                  .filterNot(free(_))
                  .map(_.toVal)
                  .toSeq
      Forall(frees, clause)

    def registerFunctions =
      funClauses.clear()
      val clauses = baseFunctions.map(f => registerFun(f.id))
      funClauses ++= clauses.map(quantify)

    def encodeFunction(tfd: TypedFunDef): Clauses = 
      val body = tfd.fullBody
      
      // get the predicate for this function
      val pred = getFunction(tfd.id)
      val outType = tfd.returnType
      val args = tfd.params.map(_.toVariable)
      val res = Variable.fresh("res", outType)
      val (clauses, guards, bodyPred) = mkExprClauses(body)
      val lhs = withGuards(guards, bodyPred(res))
      val topClause = Implies(lhs, Application(pred, args :+ res))
      val goalClauses = guards.map(cl => Implies(Not(cl), Not(Application(pred, args :+ res))))
      val allClauses = (clauses ++ goalClauses :+ topClause).distinct
      // collect function call dependencies
      val deps = allClauses.toSet.flatMap(cl => exprOps.collect[Identifier] {
        case fi @ FunctionInvocation(id, _, _) => Set(id)
        case _ => Set.empty
      } (cl)).filterNot(_ == tfd.id)
      dependencies(tfd.id) = deps // store dependencies globally
      // quantify each clause appropriately
      allClauses.map(quantify)

    def constructBoolean(expr: Expr): (Clauses, Expr) =
      println(s"Operating on $expr")
      val freeVars = exprOps.variablesOf(expr)
      def newHead = 
        val tpe = FunctionType(freeVars.map(_.tpe).toSeq, BooleanType())
        val pred = Variable.fresh("A", tpe)
        registerPredicate(pred)
        (pred, Application(pred, freeVars.toSeq))
      if isSimpleValue(expr) then
        (Seq.empty, expr)
      else
        expr match
          case Not(e) =>
            val (cl, ex) = constructBoolean(e)
            (cl.map {
              case Implies(inner, `ex`) => Implies(inner, Not(ex))
              case e => e
            }, e)
          case And(es) =>
            val inner = es.map(constructBoolean)
            val (_, applied) = newHead
            val lhs = And(inner.map(_._2))
            val cls = inner.flatMap(_._1) :+ Implies(lhs, applied)
            (cls, applied)
          case Or(es) =>
            val inner = es.map(constructBoolean)
            val (_, applied) = newHead
            val cls = inner.flatMap(_._1) ++ es.map(b => Implies(b, applied))
            (cls, applied)
          case Implies(lhs, rhs) =>
            constructBoolean(Or(Seq(Not(lhs), rhs)))
          case _ => 
            // should have reached a predicate
            val (clauses, guards, exp) = mkExprClauses(expr)
            val (_, applied) = newHead
            val res = Variable.fresh("resInternal", BooleanType())
            println(s"Got inner ${exp(res)}")
            val inner = exp(res) match
              case Equals(`res`, pred) => pred
              case Equals(pred, `res`) => pred
              case other => other
            val predCl = Implies(withGuards(guards, inner), applied)
            (clauses.map(quantify) :+ predCl, applied)

    def encodeNegatedAssertion(assertion: Expr): Clauses = 
      val flipped = 
        assertion match
          case Not(expr) => expr
          case _ => Not(assertion)
      val fin = assertion
      val (clauses, head) = constructBoolean(fin)
      clauses :+ head
      // val split = 
      //   fin match
      //     case Or(args) => args
      //     case _ => Seq(fin)
      // split
      //   .map(constructBoolean)
      //   .flatMap((clauses, expr) =>
      //     clauses :+ expr
      //   )

    def closeDependencies(id: Identifier): Set[Identifier] =
      require(dependencies.contains(id))
      val deps = dependencies(id)
      val allDeps = deps.filterNot(_ == id).flatMap(d => closeDependencies(d)).filterNot(_ == id)
      dependencies(id) = allDeps
      allDeps

    def closeDependencies: Unit = 
      baseFunctions.foreach(fd => closeDependencies(fd.id))

    // on construction, register all functions
    registerFunctions
    baseFunctions.foreach(fd => encodeFunction(fd.typed))
    closeDependencies
  }

  class UnderlyingHorn(override val program: targetProgram.type)
    extends smtlib.SMTLIBSolver(program, self.context) with smtlib.Z3Solver
  {
    override def targetName = "z3"
    import _root_.smtlib.trees.CommandsResponses._
    import _root_.smtlib.trees.Commands._
    import _root_.smtlib.Interpreter
    import _root_.smtlib.printer.Printer
    import _root_.smtlib.printer.RecursivePrinter
    import java.io.BufferedReader
    import _root_.smtlib.interpreters.ProcessInterpreter
    import _root_.smtlib.parser.Parser
    import _root_.smtlib.extensions.tip.Lexer

    class  HornZ3Interpreter(executable: String,
                      args: Array[String],
                      printer: Printer = RecursivePrinter,
                      parserCtor: BufferedReader => Parser = out => new Parser(new Lexer(out)))
    extends ProcessInterpreter (executable, args, printer, parserCtor):
      printer.printCommand(SetOption(PrintSuccess(true)), in)
      in.write("\n")
      in.flush()
      parser.parseGenResponse
      in.write("(set-logic HORN)\n")
      in.flush()
      parser.parseGenResponse

    override protected val interpreter = {
      val opts = interpreterOpts
      // reporter.debug("Invoking solver "+targetName+" with "+opts.mkString(" "))
      new HornZ3Interpreter(targetName, opts.toArray, parserCtor = out => new Z3Parser(new Lexer(out)))
    }
  }
  val underlyingHorn = UnderlyingHorn(targetProgram)

  val baseFunctions = program.symbols.functions.values.toSeq.filterNot(_.flags.exists(_.name == "synthetic"))
  // lazy val invariants = baseFunctions.map(
  //   fd =>
  //     val tfd = fd.typed
  //     val clauses = HornBuilder2.encodeFunction(tfd)
  //     val encoded = clauses.map(cl => templates.mkEncoder(Map.empty)(encode(cl)))
  //     underlyingHorn.reset()
  //     encoded.foreach(cl => underlyingHorn.assertCnstr(cl.asInstanceOf))
  //     val res = underlyingHorn.check(Model)

  //     res match
  //       case Unsat => None
  //       case SatWithModel(model) => 
  //         val modelWrapper = wrapModel(model.asInstanceOf)
  //         val res = Variable.fresh("res", fd.returnType)
  //         val funExpr = FunctionInvocation(HornBuilder2.getFunction(fd.id), Seq.empty, fd.params.map(_.toVariable) :+ res)
  //         val encoded = templates.mkEncoder(Map.empty)(encode(funExpr))
  //         modelWrapper.modelEval(encoded, t.BooleanType()) match
  //           case Some(expr) => 
  //             val inv = Implies(Equals(fd.applied, res), programEncoder.decode(expr))
  //             // println(s"Found invariant for ${fd.id}: $inv")
  //             Some(inv)
  //           case None => None
  //       case _ => None      
  // )

  protected def wrapModel(model: underlying.Model): ModelWrapper

  trait ModelWrapper {
    def modelEval(elem: Encoded, tpe: t.Type): Option[t.Expr]

    def extractConstructor(elem: Encoded, tpe: t.ADTType): Option[Identifier]
    def extractSet(elem: Encoded, tpe: t.SetType): Option[Seq[Encoded]]
    def extractMap(elem: Encoded, tpe: t.MapType): Option[(Seq[(Encoded, Encoded)], Encoded)]
    def extractBag(elem: Encoded, tpe: t.BagType): Option[Seq[(Encoded, Encoded)]]

    def getChoose(id: Identifier): Option[t.Expr]

    def eval(elem: Encoded, tpe: Type): Option[Expr] = modelEval(elem, encode(tpe)).flatMap {
      expr => try {
        Some(decode(expr))
      } catch {
        case u: Unsupported => None
      }
    }

    def getModel(extract: (Encoded, Type) => Expr): program.Model = {
      val vs = freeVars.toMap.map { case (v, idT) => v.toVal -> extract(idT, v.getType) }

      val cs = templates.getCalls
        .filter(p => modelEval(p._1, t.BooleanType()) == Some(t.BooleanLiteral(true)))
        .map(_._2)
        .groupBy(_.tfd)
        .flatMap { case (tfd, calls) =>
          chooses.getChoose(tfd.fd).map { case (id, c, vds) =>
            val tpSubst = tfd.tpSubst.map(p => decode(p._1).asInstanceOf[TypeParameter] -> decode(p._2))
            val from = tfd.params.map(_.getType(using tfd.symbols))
            val to = tfd.getType
            import templates._

            val inst = new typeOps.TypeInstantiator(tpSubst)
            val tvds = vds map inst.transform
            val tc = inst.transform(c.copy(res = c.res.freshen))

            val mappings = calls.flatMap { call =>
              val optArgs = (call.args zip from).map(p => modelEval(p._1.encoded, p._2))
              val optRes = modelEval(mkCall(tfd, call.args.map(_.encoded)), to)
              if (optArgs.forall(_.isDefined) && optRes.isDefined) {
                Some(optArgs.map(_.get) -> optRes.get)
              } else {
                None
              }
            }

            val body = mappings.foldRight(tc: Expr) { case ((args, img), elze) =>
              IfExpr(andJoin((tvds zip args).map { case (vd, arg) =>
                Equals(vd.toVariable, decode(arg))
              }), decode(img), elze)
            }

            (id, tfd.tps.map(decode(_))) -> body
          }
        }

      val freeCs = freeChooses.toMap.map { case (c, idT) =>
        (c.res.id, Seq.empty[Type]) -> extract(idT, c.res.getType)
      }

      def choosesOf(e: Expr, tps: Seq[Type]): Map[(Identifier, Seq[Type]), Expr] = exprOps.collect {
        case c: Choose => getChoose(c.res.id).map(e => (c.res.id, tps) -> decode(e)).toSet
        case _ => Set.empty[((Identifier, Seq[Type]), Expr)]
      } (e).toMap

      val modelCs = vs.values.toSeq.flatMap(e => choosesOf(e, Seq.empty)) ++
        (cs ++ freeCs).flatMap { case ((id, tps), e) => choosesOf(e, tps) }

      inox.Model(program)(vs, cs ++ freeCs ++ modelCs)
    }
  }

  private def emit(silenceErrors: Boolean)(msg: String) =
    if (silenceErrors) reporter.debug(msg) else reporter.warning(msg)

  private def validateModel(model: program.Model, assumptions: Seq[Expr], silenceErrors: Boolean): Boolean = {
    val expr = andJoin(assumptions ++ constraints)

    val typingCond = andJoin(model.vars.toSeq.map { case (v, value) =>
      def rec(e: Expr, tpe: Type): Expr = (e, tpe) match {
        case (ADT(id, _, args), adt @ ADTType(_, tps)) =>
          andJoin((args zip getConstructor(id, tps).fields).map(p => rec(p._1, p._2.tpe)))
        case (Tuple(es), TupleType(tps)) =>
          andJoin((es zip tps).map(p => rec(p._1, p._2)))
        case (FiniteSet(elems, _), SetType(base)) =>
          andJoin(elems.map(e => rec(e, base)))
        case (FiniteBag(elems, _), BagType(base)) =>
          andJoin(elems.map(p => and(rec(p._1, base), rec(p._2, IntegerType()))))
        case (FiniteMap(elems, dflt, _, _), MapType(from, to)) =>
          andJoin(elems.map(p => and(rec(p._1, from), rec(p._2, to))) :+ rec(dflt, to))
        case (Lambda(params, body), FunctionType(from, to)) =>
          val nparams = (params zip from).map { case (vd, tpe) => vd.copy(tpe = tpe) }
          forall(nparams, rec(
            exprOps.replaceFromSymbols((params zip nparams.map(_.toVariable)).toMap, body), to))
        case (_, RefinementType(vd, pred)) =>
          and(rec(e, vd.tpe), Let(vd, e, pred).copiedFrom(e))
        case (Lambda(params, body), PiType(nparams, to)) =>
          forall(nparams, rec(
            exprOps.replaceFromSymbols((params zip nparams.map(_.toVariable)).toMap, body), to))
        case (Tuple(es), SigmaType(nparams, to)) =>
          andJoin(
            (es.init zip nparams).map(p => rec(p._1, p._2.tpe)) ++ (rec(es.last, to) match {
              case BooleanLiteral(true) => None
              case p => Some((nparams zip es.init).foldRight(p) {
                case ((vd, e), p) => Let(vd, e, p).copiedFrom(p)
              })
            })
          )
        case (c: Choose, tpe) =>
          BooleanLiteral(
            c.res.tpe == tpe && tpe == tpe.getType && // choose is for a simple type
            (model.chooses contains (c.res.id -> Seq())) // the model contains a mapping for the choose
          )
        case _ => BooleanLiteral(true)
      }

      rec(value, v.tpe)
    })

    // we have to check case class constructors in model for ADT invariants
    val newExpr = model.vars.toSeq.foldRight(and(typingCond, expr)) {
      case ((v, value), e) => Let(v, value, e)
    }

    val evaluator = semantics.getEvaluator(using context.withOpts(
      optSilentErrors(silenceErrors),
      optCheckModels(checkModels || feelingLucky)
    ))

    evaluator.eval(newExpr, inox.Model(program)(Map.empty, model.chooses)) match {
      case EvaluationResults.Successful(BooleanLiteral(true)) =>
        reporter.debug("- Model validated.")
        true

      case EvaluationResults.Successful(_) =>
        reporter.debug("- Invalid model.")
        false

      case EvaluationResults.RuntimeError(msg) =>
        emit(silenceErrors)("- Model leads to runtime error: " + msg)
        false

      case EvaluationResults.EvaluatorError(msg) =>
        emit(silenceErrors)("- Model leads to evaluation error: " + msg)
        false
    }
  }

  private def extractSimpleModel(model: underlying.Model): program.Model = {
    val wrapped = wrapModel(model)
    wrapped.getModel((e, tpe) => wrapped.eval(e, tpe).getOrElse(simplestValue(tpe)))
  }

  private case class Canceled() extends Exception("Cancelation occurred while extracting model")

  private def extractTotalModel(model: underlying.Model): program.Model = {
    extension[T] (opt: Option[T]) {
      private def getOrThrow: T = opt match {
        case Some(t) => t
        case None =>
          if (abort) {
            // We got a None but were interrupted. Maybe this None is due to the cancellation,
            // so we throw a Canceled that will be caught by checkAssumptions
            throw Canceled()
          } else {
            // We got a None, but not due to interruption. This is likely a bug, this exception will not be caught.
            throw java.util.NoSuchElementException("None.get")
          }
      }
    }

    val wrapped = wrapModel(model)

    import targetProgram._
    import targetProgram.trees._
    import targetProgram.symbols.{given, _}

    // maintain extracted functions to make sure equality is well-defined
    var lambdaExtractions: Seq[(Encoded, Lambda)] = Seq.empty
    var chooseExtractions: Seq[(Encoded, Choose)] = Seq.empty

    def modelEq(e1: Encoded, e2: Encoded): Boolean =
      wrapped.modelEval(templates.mkEquals(e1, e2), BooleanType()) == Some(BooleanLiteral(true))

    def extractValue(v: Encoded, tpe: Type, seen: Map[FunctionType, Set[Encoded]]): Expr = {

      def functionsOf(v: Encoded, tpe: Type): (Seq[(Encoded, FunctionType)], Seq[Expr] => Expr) = {
        def reconstruct(subs: Seq[(Seq[(Encoded, FunctionType)], Seq[Expr] => Expr)],
                        recons: Seq[Expr] => Expr): (Seq[(Encoded, FunctionType)], Seq[Expr] => Expr) =
          (subs.flatMap(_._1), (exprs: Seq[Expr]) => {
            var curr = exprs
            recons(subs.map { case (es, recons) =>
              val (used, remaining) = curr.splitAt(es.size)
              curr = remaining
              recons(used)
            })
          })

        def rec(v: Encoded, tpe: Type): (Seq[(Encoded, FunctionType)], Seq[Expr] => Expr) = tpe match {
          case ft: FunctionType =>
            (Seq(v -> ft), es => es.head)

          case TupleType(tps) =>
            val id = Variable.fresh("tuple", tpe)
            val encoder = templates.mkEncoder(Map(id -> v)) _
            reconstruct(tps.zipWithIndex.map {
              case (tpe, index) => rec(encoder(TupleSelect(id, index + 1)), tpe)
            }, Tuple.apply)

          case tpe @ ADTType(sid, tps) =>
            val cons = wrapped.extractConstructor(v, tpe).getOrThrow
            val id = Variable.fresh("adt", tpe)
            val encoder = templates.mkEncoder(Map(id -> v)) _
            reconstruct(getConstructor(cons, tps).fields.map {
              vd => rec(encoder(ADTSelector(id, vd.id)), vd.getType)
            }, ADT(cons, tps, _))

          case st @ SetType(base) =>
            val vs = wrapped.extractSet(v, st).getOrThrow
            reconstruct(vs.map(rec(_, base)), FiniteSet(_, base))

          case mt @ MapType(from, to) =>
            val (vs, dflt) = wrapped.extractMap(v, mt).getOrThrow
            reconstruct(vs.flatMap(p => Seq(rec(p._1, from), rec(p._2, to))) :+ rec(dflt, to), {
              case es :+ default => FiniteMap(es.grouped(2).map(s => s(0) -> s(1)).toSeq, default, from, to)
            })

          case bt @ BagType(base) =>
            val vs = wrapped.extractBag(v, bt).getOrThrow
            reconstruct(vs.map(p => rec(p._1, base)), es => FiniteBag((es zip vs).map {
              case (k, (_, v)) => k -> wrapped.modelEval(v, IntegerType()).getOrThrow
            }, base))

          case _ => (Seq.empty, (es: Seq[Expr]) => wrapped.modelEval(v, tpe).getOrThrow)
        }

        rec(v, tpe)
      }

      val ev = wrapped.modelEval(v, tpe).filterNot(_.isInstanceOf[Variable])
      if (ev.isDefined) {
        val (functions, recons) = functionsOf(v, tpe)
        recons(functions.map { case (f, tpe) =>
          extractFunction(f, tpe, seen)
        })
      } else {
        encode(program.symbols.simplestValue(decode(tpe)))
      }
    }

    def extractFunction(f: Encoded, tpe: FunctionType, seen: Map[FunctionType, Set[Encoded]]): Expr = {
      val nextSeen = seen + (tpe -> (seen(tpe) + f))

      def extractLambda(f: Encoded, tpe: FunctionType): Option[Lambda] = {
        val optEqTemplate = templates.getLambdaTemplates(tpe).find { tmpl =>
          wrapped.modelEval(tmpl.start, BooleanType()) == Some(BooleanLiteral(true)) &&
          modelEq(tmpl.ids._2, f)
        }

        optEqTemplate.map { tmpl =>
          val localsSubst = tmpl.structure.locals.map { case (v, ev) =>
            v -> extractValue(ev, v.getType, nextSeen)
          }.toMap

          val res = exprOps.replaceFromSymbols(localsSubst, tmpl.structure.body)
          val (nl, subst) = normalizeStructure(res, onlySimple = true)
          exprOps.replaceFromSymbols(subst.map { case (v, e, _) => v -> e }.toMap, nl).asInstanceOf[Lambda]
        }
      }

      val params: Seq[ValDef] = tpe.from.map(tpe => ValDef.fresh("x", tpe, true))
      val arguments = templates.getGroundInstantiations(f, tpe).flatMap { case (b, eArgs) =>
        wrapped.modelEval(b, BooleanType()).filter(_ == BooleanLiteral(true)).map(_ => eArgs)
      }.distinct

      extractLambda(f, tpe).orElse {
        if (seen(tpe).exists(e => modelEq(f, e))) {
          Some(chooseExtractions.collectFirst { case (e, c) if modelEq(f, e) => c }.getOrElse {
            val c = Choose(Variable.fresh("x", tpe, true).toVal, BooleanLiteral(true))
            chooseExtractions :+= f -> c
            c
          })
        } else {
          None
        }
      }.getOrElse {
        val res = if (arguments.isEmpty) {
          wrapped.modelEval(f, tpe).getOrThrow.asInstanceOf[Lambda]
        } else if (tpe.from.isEmpty) {
          Lambda(Seq.empty, extractValue(templates.mkApp(f, tpe, Seq.empty), tpe.to, nextSeen))
        } else {
          val projections: Map[Type, Encoded] = (arguments.head zip params)
            .groupBy(p => p._2.getType)
            .view.mapValues(_.head._1).toMap

          val exArguments = for (args <- arguments) yield {
            (params zip args).map { case (vd, arg) => extractValue(arg, vd.getType, nextSeen) }
          }

          val argumentsWithConds: Seq[(Seq[Encoded], Expr)] =
            (for (subset <- params.toSet.subsets(); (args, exArgs) <- arguments zip exArguments) yield {
              val (concreteArgs, condOpts) = params.zipWithIndex.map { case (v, i) =>
                if (!subset(v)) {
                  (args(i), Some(Equals(v.toVariable, exArgs(i))))
                } else {
                  (projections(v.getType), None)
                }
              }.unzip

              (concreteArgs, andJoin(condOpts.flatten))
            }).toSeq

          val withConds :+ ((concreteArgs, _)) = argumentsWithConds: @unchecked
          val default = extractValue(templates.mkApp(f, tpe, concreteArgs), tpe.to, nextSeen)

          val sortedArguments = withConds
            .groupBy(_._2)
            .view.mapValues(_.head._1)
            .toSeq
            .sortBy(p => -exprOps.formulaSize(p._1))

          val mappings = sortedArguments.map { case (cond, arguments) =>
            (cond, extractValue(templates.mkApp(f, tpe, arguments), tpe.to, nextSeen))
          }

          val lambda = Lambda(params, mappings.foldRight(default) {
            case ((cond, img), elze) => IfExpr(cond, img, elze)
          })

          // make sure `lambda` is not equal to any other distinct extracted first-class function
          (lambdaExtractions.collectFirst {
            case (e, img) if img.getType == lambda.getType && modelEq(e, f) => Left(img)
            case (encoded, `lambda`) => Right(encoded)
          }) match {
            case Some(Right(enc)) => wrapped.modelEval(enc, tpe).getOrThrow match {
              case Lambda(_, Let(_, Tuple(es), _)) =>
                uniquateClosure(if (es.size % 2 == 0) -es.size / 2 else es.size / 2, lambda)
              case l => throw new InternalSolverError(name, "Unexpected extracted lambda format: " + l.asString)
            }
            case Some(Left(img)) => img
            case None => lambda
          }
        }

        lambdaExtractions :+= f -> res
        res
      }
    }

    /* The solver may return values that cannot be decoded by the theory encoder if they
     * weren't constrained by the generated clauses (eg. default values for functions).
     * We replace these by `simplestValue` instead of crashing as they won't have any influence
     * on model evaluation. */
    def decodeOrSimplest(e: t.Expr): s.Expr = try {
      decode(e)
    } catch {
      case t: TheoryException => program.symbols.simplestValue(decode(e.getType))
    }

    val initSeen: Map[FunctionType, Set[Encoded]] = Map.empty.withDefaultValue(Set.empty)
    val exModel = wrapped.getModel((e, tpe) => decodeOrSimplest(extractValue(e, encode(tpe), initSeen)))
    val exChooses = chooseExtractions.toMap.map { case (e, c) =>
      c -> lambdaExtractions.collectFirst {
        case (f, lambda) if lambda.getType == c.res.getType && modelEq(f, e) => lambda
      }.get
    }
    val chooses = exChooses.map(p => (p._1.res.id, Seq.empty[s.Type]) -> decodeOrSimplest(p._2))
    inox.Model(program)(exModel.vars, exModel.chooses ++ chooses)
  }

  def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[Model, Assumptions] =
      context.timers.solvers.unrolling.run(scala.util.Try({

      println("%%%%%%%%%%%%%%%%%%%%%%% Calling checkAssumptions %%%%%%%%%%%%%%%%%%%%%%%")
      println(s"Have base functions: ${baseFunctions.map(_.id).mkString(", ")}")
      println(s"with types ${baseFunctions.map(t => t.params.map(_.tpe) :+ t.returnType).flatten.distinct.collect {case ADTType(id, tps) => s"${id.uniqueName}[${tps.mkString}]"} .mkString(" ;; ")}")


      // throw error immediately if a previous call has already failed
      if (failures.nonEmpty) throw failures.head

      // Multiple calls to registerForInterrupts are (almost) idempotent and acceptable
      context.interruptManager.registerForInterrupts(this)

      val assumptionsSeq       : Seq[Expr]          = assumptions.toSeq
      val encodedAssumptions   : Seq[Encoded]       = assumptionsSeq.map { expr =>
        val vars = exprOps.variablesOf(expr)
        templates.mkEncoder(vars.map(v => encode(v) -> freeVars(v)).toMap)(encode(expr))
      }
      val encodedToAssumptions : Map[Encoded, Expr] = (encodedAssumptions zip assumptionsSeq).toMap

      // program.symbols.functions.values.map(
      //   fDef =>
      //     val clauses = HornBuilder.encodeFunction(fDef.typed)
      //     underlying.reset()
      //     val encodedClauses = clauses.map { expr =>
      //       templates.mkEncoder(Map.empty)(encode(expr))
      //     }
      //     encodedClauses.foreach(underlying.assertCnstr)
      //     val res = underlying.check(Model) // TODO:
      //     // println(s"===============================================================")
      //     // println(s"Function def\n$fDef")
      //     // println(s"Found result for ${fDef.id}:\n $res")
      //     // println(s"===============================================================")
      //     res
      // )

      // underlying.reset()

      // baseFunctions.foreach(
      //   fd =>
      //     // println("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$")
      //     // println(s"Look at the original:\n${fd.fullBody}")
      //     // println(s"And the encoded:\n${encode(fd.fullBody)}")
      //     // println("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$")
      // )

      // // println(s"Have ${assumptions.size} assumptions.")

      // assumptions.foreach(
      //   expr =>
      //     // println("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$")
      //     // println(s"Look at the original:\n$expr")
      //     // println(s"And the encoded:\n${encode(expr)}")
      //     // println("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$")
      // )

      val functionIDs = baseFunctions
      .filter(fd =>
        val id = fd.id
        encodedConstraints.exists(c => exprOps.variablesOf(c).exists(_.id == id))
      )
      .map(_.id)
      .flatMap(HornBuilder.dependencies.get)

      baseFunctions
      .filter(fd => functionIDs.contains(fd.id))
      .foreach(
        fDef =>
          val clauses = HornBuilder.encodeFunction(fDef.typed)
          val encodedClauses = clauses.map { expr =>
            encode(expr)
          }
          encodedClauses.foreach(c => underlying.assertCnstr(c.asInstanceOf))
      )

      // // println("===============================================================")
      // baseFunctions.foreach(// println)
      // // println("===============================================================")
      // assumptionsSeq.foreach(// println)
      // // println("===============================================================")

      assumptions.foreach(
        expr =>
          val uninverted = 
            expr match
              case Not(e) => e
              case e => Not(e)
          
          val enc = encode(expr)
          underlying.assertCnstr(enc.asInstanceOf)
      )

      val res = 
        if config.withModel then
          underlying.check(Model)
        else
          underlying.check(Simple)

      val resFlip = res match
        case Sat => Unsat
        case SolverResponses.SatWithModel(model) => Unsat
        case Unsat => 
          if config.withModel then
            SatWithModel(inox.Model(program)(Map.empty, Map.empty))
          else Sat
        case Unknown => Unknown

      val ress = res match
        case SolverResponses.SatWithModel(_) => SatWithModel(inox.Model(program)(Map.empty, Map.empty))
        case _ => res

      config.cast(resFlip)
    
  }).recover {
    case e @ (_: InternalSolverError | _: Unsupported) =>
      if (reporter.isDebugEnabled) reporter.debug(e)
      else if (!silentErrors && !abort) reporter.error(e.getMessage)
      config.cast(Unknown)
  }.get)
}

trait SimpleHornSolver extends AbstractSimpleHornSolver { self =>
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  type Encoded = t.Expr
  protected val underlying: AbstractSolver {
    val program: targetProgram.type
    type Trees = t.Expr
    type Model = targetProgram.Model
  } & SMTLIBTarget

  override lazy val name = "SH:"+underlying.name

  override val templates = new TemplatesImpl(targetProgram, context)

  private class TemplatesImpl(override val program: targetProgram.type, override val context: Context)
                             (using override val semantics: targetProgram.Semantics)
    extends Templates {
    import program._
    import program.trees._
    import program.symbols.{given, _}

    type Encoded = Expr

    def asString(expr: Expr): String = expr.asString
    def abort: Boolean = self.abort
    def pause: Boolean = self.pause

    def encodeSymbol(v: Variable): Expr = v.freshen
    def mkEncoder(bindings: Map[Variable, Expr])(e: Expr): Expr = exprOps.replaceFromSymbols(bindings, e)
    def mkSubstituter(substMap: Map[Expr, Expr]): Expr => Expr = (e: Expr) => exprOps.replace(substMap, e)

    def mkNot(e: Expr) = not(e)
    def mkOr(es: Expr*) = orJoin(es)
    def mkAnd(es: Expr*) = andJoin(es)
    def mkEquals(l: Expr, r: Expr) = Equals(l, r)
    def mkImplies(l: Expr, r: Expr) = implies(l, r)

    def extractNot(e: Expr) = e match {
      case Not(e2) => Some(e2)
      case _ => None
    }

    def decodePartial(e: Expr, tpe: Type): Option[Expr] = Some(e)
  }

  protected lazy val modelEvaluator: DeterministicEvaluator { val program: self.targetProgram.type } =
    targetSemantics.getEvaluator(using context.withOpts(optIgnoreContracts(true)))

  protected def declareVariable(v: t.Variable): t.Variable = v
  protected def wrapModel(model: targetProgram.Model): ModelWrapper = ModelWrapperImpl(model)

  private case class ModelWrapperImpl(model: targetProgram.Model) extends ModelWrapper {
    private def e(expr: t.Expr): Option[t.Expr] = modelEvaluator.eval(expr, model).result

    def extractConstructor(elem: t.Expr, tpe: t.ADTType): Option[Identifier] = e(elem) match {
      case Some(t.ADT(id, _, _)) => Some(id)
      case _ => None
    }

    def extractSet(elem: t.Expr, tpe: t.SetType): Option[Seq[t.Expr]] = e(elem) match {
      case Some(t.FiniteSet(elems, _)) => Some(elems)
      case _ => None
    }

    def extractBag(elem: t.Expr, tpe: t.BagType): Option[Seq[(t.Expr, t.Expr)]] = e(elem) match {
      case Some(t.FiniteBag(elems, _)) => Some(elems)
      case _ => None
    }

    def extractMap(elem: t.Expr, tpe: t.MapType): Option[(Seq[(t.Expr, t.Expr)], t.Expr)] = e(elem) match {
      case Some(t.FiniteMap(elems, default, _, _)) => Some((elems, default))
      case _ => None
    }

    def modelEval(elem: t.Expr, tpe: t.Type): Option[t.Expr] = e(elem)
    def getChoose(id: Identifier): Option[t.Expr] = model.chooses.collectFirst {
      case ((cid, tps), e) if cid == id && tps.isEmpty => e
    }

    override def toString = model.asString(using targetProgram.printerOpts)
  }

  override def dbg(msg: => Any) = underlying.dbg(msg)

  override def push(): Unit = {
    super.push()
    underlying.push()
  }

  override def pop(): Unit = {
    super.pop()
    underlying.pop()
  }

  override def reset(): Unit = {
    underlying.reset()
    super.reset()
  }

  override def interrupt(): Unit = {
    super.interrupt()
    underlying.interrupt()
  }

  override def free(): Unit = {
    super.free()
    underlying.free()
  }
}
