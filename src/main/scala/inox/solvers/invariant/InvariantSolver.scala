package inox
package solvers
package invariant

import inox.solvers.SolverResponses.CheckConfiguration

import inox.solvers.SolverResponses.Configuration
import scala.collection.mutable.ListBuffer
import inox.utils.IncrementalSeq
import inox.solvers.smtlib.SMTLIBSolver
import scala.collection.immutable.LazyList.cons

trait InvariantSolver extends Solver: 
  import program.trees.*

object AbstractInvariantSolver:

end AbstractInvariantSolver

abstract class AbstractInvariantSolver(override val program: Program,
   override val context: Context)
  // Alias for `program`, as there are some places where `program` is shadowed.
  (val prog: program.type)
  (val enc: transformers.ProgramTransformer {val sourceProgram: program.type})
  (val programEncoder: transformers.ProgramTransformer {
    val sourceProgram: program.type
    val targetProgram: Program { val trees: enc.targetProgram.trees.type }
  })
  (using val semantics: program.Semantics,
   val targetSemantics: programEncoder.targetProgram.Semantics)
  extends Solver with InvariantSolver:

  /* Internal imports, types, and aliases */

  protected final val s: programEncoder.sourceProgram.trees.type = programEncoder.sourceProgram.trees
  protected final val t: programEncoder.targetProgram.trees.type = programEncoder.targetProgram.trees
  protected final val targetProgram: programEncoder.targetProgram.type = programEncoder.targetProgram

  type Source  = s.Expr
  type Encoded = t.Expr

  import targetProgram._
  import targetProgram.trees._
  import targetProgram.symbols.{given, _}

  /* Formula representation and transformation */

  protected object HornClauses:
    /**
      * Representation of a Horn clause.
      *
      * @param head conclusion (possibly False, implying empty head)
      * @param body possibly empty sequence of premises
      */
    case class Clause(head: Encoded, body: Seq[Encoded]):
      /**
        * Collapse this clause to a single Inox implication.
        */
      def collapse: Encoded = 
        if body.isEmpty then head
        else if body.tail.isEmpty then Implies(body.head, head)
        else Implies(And(body), head)
      /**
        * Fresh clause with an additional guard / premise.
        */
      def withGuard(expr: Encoded): Clause =
        Clause(head, body :+ expr)
      /**
       * Fresh clause with additional guards / premises.
       */
      def withGuards(exprs: Iterable[Encoded]): Clause =
        Clause(head, body ++ exprs)


    extension (expr: Encoded)
      /**
      * Implied-by relation. Prolog syntax for Horn clauses.
      * 
      * @example `head :- (body0, body1, body2)`
      */
      infix def :- (body: Encoded*): Clause = Clause(expr, body)
      /**
      * Implied-by relation. Prolog syntax for Horn clauses.
      */
      @annotation.targetName("impliedBySeq") // disambiguate from the Encoded* version
      infix def :- (body: Iterable[Encoded]): Clause = Clause(expr, body.toSeq)

  end HornClauses

  import HornClauses.*

  /* Interface */

  /**
    * Checks whether the given set of assumptions is satisfiable together with
    * the current state. Does not permanently add them to the constraint set,
    * unlike [[assertCnstr]] + [[check]].
    *
    * @param config expected response configuration
    * @param assumptions set of assumptions to check
    * @return a response containing satisfiability result, and a model if the
    * config requires it and one is available
    */
  override def checkAssumptions(config: Configuration)(assumptions: Set[Source]): config.Response[Model, Assumptions] = 
    checkAssumptions_(config)(assumptions)

  override def declare(vd: program.trees.ValDef): Unit = 
    val evd = encode(vd)

    context.timers.solvers.declare.sanity.run:
      assert(evd.getType.isTyped)

    // Multiple calls to registerForInterrupts are (almost) idempotent and acceptable
    context.interruptManager.registerForInterrupts(this)

    registerValDef(evd)

  override def interrupt(): Unit = 
    abort = true

  override def reset(): Unit = 
    abort = false
    failures.clear()
    constraints.reset()

  override def push(): Unit = 
    constraints.push()

  override def pop(): Unit = 
    constraints.pop()

  override def free(): Unit = 
    failures.clear()
    constraints.clear()
    context.interruptManager.unregisterForInterrupts(this)

  /**
    * Checks the satisfiability of the currently asserted set of constraints.
    *
    * @param config expected response configuration
    * @return a response containing satisfiability result, and a model if the
    * config requires it and one is available
    */
  override def check(config: CheckConfiguration): config.Response[Model, Assumptions] = 
    checkAssumptions(config)(Set.empty)

  /**
    * Asserts a constraint to the solver. A call to [[check]] checks the
    * satisfiability of the conjunction of all asserted constraints.
    *
    * @param expression constraint to assert
    */
  override def assertCnstr(expression: Source): Unit = 
    constraints += expression

  override def name: String = 
    "inv-" + underlyingHorn.name

  /* Internal state */

  /**
    * Underlying Horn solver to use for invariant inference.
    */
  protected val underlyingHorn: SMTLIBSolver & AbstractSolver {
    val program: targetProgram.type
    type Trees = Encoded
  }

  /**
    * Predicate variables introduced during this run. Should not be quantifed,
    * should not be treated as HOF.
    */
  protected val predicates: IncrementalSeq[Variable] = new IncrementalSeq()

  /**
    * Top-level variables declared during this run. Should not be quantified.
    */
  protected val freeVariables: IncrementalSeq[Variable] = new IncrementalSeq()

  /**
    * Function replacements for function invocations.
    */
  protected val funReplacements: Map[Identifier, Variable] = 
    program.symbols.functions.map: (id, fd) =>
      val tpe = FunctionType(fd.params.map(p => encode(p.tpe)) :+ encode(fd.returnType), BooleanType())
      val fresh = Variable.fresh(id.name, tpe)
      registerPredicate(fresh)
      id -> fresh

  // run state

  /**
    * List of exceptions caught during this run. Thrown when the solver is asked
    * to check constraints next. 
    */
  protected val failures: ListBuffer[Throwable] = new ListBuffer

  /**
    * Whether the solver has been externally interrupted. See [[interrupt]].
    */
  private var abort: Boolean = false

  /**
    * Stack of constraints to check.
    */
  protected val constraints: IncrementalSeq[Source] = new IncrementalSeq()

  /* Translation of expressions */

  // encoding and decoding trees

  protected final def encode(vd: s.ValDef): t.ValDef = programEncoder.encode(vd)
  protected final def decode(vd: t.ValDef): s.ValDef = programEncoder.decode(vd)

  protected final def encode(v: s.Variable): t.Variable = programEncoder.encode(v)
  protected final def decode(v: t.Variable): s.Variable = programEncoder.decode(v)

  protected final def encode(e: s.Expr): t.Expr = programEncoder.encode(e)
  protected final def decode(e: t.Expr): s.Expr = programEncoder.decode(e)

  protected final def encode(tpe: s.Type): t.Type = programEncoder.encode(tpe)
  protected final def decode(tpe: t.Type): s.Type = programEncoder.decode(tpe)

  // generating Horn clauses

  type Guards = ListBuffer[Expr]
  type Clauses = ListBuffer[Clause]

  case class UnexpectedMatchError(expr: Expr) extends Exception(s"Unexpected match encountered on $expr.")

  private def canonicalType(tpe: Type): Type = 
    // partial map for canonicalization 
    def typeMap(tpe: Type): Option[Type] =
      tpe match
        case FunctionType(args, ret) =>
          Some(args.foldRight(ret) {(next, acc) => t.MapType(next, acc)})
        case _ => None
        
    // replace, then traverse
    typeOps.preMap(typeMap)(tpe)

  inline protected def registerPredicate(pred: Variable): Unit = 
    predicates += pred

  inline protected def registerValDef(vd: ValDef): Unit = 
    freeVariables += vd.toVariable

  /**
  * is this a "pure" value expression 
  * 
  * i.e. no language constructs that require their own predicates or guards.
  * so, no lets, no ifs, etc.
  */
  private def isSimpleValue(expr: Expr): Boolean = 
    expr match
      case Variable(_, tpe, _) => !tpe.isInstanceOf[FunctionType] 
      // anything that required the introduction of a predicate
      case Assume(_, _) => false
      case Let(_, _, _) => false
      case Application(_, _) => false
      case Lambda(_, _) => false 
      case Forall(_, _) => false
      case Choose(_, _) => false
      case IfExpr(_, _, _) => false
      case FunctionInvocation(_, _, args) => false // functions need to be replaced!
      // everything else, including theory operators && || ! ==> + - > < >= <= ==
      case Operator(args, _) => args.forall(isSimpleValue)
      case _ => throw UnexpectedMatchError(expr)

  /**
  * Generate a fresh predicate variable of given name and input type, and
  * register it as a predicate for the underlying solver.
  * @return fresh predicate variable
  **/
  private def generateFreshPredicate(name: String, inputType: Seq[Type]): Variable =
    val tpe = FunctionType(inputType, BooleanType())
    val pred = Variable.fresh(name, tpe, true)
    registerPredicate(pred)
    pred

  /**
    * Given an expression, construct a new predicate P and relevant clauses such that
    *
    * res == expr ==> P(res) (+ free variables)
    * 
    * Clauses may need recursive exploration and construction.
    * 
    * @return defining clauses, empty guards, and P(res)
    */
  private def makePredicate(expr: Expr, frees: Seq[Variable], res: Variable): (Clauses, Guards, Application) =
    val args = frees :+ res
    val inputType = args.map(_.tpe).map(canonicalType)
    val pred = generateFreshPredicate("ExprPred", inputType)
    val (clauses, guards, body) = makeExprClauses(expr)
    val aply = (x: Expr) => Application(pred, frees :+ x)
    
    // construct constraints
    val predClause = aply(res) :- (body(res) +: guards)

    (clauses :+ predClause, guards, aply(res))

  // TODO: Move

  val HOVarLookup: collection.mutable.Map[Variable, Expr] = collection.mutable.Map.empty
  val LambdaLookup: collection.mutable.Map[Lambda, (Clauses, Variable)] = collection.mutable.Map.empty

  /**
    * Recall or register the representation for an HOF variable
    *
    * @param v variable to replace
    * @return known repr. if available, or new registered repr. otherwise
    */
  private def makeHOFVariable(v: Variable): Expr = 
    require(v.tpe.isInstanceOf[FunctionType])
    HOVarLookup.getOrElseUpdate(v, Variable.fresh("HOF", canonicalType(v.tpe)))

  /**
    * Recall or register a lambda expression, clauses for its evaluation
    *
    * @param l
    * @return
    */
  private def makeLambda(l: Lambda): (Clauses, Variable) = 
    LambdaLookup.getOrElseUpdate(l, {
      val Lambda(args, body) = l
      val res = Variable.fresh("LambdaRes", canonicalType(l.getType))
      val applied = args.foldLeft(res: Expr)((acc, next) => MapApply(acc, next.toVariable))
      val (clauses, _, pred) = makePredicate(body, args.map(_.toVariable), res)
      clauses += pred :- Equals(res, applied)

      (clauses, res)
    })

  val assertions: collection.mutable.ListBuffer[Expr] = collection.mutable.ListBuffer.empty

  /**
    * Encode an expression, recursively generating clauses for its elaboration
    * into Horn clauses.
    *
    * Postconditions:
    * - clauses are not quantified, and are the responsibility of the top level
    *   callee
    * - guards must be accumulated into a top-level clause
    * - the body is conditionally valid under the guards
    * - the explicit (Inox) type of body 
    * - `\forall res: Expr. expr == res ==> body(res)`
    *
    * @param expr expression to encode
    * @return clauses generated by recursive elaboration
    * @return guards under which the body is valid
    * @return body predicate over expressions evaluating to input expr
    */
  private def makeExprClauses(expr: Expr): (Clauses, Guards, Expr => Expr) =
    val clauses = ListBuffer.empty[Clause]
    val guards = ListBuffer.empty[Expr]
    val freeVars = exprOps.variablesOf(expr).toSeq

    if isSimpleValue(expr) then
      // notably, only HOFs or simple expressions should introduce Equals
      return (clauses, guards, Equals(_, expr))

    // otherwise, need to elaborate
    expr match
      case v @ Variable(id, FunctionType(_, _), _) =>
        // other variable cases are simple expression, and covered above
        // return the HOF representation variable corresponding to this
        (clauses, guards, Equals(_, makeHOFVariable(v)))

      case Assume(cond, body) =>
        // expr == Assume(cond, body)
        // iff expr = body, under cond as a guard

        val newCond = 
          // condition appears in the guards, so we have to decide whether to elaborate or leave it
          if isSimpleValue(cond) then
            // condition is a theory expression, leave as is
            cond
          else
            // elaborate
            val (condClauses, condGuards, condPred) = makePredicate(cond, freeVars, Variable.fresh("AssumeCond", BooleanType()))
            clauses ++= condClauses
            guards ++= condGuards
            condPred

        guards += newCond

        assertions += cond
        
        val newBody = 
            // body is the target expression, it must always be elaborated
            val (bodyClauses, bodyGuards, bodyPred) = makePredicate(body, freeVars, Variable.fresh("AssumeBody", body.getType))
            clauses ++= bodyClauses
            guards ++= bodyGuards
            bodyPred

        // TODO: this can be cleaned up with a more principled way to generate predicates
        // it would require the callee to be more aware of the free variable order used for the predicate
        // but if that is the common use case, then maybe it should be the default w/o extraction
        val Application(pred, _) = newBody
        
        (clauses, guards, (e: Expr) => Application(pred, freeVars :+ e))
        
      case Choose(res, pred) => 
        // unexpected, what do we do regarding chooses? TODO: simply evaluate
        // under uninterpreted values or attempt to synthesize something in
        // their place?
        ???

      case Let(vd, value, body) =>
        // expr == let (vd = value) in body
        // iff expr = body under the guard that vd = value
        // vd = value becomes conditionOf(value)(vd)

        val cond = 
            val (valueClauses, valueGuards, valuePred) = makeExprClauses(value)
            clauses ++= valueClauses
            guards ++= valueGuards
            valuePred

        guards += cond(vd.toVariable)

        val bodyPred = 
            val (bodyClauses, bodyGuards, bodyPred) = makeExprClauses(body)
            clauses ++= bodyClauses
            guards ++= bodyGuards
            bodyPred
        
        (clauses, guards, bodyPred)

      case IfExpr(cond, thenn, elze) => 
        // expr == if cond then e1 else e2
        // iff expr == e1 under guard  cond
        // and expr == e2 under guard !cond

        val tpe = thenn.getType

        val condHolds = 
          // split on whether to elabroate cond
          if isSimpleValue(cond) then
            cond
          else
            val (condClauses, condGuards, condPred) = makePredicate(cond, freeVars, Variable.fresh("IfCond", BooleanType()))
            clauses ++= condClauses
            guards ++= condGuards
            condPred

        val condInv = Not(cond)

        // the encoding of the inverse of the condition can (should) involve a different predicate
        val condInvHolds = 
          // split on whether to elabroate cond
          if isSimpleValue(condInv) then
            condInv
          else
            val (condClauses, condGuards, condPred) = makePredicate(condInv, freeVars, Variable.fresh("IfCondInv", BooleanType()))
            clauses ++= condClauses
            guards ++= condGuards
            condPred

        val condLabel = Variable.fresh("IfInnerExpr", tpe)

        val (thennClauses, thennGuards, thennExpr) = makePredicate(thenn, freeVars, condLabel)
        val (elzeClauses, elzeGuards, elzeExpr) = makePredicate(elze, freeVars, condLabel)

        clauses ++= thennClauses
        clauses ++= elzeClauses

        // guards should not escape branches
        // guards ++= thennGuards
        // guards ++= elzeGuards

        // create a new predicate for this branch
        val newPred = generateFreshPredicate("IfBranch", (freeVars.map(_.tpe) :+ tpe).map(canonicalType))
        
        val branch: Expr => Expr = (res: Expr) => Application(newPred, freeVars :+ res)

        val positiveClause = branch(condLabel) .:- (thennExpr, condHolds)
        val negativeClause = branch(condLabel) .:- (elzeExpr, condInvHolds)
        
        clauses += positiveClause
        clauses += negativeClause

        (clauses, guards, branch)

      case Application(l @ Lambda(params, body), args) =>
        val fun = 
          val (funClauses, funGuards, funExpr) = makeExprClauses(l)
          clauses ++= funClauses
          guards ++= funGuards
          funExpr

        val funVar = Variable.fresh("fun", canonicalType(l.getType))
        guards += fun(funVar)

        val newArgs = args.map: a =>
          if isSimpleValue(a) then
            a
          else
            // register a new guard
            val newArg = Variable.fresh("arg", a.getType)
            val (predClauses, predGuards, pred) = makePredicate(a, freeVars, newArg)
            guards ++= predGuards
            clauses ++= predClauses
            newArg

        val applied = newArgs.foldLeft(funVar: Expr)((acc, next) => MapApply(acc, next))

        (clauses, guards, res => Equals(res, applied))

      case l @ Lambda(args, body) => 
        // eliminate it into an integer, and generate an applicative
        // predicate for it, if not already done
        val (definingClauses, identifier) = makeLambda(l)
        clauses ++= definingClauses
        (clauses, guards, Equals(_, l))
      
      case Forall(args, body) => 
        // Quantifier? Unexpected
        ???

      case FunctionInvocation(id, tps, args) if funReplacements.contains(id) =>
        // matched a known named function call (possibly (mutually) recursive)

        val functionIdentifer = funReplacements(id)
        val outType = expr.getType

        val newArgs = args.map: a =>
          if isSimpleValue(a) then
            a
          else
            // register a new guard
            val newArg = Variable.fresh("arg", a.getType)
            val (predClauses, predGuards, pred) = makePredicate(a, freeVars, newArg)
            guards ++= predGuards
            guards += pred
            clauses ++= predClauses
            newArg

        (clauses, guards, e => Application(functionIdentifer, newArgs :+ e))

      case Application(l : Variable, args) if l.tpe.isInstanceOf[FunctionType] =>
        // translate HOF applications to array selections
        val repr = makeHOFVariable(l)
        val selection = args.foldLeft(l: Expr)((acc, next) => MapApply(acc, next))
        (clauses, guards, Equals(_, selection))

      // handle booleans separately
      case Not(inner) =>
        val newRes = Variable.fresh("NotExpr", BooleanType())
        val (innerClauses, innerGuards, innerPred) = makeExprClauses(inner)
        clauses ++= innerClauses
        guards ++= innerGuards
        val newPred = generateFreshPredicate("NotExpr", (freeVars.map(_.tpe) :+ BooleanType()).map(canonicalType))
        clauses += Application(newPred, freeVars :+ newRes) :- (innerPred(Not(newRes)))
        (clauses, guards, res => Application(newPred, freeVars :+ res))

      case Or(inners) =>
        val newPred = generateFreshPredicate("OrExpr", (freeVars.map(_.tpe) :+ BooleanType()).map(canonicalType))
        inners.map(makeExprClauses).map: (innerClauses, innerGuards, innerPred) =>
          clauses ++= innerClauses
          // guards ++= innerGuards // guards should not escape branches?
          clauses += Application(newPred, freeVars :+ BooleanLiteral(true)) :- (innerPred(BooleanLiteral(true)) +: innerGuards)
        (clauses, guards, res => Application(newPred, freeVars :+ res))

      case And(inners) =>
        val newPred = generateFreshPredicate("AndExpr", (freeVars.map(_.tpe) :+ BooleanType()).map(canonicalType))
        val lhs = inners.map(makeExprClauses).flatMap: (innerClauses, innerGuards, innerPred) =>
          clauses ++= innerClauses
          innerGuards :+ innerPred(BooleanLiteral(true))
        clauses += Application(newPred, freeVars :+ BooleanLiteral(true)) :- lhs
        (clauses, guards, res => Application(newPred, freeVars :+ res))

      // other operator
      // deconstruct arguments similar to a function call
      case Operator(args, recons) => 
        val newArgs = args.map: a =>
          if isSimpleValue(a) then
            a
          else
            // register a new guard
            val newArg = Variable.fresh("arg", a.getType, true)
            val (predClauses, predGuards, pred) = makePredicate(a, freeVars, newArg)
            guards ++= predGuards
            guards += pred
            clauses ++= predClauses
            newArg

        val newExpr = recons(newArgs)
        val body = Equals(_, newExpr)

        (clauses, guards, body)
      
      case _ => throw UnexpectedMatchError(expr)

  private def extractModel(model: underlyingHorn.Model): Model = 
    ???

  private def reportInvariants(model: underlyingHorn.Model, targets: Map[Identifier, Variable]): Unit =
      context.reporter.info(
        s"Discovered Invariant for: $model"
      )

  protected def encodeFunction(tfd: TypedFunDef): Set[Expr] = 
    // collect data
    val body = tfd.fullBody
    val pred = funReplacements(tfd.id)
    val outType = tfd.returnType
    val args = tfd.params.map(_.toVariable)

    val res = Variable.fresh("res", outType)

    assertions.clear()

    // actually generate clauses
    val (clauses, guards, bodyPred) = makeExprClauses(body)

    val appliedFun: Encoded = Application(pred, args :+ res)

    val topClause = appliedFun :- (bodyPred(res) +: guards)

    // add goal clauses from top-level assertions
    assertions.foreach: a =>
      val (aClauses, aGuards, aPred) = makeExprClauses(Not(a))
      clauses ++= aClauses
      clauses += BooleanLiteral(false) :- (aPred(BooleanLiteral(true)) +: appliedFun +: (aGuards ++ guards))

    (topClause +: clauses).to(Set).map(_.collapse).map(quantify)

  protected def isFree(v: Variable): Boolean = 
    freeVariables.exists(_ == v) || predicates.exists(_ == v)

  protected def quantify(clause: Expr): Expr = 
    val frees = exprOps
                .variablesOf(clause)
                .filterNot(isFree)
                .map(_.toVal)
                .toSeq

    Forall(frees, clause)    

  /* Communicate with solver */

  protected lazy val emptyModel: underlyingHorn.Model = 
    inox.Model(targetProgram)(Map.empty, Map.empty)
    // underlyingHorn.checkAssumptions(SolverResponses.Model)(Set.empty) match
    //   case SolverResponses.SatWithModel(model) => model
    //   case _ => throw new Exception("Could not construct empty model.")

  protected def emptyProgramModel: Model = 
    inox.Model(program)(Map.empty, Map.empty)

  private def encodeAssumptions(assumptions: Set[Source]): Set[Encoded] = 
    assumptions
      .map(encode)
      .map(makeExprClauses)
      .flatMap {
        (clauses, guards, predicate) =>
          // false :- !assumption /\ guards
          val topClause = 
            BooleanLiteral(false) :- (predicate(BooleanLiteral(true)) +: guards)
          clauses += topClause
          clauses
      }
      .map(_.collapse)
      .map(quantify)

  private def encodeFunctionsForAssumptions(assumptions: Set[Source]): Set[Encoded] = 
    // all functions that appear in the assumptions, transitively
    val functions = assumptions
                      .map(encode)
                      .flatMap(exprOps.functionCallsOf)
                      .map(_.id)
                      .filter(funReplacements.contains)
                      .flatMap(program.symbols.callGraph.transitiveSucc)

    // generate the clauses for these functions
    functions.flatMap: id =>
      val tfd = targetProgram.symbols.getFunction(id)
      encodeFunction(tfd.typed(using targetProgram.symbols))

  /**
    * Invariant-generating implementation of [[checkAssumptions]].
    */
  private def checkAssumptions_(config: Configuration)(assumptions: Set[Source]): config.Response[Model, Assumptions] = 

    // send constraints to solver
    val totalAssumptions = assumptions ++ constraints

    // Horn encode assumptions
    val assumptionClauses = encodeAssumptions(totalAssumptions)

    // find and encode all function calls (recursively)
    val definitionClauses = encodeFunctionsForAssumptions(totalAssumptions)
    
    // declare variables
    predicates.foreach(underlyingHorn.registerPredicate)

    (assumptionClauses ++ definitionClauses).foreach(underlyingHorn.assertCnstr)
    
    // check satisfiability
    val underlyingResult = underlyingHorn.checkAssumptions(config)(Set.empty)

    // interpret result
    val res = 
      underlyingResult match
        case SolverResponses.SatWithModel(model) =>
          // report discovery of invariants
          reportInvariants(model, funReplacements)
          // discard underlying model. We cannot (in general) construct a program
          // model from the Horn model 
          config.cast(SolverResponses.Unsat)
        case SolverResponses.Unknown => config.cast(SolverResponses.Unknown)
        case SolverResponses.Check(r) => config.cast(if r then SolverResponses.Unsat else SolverResponses.SatWithModel(emptyProgramModel))

    res

end AbstractInvariantSolver
