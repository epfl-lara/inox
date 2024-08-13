package inox
package solvers
package invariant

import inox.solvers.SolverResponses.CheckConfiguration

import inox.solvers.SolverResponses.Configuration
import scala.collection.mutable.ListBuffer
import inox.utils.IncrementalSeq
import inox.solvers.smtlib.SMTLIBSolver
import scala.collection.immutable.LazyList.cons
import inox.utils.IncrementalBijection

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
        // choose HOF representation
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

  object Context:
    import collection.mutable.{Map => MMap}

    // guards corresponding to variables
    private val variableGuards: MMap[Variable, List[Expr]] = MMap.empty
    private val functionReplacements: IncrementalBijection[TypedFunDef, Expr] = IncrementalBijection()
    private val functionClauses: MMap[TypedFunDef, Set[Expr]] = MMap.empty
    private val callReplacements: IncrementalBijection[Variable, FunctionInvocation] = IncrementalBijection()

    def functionOf(v: Variable): Option[FunctionInvocation] = 
      callReplacements.getB(v)

    def isFunctionalPredicate(v: Variable): Boolean = 
      functionReplacements.containsB(v)

    def predicateOf(tfd: TypedFunDef): Expr = 
      functionReplacements.cachedB(tfd) {
        // this is an unseen typed def, generate a new predicate and clause set
        // also populate the defining clauses
        val funTpe = tfd.functionType
        val pred = generateFreshPredicate(tfd.id.name, (funTpe.from :+ funTpe.to).map(canonicalType))
        pred
      }

    def definingClauses(tfd: TypedFunDef): Set[Expr] = 
      if functionClauses.contains(tfd) then
        functionClauses(tfd)
      else
        // unseen def. Unusual but ok.
        generateClauses(tfd) // force generation
        definingClauses(tfd)
    
    private def generateClauses(tfd: TypedFunDef): Unit = 
      val clauses = encodeFunction(tfd)
      functionClauses(tfd) = clauses

    def addGuard(v: Variable, guard: Expr): Unit = 
      variableGuards(v) = guard :: variableGuards.getOrElse(v, Nil)

    def addCallGuard(v: Variable, call: FunctionInvocation): Unit = 
      callReplacements += v -> call

    def guardFor(v: Variable): List[Expr] = 
      val call = callReplacements.getB(v)
      val callGuard = 
        if call.isDefined then
          val tfd = targetProgram.symbols.getFunction(call.get.id).typed(call.get.tps)
          val pred = predicateOf(tfd)
          List(Application(pred, call.get.args :+ v))
        else
          Nil
      callGuard ++ variableGuards.getOrElse(v, Nil)

    def transitiveVarsFor(v: Variable): Set[Variable] =
      def rec(vs: Set[Variable]) =
        vs.flatMap(guardFor)
          .flatMap(exprOps.variablesOf)
          .filterNot(isFree) 
      utils.fixpoint(rec)(Set(v))

    def toReplace(id: Identifier): Boolean =
      targetProgram.symbols.functions.contains(id)

    def freshFunctionReplacement(fn: FunctionInvocation): Variable =
      callReplacements.cachedA(fn){
        val tpe = fn.getType
        val fresh = Variable.fresh(s"${fn.id}_call", tpe, true)
        addCallGuard(fresh, fn)
        fresh        
      }

    def insertGuards(clause: Clause): Clause =
      val exprs = clause.body.filter(isSimpleValue)
      val variables = exprs.flatMap(exprOps.variablesOf)
      val newGuards = variables.flatMap(guardFor)
      clause.withGuards(newGuards)


  /**
    * "Purify" an expression by replacing function invocations with fresh
    * variables and registering guards for the variables as predicate
    * invocations.
    *
    * @param expr expression to purify
    */
  private def purify(expr: Expr): Expr =
      def _purify(expr: Expr): Option[Expr] = 
        expr match
          case fn @ FunctionInvocation(id, _, _) if Context.toReplace(id) =>
            Some(Context.freshFunctionReplacement(fn))
          case _ => None
        
      exprOps.postMap(_purify)(expr)

  private case class ClauseResult(clauses: Clauses, guards: Guards, assertions: ListBuffer[List[Expr]],  body: Expr => Expr)

  private inline def conjunction(exprs: Iterable[Expr]): Expr = 
    if exprs.isEmpty then BooleanLiteral(true)
    else if exprs.tail.isEmpty then exprs.head
    else And(exprs.toSeq)

  private def freeVariablesOf(expr: Expr): Seq[Variable] =
    val baseFrees = exprOps.variablesOf(expr)
    val guardFrees = baseFrees
                      .flatMap(Context.transitiveVarsFor)
                      .flatMap(exprOps.variablesOf)
                      .filterNot(isFree)
    (baseFrees ++ guardFrees).toSeq

  /**
    * Given an expression, construct a new predicate P and relevant clauses such that
    *
    * res == expr ==> P(res) (+ free variables)
    * 
    * Clauses may need recursive exploration and construction.
    * 
    * @return defining clauses, empty guards, and P(res)
    */
  private def generatePredicate(name: String, expr: Expr, pathCondition: List[Expr]): ClauseResult =
    val res = Variable.fresh("res", expr.getType)
    val frees = freeVariablesOf(expr)
    val args = frees :+ res
    val inputType = args.map(_.tpe).map(canonicalType)
    val pred = generateFreshPredicate(name, inputType)
    val inner = encodeClauses(expr, pathCondition)
    val aply = (x: Expr) => Application(pred, frees :+ x)
    
    // construct constraints
    val predClause = aply(res) :- (inner.body(res) +: inner.guards)

    // guards do not escape predicate definitions
    ClauseResult(inner.clauses :+ predClause, ListBuffer.empty, inner.assertions, aply)

  private def encodeClauses(expr: Expr, pathCondition: List[Expr]): ClauseResult =
    val clauses = ListBuffer.empty[Clause]
    val guards = ListBuffer.empty[Expr]
    val assertions = ListBuffer.empty[List[Expr]]
    val freeVars = freeVariablesOf(expr)

    inline def ret(body: Expr => Expr) = ClauseResult(clauses, guards, assertions, body)
    inline def subsume(inner: ClauseResult): Unit =
      clauses ++= inner.clauses
      guards ++= inner.guards
      assertions ++= inner.assertions

    if isSimpleValue(expr) then
      // notably, only HOFs or simple expressions should introduce Equals
      return ret(Equals(_, expr))

    // otherwise, need to elaborate
    expr match
      case v @ Variable(id, FunctionType(_, _), _) =>
        // other variable cases are simple expression, and covered above
        // return the HOF representation variable corresponding to this
        ret(Equals(_, makeHOFVariable(v)))

      case Assume(cond, body) =>
        // expr == Assume(cond, body)
        // iff expr = body, under cond as a guard

        // condition appears in the guards, so we have to decide whether to elaborate or leave it
        val newCond =
          if isSimpleValue(cond) then
            // condition is a theory expression, leave as is
            cond
          else
            // elaborate
            val innerCond = generatePredicate("AssumeCond", cond, pathCondition)
            subsume(innerCond)
            innerCond.body(BooleanLiteral(true))

        val invCond =
          val ncond = Not(cond)
          if isSimpleValue(ncond) then
            // condition is a theory expression, leave as is
            ncond
          else
            // elaborate
            val innerCond = generatePredicate("NegatedAssumeCond", ncond, pathCondition)
            subsume(innerCond)
            innerCond.body(BooleanLiteral(true))

        guards += newCond
        assertions += invCond :: pathCondition

        val newBody = 
            // body is the target expression, it must always be elaborated
            val bodyRes = encodeClauses(body, newCond :: pathCondition)
            subsume(bodyRes)
            bodyRes.body

        val res = Variable.fresh("AssumeExpr", expr.getType)
        val pred = generateFreshPredicate("AssumeExpr", (freeVars.map(_.tpe) :+ res.getType).map(canonicalType))
        val topClause = Application(pred, freeVars :+ res) .:- (newCond, newBody(res))
        clauses += topClause
        
        ret(res => Application(pred, freeVars :+ res))
        
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
            val inner = generatePredicate("LetInnerValue", value, pathCondition)
            subsume(inner)
            inner.body

        Context.addGuard(vd.toVariable, cond(vd.toVariable))

        val bodyPred = 
            val inner = encodeClauses(body, pathCondition)
            subsume(inner)
            inner.body

        ret(bodyPred)

      case IfExpr(cond, thenn, elze) => 
        // expr == if cond then e1 else e2
        // iff expr == e1 under guard  cond
        // and expr == e2 under guard !cond

        val tpe = thenn.getType

        val condHolds = 
          // split on whether to elaborate cond
          if isSimpleValue(cond) then
            cond
          else
            val inner = generatePredicate("IfCond", cond, pathCondition)
            subsume(inner)
            inner.body(BooleanLiteral(true))

        val condInv = Not(cond)

        // the encoding of the inverse of the condition can (should) involve a different predicate
        val condInvHolds = 
          // split on whether to elaborate cond
          if isSimpleValue(condInv) then
            condInv
          else
            val inner = generatePredicate("NegatedIfCond", condInv, pathCondition)
            subsume(inner)
            inner.body(BooleanLiteral(true))

        val condLabel = Variable.fresh("IfCondition", tpe)

        val thennResult = generatePredicate("ThenBranch", thenn, condHolds :: pathCondition)
        val elzeResult = generatePredicate("ElseBranch", elze, condInvHolds :: pathCondition)

        subsume(thennResult)
        subsume(elzeResult)

        // create a new predicate for this branch
        val newPred = generateFreshPredicate("IfNode", (freeVars.map(_.tpe) :+ tpe).map(canonicalType))
        
        val branch: Expr => Expr = (res: Expr) => Application(newPred, freeVars :+ res)

        val positiveClause = branch(condLabel) .:- (thennResult.body(condLabel), condHolds)
        val negativeClause = branch(condLabel) .:- (elzeResult.body(condLabel), condInvHolds)
        
        clauses += positiveClause
        clauses += negativeClause

        ret(branch)

      case Application(l @ Lambda(params, body), args) =>
        val fun = 
          val inner = encodeClauses(l, pathCondition)
          subsume(inner)
          inner.body

        val funVar = Variable.fresh("fun", canonicalType(l.getType))
        Context.addGuard(funVar, fun(funVar))

        val newArgs = args.map: a =>
          if isSimpleValue(a) then
            a
          else
            // register a new guard
            val newArg = Variable.fresh("arg", a.getType)
            val inner = generatePredicate("LambdaArg", a, pathCondition)
            subsume(inner)
            Context.addGuard(newArg, inner.body(newArg))
            newArg

        val applied = newArgs.foldLeft(funVar: Expr)((acc, next) => MapApply(acc, next))

        ret(Equals(_, applied))

      case l @ Lambda(args, body) => 
        // eliminate it into an integer, and generate an applicative
        // predicate for it, if not already done
        val (definingClauses, identifier) = makeLambda(l)
        clauses ++= definingClauses
        ret(Equals(_, l))
      
      case Forall(args, body) => 
        // Quantifier? Unexpected
        ???

      case FunctionInvocation(id, tps, args) if funReplacements.contains(id) =>
        // this expression should have been purified
        throw UnexpectedMatchError(expr)

      case Application(l : Variable, args) if l.tpe.isInstanceOf[FunctionType] =>
        // translate HOF applications to array selections
        val repr = makeHOFVariable(l)

        val newArgs = args.map: a =>
          if isSimpleValue(a) then
            a
          else
            // register a new guard
            val newArg = Variable.fresh("arg", a.getType)
            val inner = generatePredicate("HOFArg", a, pathCondition)
            subsume(inner)
            Context.addGuard(newArg, inner.body(newArg))
            newArg

        val applied = newArgs.foldLeft(repr: Expr)((acc, next) => MapApply(acc, next))

        ret(Equals(_, applied))

      // handle booleans separately
      case Not(inner) =>
        val newRes = Variable.fresh("NotExpr", BooleanType())
        val innerResult = encodeClauses(inner, pathCondition)
        subsume(innerResult)

        val newPred = generateFreshPredicate("NotExpr", (freeVars.map(_.tpe) :+ BooleanType()).map(canonicalType))
        clauses += Application(newPred, freeVars :+ newRes) :- (innerResult.body(Not(newRes)))

        ret(res => Application(newPred, freeVars :+ res))

      case Or(inners) =>
        val newPred = generateFreshPredicate("OrExpr", (freeVars.map(_.tpe) :+ BooleanType()).map(canonicalType))
        inners
          .map(encodeClauses(_, pathCondition))
          .map: inner =>
            subsume(inner)
            clauses += Application(newPred, freeVars :+ BooleanLiteral(true)) :- (inner.body(BooleanLiteral(true)) +: inner.guards)

        ret(res => Application(newPred, freeVars :+ res))

      case And(inners) =>
        val newPred = generateFreshPredicate("AndExpr", (freeVars.map(_.tpe) :+ BooleanType()).map(canonicalType))
        val lhs = inners
          .map(encodeClauses(_, pathCondition))
          .map: inner =>
            subsume(inner)
            inner.body(BooleanLiteral(true))

        clauses += Application(newPred, freeVars :+ BooleanLiteral(true)) :- (lhs ++ guards)

        ret(res => Application(newPred, freeVars :+ res))

      // other operator
      // deconstruct arguments similar to a function call
      case Operator(args, recons) => 
        val newArgs = args.map: a =>
          if isSimpleValue(a) then
            a
          else
            // register a new guard
            val newArg = Variable.fresh("arg", a.getType, true)
            val inner = generatePredicate("OperatorArg", a, pathCondition)
            subsume(inner)
            Context.addGuard(newArg, inner.body(newArg))
            newArg

        val newExpr = recons(newArgs)
        val body = Equals(_, newExpr)

        ret(body)
      
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
      val inner = generatePredicate("LambdaBody", body, List.empty) // lambdas should not be conditionally valid?
      val topClause = inner.body(res) :- Equals(res, applied)

      (inner.clauses :+ topClause, res)
    })

  private def extractModel(model: underlyingHorn.Model): Model = 
    ???

  private def reportInvariants(model: underlyingHorn.Model): Unit =
      context.reporter.info(
        s"Discovered Invariant for: $model"
      )

  protected def encodeFunction(tfd: TypedFunDef): Set[Expr] = 
    // collect data
    val body = purify(tfd.fullBody)
    val pred = Context.predicateOf(tfd)
    val outType = tfd.returnType
    val args = tfd.params.map(_.toVariable)

    val res = Variable.fresh("res", outType)

    // actually generate clauses
    val ClauseResult(clauses, guards, assertions, inner) = encodeClauses(body, List.empty)

    val appliedFun: Encoded = Application(pred, args :+ res)

    val topClause = appliedFun :- inner(res)

    // add goal clauses from top-level assertions
    assertions.foreach: as =>
      clauses += (BooleanLiteral(false) :- (appliedFun +: as))

    (topClause +: clauses)
      .to(Set)
      .map(Context.insertGuards)
      .map(_.collapse)
      .map(quantify)

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
      .map(purify)
      .map(encodeClauses(_, List.empty))
      .flatMap {
        case ClauseResult(clauses, guards, assertions, predicate) =>
          // false :- assumption /\ guards
          val topClause = BooleanLiteral(false) :- (predicate(BooleanLiteral(true)) +: guards)

          clauses += topClause

          // do we ever expect these to be non-empty? Don't think so
          // your assertions should not come with assume statements inside them
          assert(assertions.isEmpty)

          // assertions.foreach: conds => // SHOULD be empty though? FIXME: ?
          //   clauses += (BooleanLiteral(false) :- conds)

          clauses
      }
      .map(Context.insertGuards)
      .map(_.collapse)
      .map(quantify)

  private def encodeFunctionsForAssumptions(assumptions: Set[Source]): Set[Encoded] = 
    // all functions that appear in the assumptions, transitively
    val baseCalls = assumptions
                      .map(encode)
                      .flatMap(exprOps.functionCallsOf)
                      .filter(f => Context.toReplace(f.id))

    def transitiveCalls(calls: Set[FunctionInvocation]): Set[FunctionInvocation] = 
      calls.flatMap: call =>
        val funDef = targetProgram.symbols.getFunction(call.id)
        val typedDef = funDef.typed(call.tps)
        val body = typedDef.fullBody
        val newCalls = exprOps.functionCallsOf(body)
                        .filter(f => Context.toReplace(f.id))
        newCalls + call

    // termination is guaranteed by Stainless' type checking beforehand
    val calls = utils.fixpoint(transitiveCalls)(baseCalls)

    calls
      .flatMap: call =>
        val funDef = targetProgram.symbols.getFunction(call.id)
        val typedDef = funDef.typed(call.tps)
        Context.definingClauses(typedDef)

  /**
    * Does the model set any predicates arising from a function to false?
    * 
    * This means that no function calls succeed in satisfying the internal assertions.
    *
    * @param model model to check
    */
  private def nonVacuousModel(model: underlyingHorn.Model): Boolean = 
    !model.vars.exists: (v, expr) => 
      println(s"CHECKING $v for $expr")
      println(s"IS FUNCTION? ${Context.isFunctionalPredicate(v.toVariable)}")
      Context.isFunctionalPredicate(v.toVariable) && expr == BooleanLiteral(false)

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
          reportInvariants(model)
          // discard underlying model. We cannot (in general) construct a program
          // model from the Horn model 
          if nonVacuousModel(model) then
            config.cast(SolverResponses.Unsat)
          else
            config.cast(SolverResponses.SatWithModel(emptyProgramModel))

        case SolverResponses.Check(r) => config.cast(if r then SolverResponses.Unsat else SolverResponses.SatWithModel(emptyProgramModel))

        case _ => config.cast(SolverResponses.Unknown) // unknown or unreachable

    res

end AbstractInvariantSolver
