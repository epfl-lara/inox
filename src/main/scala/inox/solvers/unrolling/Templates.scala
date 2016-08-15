/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

import scala.collection.generic.CanBuildFrom

trait Templates extends TemplateGenerator
                   with FunctionTemplates
                   with DatatypeTemplates
                   with LambdaTemplates
                   with QuantificationTemplates
                   with IncrementalStateWrapper {

  val program: Program
  import program._
  import program.trees._
  import program.symbols._

  type Encoded

  def asString(e: Encoded): String

  def encodeSymbol(v: Variable): Encoded
  def mkEncoder(bindings: Map[Variable, Encoded])(e: Expr): Encoded
  def mkSubstituter(map: Map[Encoded, Encoded]): Encoded => Encoded

  def mkNot(e: Encoded): Encoded
  def mkOr(es: Encoded*): Encoded
  def mkAnd(es: Encoded*): Encoded
  def mkEquals(l: Encoded, r: Encoded): Encoded
  def mkImplies(l: Encoded, r: Encoded): Encoded

  private[unrolling] lazy val trueT = mkEncoder(Map.empty)(BooleanLiteral(true))

  private var currentGen: Int = 0
  protected def currentGeneration: Int = currentGen
  protected def nextGeneration(gen: Int): Int = gen + 5

  trait Manager extends IncrementalStateWrapper {
    def unrollGeneration: Option[Int]

    def unroll: Clauses
    def satisfactionAssumptions: Seq[Encoded]
    def refutationAssumptions: Seq[Encoded]
    def promoteBlocker(b: Encoded): Boolean
  }

  private val managers: Seq[Manager] = Seq(
    functionsManager,
    datatypesManager,
    lambdasManager,
    quantificationsManager
  )

  def canUnroll: Boolean = managers.exists(_.unrollGeneration.isDefined)
  def unroll: Clauses = {
    assert(canUnroll, "Impossible to unroll further")
    val generation = managers.flatMap(_.unrollGeneration).min
    if (generation > currentGen) {
      currentGen = generation
    }

    managers.flatMap(_.unroll)
  }

  def satisfactionAssumptions = managers.flatMap(_.satisfactionAssumptions)
  def refutationAssumptions = managers.flatMap(_.refutationAssumptions)

  private val condImplies = new IncrementalMap[Encoded, Set[Encoded]].withDefaultValue(Set.empty)
  private val condImplied = new IncrementalMap[Encoded, Set[Encoded]].withDefaultValue(Set.empty)
  private val condEquals  = new IncrementalBijection[Encoded, Set[Encoded]]

  val incrementals: Seq[IncrementalState] = managers ++ Seq(condImplies, condImplied, condEquals)

  protected def freshConds(
    pathVar: Encoded,
    condVars: Map[Variable, Encoded],
    tree: Map[Variable, Set[Variable]]): Map[Encoded, Encoded] = {

    val subst = condVars.map { case (v, idT) => idT -> encodeSymbol(v) }
    val mapping = condVars.mapValues(subst)

    for ((parent, children) <- tree) {
      mapping.get(parent) match {
        case None => // enabling condition, corresponds to pathVar
          for (child <- children) {
            val ec = mapping(child)
            condImplied += ec -> (condImplies(ec) + pathVar)
          }

        case Some(ep) =>
          for (child <- children) {
            val ec = mapping(child)
            condImplies += ep -> (condImplies(ep) + ec)
            condImplied += ec -> (condImplied(ec) + ep)
          }
      }
    }

    subst
  }

  private val sym = Variable(FreshIdentifier("bs", true), BooleanType)
  protected def encodeBlockers(bs: Set[Encoded]): (Encoded, Clauses) = bs.toSeq match {
    case Seq(b) if condImplies.isDefinedAt(b) || condImplied.isDefinedAt(b) || condEquals.containsA(b) =>
      (b, Seq.empty)

    case _ =>
      val flatBs = fixpoint((bs: Set[Encoded]) => bs.flatMap(b => condEquals.getBorElse(b, Set(b))))(bs)
      condEquals.getA(flatBs) match {
        case Some(b) => (b, Seq.empty)
        case None =>
          val b = encodeSymbol(sym)
          condEquals += (b -> flatBs)
          (b, Seq(mkEquals(b, if (flatBs.isEmpty) trueT else mkAnd(flatBs.toSeq : _*))))
      }
  }

  protected def blockerParents(b: Encoded): Set[Encoded] = condImplied(b)
  protected def blockerChildren(b: Encoded): Set[Encoded] = condImplies(b)

  def promoteBlocker(b: Encoded, force: Boolean = false): Boolean = {
    var seen: Set[Encoded] = Set.empty
    var promoted: Boolean = false
    var blockers: Seq[Set[Encoded]] = Seq(Set(b))

    do {
      val (bs +: rest) = blockers
      blockers = rest

      val next = (for (b <- bs if !seen(b)) yield {
        seen += b

        for (manager <- managers) {
          val p = manager.promoteBlocker(b)
          promoted = promoted || p
        }

        if (force) {
          blockerChildren(b)
        } else {
          Seq.empty[Encoded]
        }
      }).flatten

      if (next.nonEmpty) blockers :+= next
    } while (!promoted && blockers.nonEmpty)

    promoted
  }

  implicit val debugSection = DebugSectionSolver

  type Arg = Either[Encoded, Matcher]

  implicit class ArgWrapper(arg: Arg) {
    def encoded: Encoded = arg match {
      case Left(value) => value
      case Right(matcher) => matcher.encoded
    }

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): Arg = arg match {
      case Left(v) => msubst.get(v) match {
        case Some(m) => Right(m)
        case None => Left(substituter(v))
      }
      case Right(m) => Right(m.substitute(substituter, msubst))
    }
  }

  /** Represents a named function call in the unfolding procedure */
  case class Call(tfd: TypedFunDef, args: Seq[Arg]) {
    override def toString = {
      tfd.signature + args.map {
        case Right(m) => m.toString
        case Left(v) => asString(v)
      }.mkString("(", ", ", ")")
    }

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): Call = copy(
      args = args.map(_.substitute(substituter, msubst))
    )
  }

  /** Represents an application of a first-class function in the unfolding procedure */
  case class App(caller: Encoded, tpe: FunctionType, args: Seq[Arg], encoded: Encoded) {
    override def toString: String =
      "(" + asString(caller) + " : " + tpe.asString + ")" + args.map(a => asString(a.encoded)).mkString("(", ",", ")")

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): App = copy(
      caller = substituter(caller),
      args = args.map(_.substitute(substituter, msubst)),
      encoded = substituter(encoded)
    )
  }

  /** Represents an E-matching matcher that will be used to instantiate relevant quantified propositions */
  case class Matcher(key: Either[(Encoded, Type), TypedFunDef], args: Seq[Arg], encoded: Encoded) {
    override def toString: String = (key match {
      case Left((c, tpe)) => asString(c)
      case Right(tfd) => tfd.signature
    }) + args.map {
      case Right(m) => m.toString
      case Left(v) => asString(v)
    }.mkString("(", ",", ")")

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): Matcher = copy(
      key = key.left.map(p => substituter(p._1) -> p._2),
      args = args.map(_.substitute(substituter, msubst)),
      encoded = substituter(encoded)
    )
  }


  /** Template instantiations
    *
    * [[Template]] instances, when provided with concrete arguments and a
    * blocker, will generate three outputs used for program unfolding:
    * - clauses: clauses that will be added to the underlying solver
    * - call blockers: bookkeeping information necessary for named
    *                  function unfolding
    * - app blockers: bookkeeping information necessary for first-class
    *                 function unfolding
    *
    * This object provides helper methods to deal with the triplets
    * generated during unfolding.
    */
  type Clauses       = Seq[Encoded]
  type CallBlockers  = Map[Encoded, Set[Call]]
  type AppBlockers   = Map[(Encoded, App), Set[TemplateAppInfo]]

  implicit class MapSetWrapper[A,B](map: Map[A,Set[B]]) {
    def merge(that: Map[A,Set[B]]): Map[A,Set[B]] = (map.keys ++ that.keys).map { k =>
      k -> (map.getOrElse(k, Set.empty) ++ that.getOrElse(k, Set.empty))
    }.toMap
  }

  implicit class MapSeqWrapper[A,B](map: Map[A,Seq[B]]) {
    def merge(that: Map[A,Seq[B]]): Map[A,Seq[B]] = (map.keys ++ that.keys).map { k =>
      k -> (map.getOrElse(k, Seq.empty) ++ that.getOrElse(k, Seq.empty)).distinct
    }.toMap
  }

  /** Abstract templates
    *
    * Pre-compiled sets of clauses with extra bookkeeping information that enables
    * efficient unfolding of function calls and applications.
    * [[Template]] is a super-type for all such clause sets that can be instantiated
    * given a concrete argument list and a blocker in the decision-tree.
    */
  type Apps      = Map[Encoded, Set[App]]
  type Calls     = Map[Encoded, Set[Call]]
  type Matchers  = Map[Encoded, Set[Matcher]]

  trait Template { self =>
    val pathVar : (Variable, Encoded)
    val args    : Seq[Encoded]

    val condVars : Map[Variable, Encoded]
    val exprVars : Map[Variable, Encoded]
    val condTree : Map[Variable, Set[Variable]]

    val clauses      : Clauses
    val blockers     : Calls
    val applications : Apps
    val matchers     : Matchers

    val lambdas         : Seq[LambdaTemplate]
    val quantifications : Seq[QuantificationTemplate]

    lazy val start = pathVar._2

    def instantiate(aVar: Encoded, args: Seq[Arg]): Clauses = {
      val (substMap, clauses) = Template.substitution(
        condVars, exprVars, condTree, lambdas, quantifications,
        (this.args zip args).toMap + (start -> Left(aVar)), pathVar._1, aVar)
      clauses ++ instantiate(substMap)
    }

    protected def instantiate(substMap: Map[Encoded, Arg]): Clauses =
      Template.instantiate(clauses, blockers, applications, matchers, substMap)

    override def toString : String = "Instantiated template"
  }

  private[unrolling] def mkApplication(caller: Expr, args: Seq[Expr]): Expr = caller.getType match {
    case FunctionType(from, to) =>
      val (curr, next) = args.splitAt(from.size)
      mkApplication(Application(caller, curr), next)
    case _ =>
      assert(args.isEmpty, s"Non-function typed $caller applied to ${args.mkString(",")}")
      caller
  }

  object Template {

    def encode(
      pathVar: (Variable, Encoded),
      arguments: Seq[(Variable, Encoded)],
      condVars: Map[Variable, Encoded],
      exprVars: Map[Variable, Encoded],
      guardedExprs: Map[Variable, Seq[Expr]],
      lambdas: Seq[LambdaTemplate],
      quantifications: Seq[QuantificationTemplate],
      substMap: Map[Variable, Encoded] = Map.empty[Variable, Encoded],
      optCall: Option[TypedFunDef] = None,
      optApp: Option[(Encoded, FunctionType)] = None
    ) : (Clauses, Calls, Apps, Matchers, () => String) = {

      val idToTrId : Map[Variable, Encoded] =
        condVars ++ exprVars + pathVar ++ arguments ++ substMap ++
        lambdas.map(_.ids) ++ quantifications.flatMap(_.mapping)

      val encoder : Expr => Encoded = mkEncoder(idToTrId)

      val optIdCall = optCall.map(tfd => Call(tfd, arguments.map(p => Left(p._2))))
      val optIdApp = optApp.map { case (idT, tpe) =>
        val v = Variable(FreshIdentifier("x", true), tpe)
        val encoded = mkEncoder(Map(v -> idT) ++ arguments)(mkApplication(v, arguments.map(_._1)))
        App(idT, bestRealType(tpe).asInstanceOf[FunctionType], arguments.map(p => Left(p._2)), encoded)
      }

      lazy val optIdMatcher = optCall.map { tfd =>
        val (fiArgs, appArgs) = arguments.map(_._1).splitAt(tfd.params.size)
        val encoded = mkEncoder(arguments.toMap)(mkApplication(tfd.applied(fiArgs), appArgs))
        Matcher(Right(tfd), arguments.map(p => Left(p._2)), encoded)
      }

      val (clauses, blockers, applications, matchers) = {
        var clauses      : Clauses = Seq.empty
        var blockers     : Map[Variable, Set[Call]]    = Map.empty
        var applications : Map[Variable, Set[App]]     = Map.empty
        var matchers     : Map[Variable, Set[Matcher]] = Map.empty

        for ((b,es) <- guardedExprs) {
          var funInfos   : Set[Call]    = Set.empty
          var appInfos   : Set[App]     = Set.empty
          var matchInfos : Set[Matcher] = Set.empty

          for (e <- es) {
            val exprToMatcher = exprOps.fold[Map[Expr, Matcher]] { (expr, res) =>
              val result = res.flatten.toMap

              result ++ (expr match {
                case QuantificationMatcher(c, args) =>
                  // Note that we rely here on the fact that foldRight visits the matcher's arguments first,
                  // so any Matcher in arguments will belong to the `result` map
                  val encodedArgs = args.map(arg => result.get(arg) match {
                    case Some(matcher) => Right(matcher)
                    case None => Left(encoder(arg))
                  })

                  Some(expr -> Matcher(Left(encoder(c) -> bestRealType(c.getType)), encodedArgs, encoder(expr)))
                case _ => None
              })
            }(e)

            def encodeArg(arg: Expr): Arg = exprToMatcher.get(arg) match {
              case Some(matcher) => Right(matcher)
              case None => Left(encoder(arg))
            }

            funInfos ++= firstOrderCallsOf(e).map { case (id, tps, args) =>
              Call(getFunction(id, tps), args.map(encodeArg))
            }

            appInfos ++= firstOrderAppsOf(e).map { case (c, args) =>
              val tpe = bestRealType(c.getType).asInstanceOf[FunctionType]
              App(encoder(c), tpe, args.map(encodeArg), encoder(mkApplication(c, args)))
            }

            matchInfos ++= exprToMatcher.values
            clauses :+= encoder(Implies(b, e))
          }

          val calls = funInfos.filter(i => Some(i) != optIdCall)
          if (calls.nonEmpty) blockers += b -> calls

          val apps = appInfos.filter(i => Some(i) != optIdApp)
          if (apps.nonEmpty) applications += b -> apps

          val matchs = matchInfos.filter { case m @ Matcher(_, _, menc) =>
            !optIdApp.exists { case App(_, _, _, aenc) => menc == aenc }
          }

          if (matchs.nonEmpty) matchers += b -> matchs
        }

        (clauses, blockers, applications, matchers merge optIdMatcher.map(m => pathVar._1 -> Set(m)).toMap)
      }

      val encodedBlockers : Calls    = blockers.map(p => idToTrId(p._1) -> p._2)
      val encodedApps     : Apps     = applications.map(p => idToTrId(p._1) -> p._2)
      val encodedMatchers : Matchers = matchers.map(p => idToTrId(p._1) -> p._2)

      val stringRepr : () => String = () => {
        " * Activating boolean : " + pathVar._1 + "\n" +
        " * Control booleans   : " + condVars.keys.mkString(", ") + "\n" +
        " * Expression vars    : " + exprVars.keys.mkString(", ") + "\n" +
        " * Clauses            : " + (if (guardedExprs.isEmpty) "\n" else {
          "\n   " + (for ((b,es) <- guardedExprs; e <- es) yield (b + " ==> " + e)).mkString("\n   ") + "\n"
        }) +
        " * Invocation-blocks  :" + (if (blockers.isEmpty) "\n" else {
          "\n   " + blockers.map(p => p._1 + " ==> " + p._2).mkString("\n   ") + "\n"
        }) +
        " * Application-blocks :" + (if (applications.isEmpty) "\n" else {
          "\n   " + applications.map(p => p._1 + " ==> " + p._2).mkString("\n   ") + "\n"
        }) + 
        " * Matchers           :" + (if (matchers.isEmpty) "\n" else {
          "\n   " + matchers.map(p => p._1 + " ==> " + p._2).mkString("\n   ") + "\n"
        }) +
        " * Lambdas            :\n" + lambdas.map { case template =>
          " +> " + template.toString.split("\n").mkString("\n    ") + "\n"
        }.mkString("\n") +
        " * Foralls            :\n" + quantifications.map { case template =>
          " +> " + template.toString.split("\n").mkString("\n    ") + "\n"
        }.mkString("\n")
      }

      (clauses, encodedBlockers, encodedApps, encodedMatchers, stringRepr)
    }

    def substitution(
      condVars: Map[Variable, Encoded],
      exprVars: Map[Variable, Encoded],
      condTree: Map[Variable, Set[Variable]],
      lambdas: Seq[LambdaTemplate],
      quantifications: Seq[QuantificationTemplate],
      baseSubst: Map[Encoded, Arg],
      pathVar: Variable,
      aVar: Encoded
    ): (Map[Encoded, Arg], Clauses) = {

      val freshSubst = exprVars.map { case (v, vT) => vT -> encodeSymbol(v) } ++
                       freshConds(aVar, condVars, condTree)

      val matcherSubst = baseSubst.collect { case (c, Right(m)) => c -> m }

      var subst = freshSubst.mapValues(Left(_)) ++ baseSubst
      var clauses : Clauses = Seq.empty

      // /!\ CAREFUL /!\
      // We have to be wary while computing the lambda subst map since lambdas can
      // depend on each other. However, these dependencies cannot be cyclic so it
      // suffices to make sure the traversal order is correct.
      var seen : Set[LambdaTemplate] = Set.empty

      val lambdaKeys = lambdas.map(lambda => lambda.ids._2 -> lambda).toMap
      def extractSubst(lambda: LambdaTemplate): Unit = {
        for {
          dep <- lambda.structure.closures flatMap lambdaKeys.get 
          if !seen(dep)
        } extractSubst(dep)

        if (!seen(lambda)) {
          val substMap = subst.mapValues(_.encoded)
          val substLambda = lambda.substitute(mkSubstituter(substMap), matcherSubst)
          val (idT, cls) = instantiateLambda(substLambda)
          subst += lambda.ids._2 -> Left(idT)
          clauses ++= cls
          seen += lambda
        }
      }

      for (l <- lambdas) extractSubst(l)

      // instantiate positive quantifications last to avoid introducing
      // extra quantifier instantiations that arise due to empty domains
      for (q <- quantifications.sortBy(_.polarity.isInstanceOf[Positive])) {
        val substMap = subst.mapValues(_.encoded)
        val substQuant = q.substitute(mkSubstituter(substMap), matcherSubst)
        val (map, cls) = instantiateQuantification(substQuant)
        subst ++= map.mapValues(Left(_))
        clauses ++= cls
      }

      (subst, clauses)
    }

    def instantiate(
      clauses: Clauses,
      calls: Calls,
      apps: Apps,
      matchers: Matchers,
      substMap: Map[Encoded, Arg]
    ): Clauses = {

      val substituter : Encoded => Encoded = mkSubstituter(substMap.mapValues(_.encoded))
      val msubst = substMap.collect { case (c, Right(m)) => c -> m }

      val allClauses = new scala.collection.mutable.ListBuffer[Encoded]
      allClauses ++= clauses.map(substituter)

      for ((b, fis) <- calls; bp = substituter(b); fi <- fis) {
        allClauses ++= instantiateCall(bp, fi.substitute(substituter, msubst))
      }

      for ((b,fas) <- apps; bp = substituter(b); fa <- fas) {
        allClauses ++= instantiateApp(bp, fa.substitute(substituter, msubst))
      }

      for ((b, matchs) <- matchers; bp = substituter(b); m <- matchs) {
        allClauses ++= instantiateMatcher(bp, m.substitute(substituter, msubst))
      }

      allClauses.toSeq
    }
  }

  def instantiateExpr(expr: Expr, bindings: Map[Variable, Encoded]): Clauses = {
    val start = Variable(FreshIdentifier("start", true), BooleanType)
    val encodedStart = encodeSymbol(start)

    val tpeClauses = bindings.flatMap { case (v, s) => registerSymbol(encodedStart, s, v.getType) }.toSeq

    val instExpr = simplifyHOFunctions(simplifyQuantifications(expr))
    val (condVars, exprVars, condTree, guardedExprs, lambdas, quants) =
      mkClauses(start, instExpr, bindings + (start -> encodedStart), polarity = Some(true))

    val (clauses, calls, apps, matchers, _) = Template.encode(
      start -> encodedStart, bindings.toSeq, condVars, exprVars, guardedExprs, lambdas, quants)

    val (substMap, substClauses) = Template.substitution(
      condVars, exprVars, condTree, lambdas, quants, Map.empty, start, encodedStart)

    val templateClauses = Template.instantiate(clauses, calls, apps, matchers, substMap)
    val allClauses = encodedStart +: (tpeClauses ++ substClauses ++ templateClauses)

    for (cl <- allClauses) {
      ctx.reporter.debug("  . " + cl)
    }

    allClauses
  }
}
