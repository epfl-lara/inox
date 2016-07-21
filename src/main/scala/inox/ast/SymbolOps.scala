/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

import utils._

/** Provides functions to manipulate [[purescala.Expressions]].
  *
  * This object provides a few generic operations on Leon expressions,
  * as well as some common operations.
  *
  * The generic operations lets you apply operations on a whole tree
  * expression. You can look at:
  *   - [[GenTreeOps.fold foldRight]]
  *   - [[GenTreeOps.preTraversal preTraversal]]
  *   - [[GenTreeOps.postTraversal postTraversal]]
  *   - [[GenTreeOps.preMap preMap]]
  *   - [[GenTreeOps.postMap postMap]]
  *   - [[GenTreeOps.genericTransform genericTransform]]
  *
  * These operations usually take a higher order function that gets applied to the
  * expression tree in some strategy. They provide an expressive way to build complex
  * operations on Leon expressions.
  *
  */
trait SymbolOps extends TreeOps { self: TypeOps =>
  import trees._
  import trees.exprOps._
  val symbols: Symbols
  import symbols._

  /** Computes the negation of a boolean formula, with some simplifications. */
  def negate(expr: Expr) : Expr = {
    (expr match {
      case Let(i,b,e) => Let(i,b,negate(e))
      case Not(e) => e
      case Implies(e1,e2) => and(e1, negate(e2))
      case Or(exs) => and(exs map negate: _*)
      case And(exs) => or(exs map negate: _*)
      case LessThan(e1,e2) => GreaterEquals(e1,e2)
      case LessEquals(e1,e2) => GreaterThan(e1,e2)
      case GreaterThan(e1,e2) => LessEquals(e1,e2)
      case GreaterEquals(e1,e2) => LessThan(e1,e2)
      case IfExpr(c,e1,e2) => IfExpr(c, negate(e1), negate(e2))
      case BooleanLiteral(b) => BooleanLiteral(!b)
      case e => Not(e)
    }).setPos(expr)
  }

  /** Replace each node by its constructor
    *
    * Remap the expression by calling the corresponding constructor
    * for each node of the expression. The constructor will perfom
    * some local simplifications, resulting in a simplified expression.
    */
  def simplifyByConstructors(expr: Expr): Expr = {
    def step(e: Expr): Option[Expr] = e match {
      case Not(t) => Some(not(t))
      case UMinus(t) => Some(uminus(t))
      case CaseClassSelector(cd, e, sel) => Some(caseClassSelector(cd, e, sel))
      case AsInstanceOf(e, ct) => Some(asInstOf(e, ct))
      case Equals(t1, t2) => Some(equality(t1, t2))
      case Implies(t1, t2) => Some(implies(t1, t2))
      case Plus(t1, t2) => Some(plus(t1, t2))
      case Minus(t1, t2) => Some(minus(t1, t2))
      case Times(t1, t2) => Some(times(t1, t2))
      case And(args) => Some(andJoin(args))
      case Or(args) => Some(orJoin(args))
      case Tuple(args) => Some(tupleWrap(args))
      case MatchExpr(scrut, cases) => Some(matchExpr(scrut, cases))
      case _ => None
    }
    postMap(step)(expr)
  }

  /** Normalizes the expression expr */
  def normalizeExpression(expr: Expr): Expr = {
    def rec(e: Expr): Option[Expr] = e match {
      case TupleSelect(Let(id, v, b), ts) =>
        Some(Let(id, v, tupleSelect(b, ts, true)))

      case TupleSelect(LetTuple(ids, v, b), ts) =>
        Some(letTuple(ids, v, tupleSelect(b, ts, true)))

      case CaseClassSelector(cct, cc: CaseClass, id) =>
        Some(caseClassSelector(cct, cc, id).copiedFrom(e))

      case IfExpr(c, thenn, elze) if (thenn == elze) && isPurelyFunctional(c) =>
        Some(thenn)

      case IfExpr(c, BooleanLiteral(true), BooleanLiteral(false)) =>
        Some(c)

      case IfExpr(Not(c), thenn, elze) =>
        Some(IfExpr(c, elze, thenn).copiedFrom(e))

      case IfExpr(c, BooleanLiteral(false), BooleanLiteral(true)) =>
        Some(Not(c).copiedFrom(e))

      case FunctionInvocation(id, tps, List(IfExpr(c, thenn, elze))) =>
        Some(IfExpr(c, FunctionInvocation(id, tps, List(thenn)), FunctionInvocation(id, tps, List(elze))).copiedFrom(e))

      case _ =>
        None
    }

    fixpoint(postMap(rec))(expr)
  }

  private val typedIds: scala.collection.mutable.Map[Type, List[Identifier]] =
    scala.collection.mutable.Map.empty.withDefaultValue(List.empty)

  /** Normalizes identifiers in an expression to enable some notion of structural
    * equality between expressions on which usual equality doesn't make sense
    * (i.e. closures).
    *
    * This function relies on the static map `typedIds` to ensure identical
    * structures and must therefore be synchronized.
    *
    * The optional argument [[onlySimple]] determines whether non-simple expressions
    * (see [[isSimple]]) should be normalized into a dependency or recursed into
    * (when they don't depend on [[args]]). This distinction is used in the
    * unrolling solver to provide geenral equality checks between functions even when
    * they have complex closures.
    */
  def normalizeStructure(args: Seq[ValDef], expr: Expr, onlySimple: Boolean = true):
                        (Seq[ValDef], Expr, Map[Variable, Expr]) = synchronized {
    val vars = args.map(_.toVariable).toSet

    class Normalizer extends TreeTransformer {
      var subst: Map[Variable, Expr] = Map.empty
      var remainingIds: Map[Type, List[Identifier]] = typedIds.toMap

      def getId(e: Expr): Identifier = {
        val tpe = bestRealType(e.getType)
        val newId = remainingIds.get(tpe) match {
          case Some(x :: xs) =>
            remainingIds += tpe -> xs
            x
          case _ =>
            val x = FreshIdentifier("x", true)
            typedIds(tpe) = typedIds(tpe) :+ x
            x
        }
        subst += Variable(newId, tpe) -> e
        newId
      }

      override def transform(id: Identifier, tpe: Type): (Identifier, Type) = subst.get(Variable(id, tpe)) match {
        case Some(Variable(newId, tpe)) => (newId, tpe)
        case Some(_) => scala.sys.error("Should never happen!")
        case None => (getId(Variable(id, tpe)), tpe)
      }

      override def transform(e: Expr): Expr = e match {
        case expr if (isSimple(expr) || !onlySimple) && (variablesOf(expr) & vars).isEmpty =>
          Variable(getId(expr), expr.getType)
        case f: Forall =>
          val (args, body, newSubst) = normalizeStructure(f.args, f.body, onlySimple)
          subst ++= newSubst
          Forall(args, body)
        case l: Lambda =>
          val (args, body, newSubst) = normalizeStructure(l.args, l.body, onlySimple)
          subst ++= newSubst
          Lambda(args, body)
        case _ => super.transform(e)
      }
    }

    val n = new Normalizer
    // this registers the argument images into n.subst
    val bindings = args map n.transform
    val normalized = n.transform(matchToIfThenElse(expr))

    val freeVars = variablesOf(normalized) -- bindings.map(_.toVariable)
    val bodySubst = n.subst.filter(p => freeVars(p._1))

    (bindings, normalized, bodySubst)
  }

  def normalizeStructure(lambda: Lambda): (Lambda, Map[Variable, Expr]) = {
    val (args, body, subst) = normalizeStructure(lambda.args, lambda.body, onlySimple = false)
    (Lambda(args, body), subst)
  }

  def normalizeStructure(forall: Forall): (Forall, Map[Variable, Expr]) = {
    val (args, body, subst) = normalizeStructure(forall.args, forall.body)
    (Forall(args, body), subst)
  }

  /** Fully expands all let expressions. */
  def expandLets(expr: Expr): Expr = {
    def rec(ex: Expr, s: Map[Variable,Expr]) : Expr = ex match {
      case v: Variable if s.isDefinedAt(v) => rec(s(v), s)
      case l @ Let(i,e,b) => rec(b, s + (i.toVariable -> rec(e, s)))
      case i @ IfExpr(t1,t2,t3) => IfExpr(rec(t1, s),rec(t2, s),rec(t3, s)).copiedFrom(i)
      case m @ MatchExpr(scrut, cses) => matchExpr(rec(scrut, s), cses.map(inCase(_, s))).copiedFrom(m)
      case n @ Deconstructor(args, recons) =>
        var change = false
        val rargs = args.map(a => {
          val ra = rec(a, s)
          if(ra != a) {
            change = true
            ra
          } else {
            a
          }
        })
        if(change)
          recons(rargs).copiedFrom(n)
        else
          n
      case unhandled => scala.sys.error("Unhandled case in expandLets: " + unhandled)
    }

    def inCase(cse: MatchCase, s: Map[Variable,Expr]) : MatchCase = {
      import cse._
      MatchCase(pattern, optGuard map { rec(_, s) }, rec(rhs,s))
    }

    rec(expr, Map.empty)
  }

  /** Lifts lets to top level.
    *
    * Does not push any used variable out of scope.
    * Assumes no match expressions (i.e. matchToIfThenElse has been called on e)
    */
  def liftLets(e: Expr): Expr = {

    type C = Seq[(ValDef, Expr)]

    def combiner(e: Expr, defs: Seq[C]): C = (e, defs) match {
      case (Let(v, ex, b), Seq(inDef, inBody)) =>
        inDef ++ ((v, ex) +: inBody)
      case _ =>
        defs.flatten
    }

    def noLet(e: Expr, defs: C) = e match {
      case Let(_, _, b) => (b, defs)
      case _ => (e, defs)
    }

    val (bd, defs) = genericTransform[C](noTransformer, noLet, combiner)(Seq())(e)

    defs.foldRight(bd){ case ((vd, e), body) => Let(vd, e, body) }
  }

  /** Recursively transforms a pattern on a boolean formula expressing the conditions for the input expression, possibly including name binders
    *
    * For example, the following pattern on the input `i`
    * {{{
    * case m @ MyCaseClass(t: B, (_, 7)) =>
    * }}}
    * will yield the following condition before simplification (to give some flavour)
    *
    * {{{and(IsInstanceOf(MyCaseClass, i), and(Equals(m, i), InstanceOfClass(B, i.t), equals(i.k.arity, 2), equals(i.k._2, 7))) }}}
    *
    * Pretty-printed, this would be:
    * {{{
    * i.instanceOf[MyCaseClass] && m == i && i.t.instanceOf[B] && i.k.instanceOf[Tuple2] && i.k._2 == 7
    * }}}
    *
    * @see [[purescala.Expressions.Pattern]]
    */
  def conditionForPattern(in: Expr, pattern: Pattern, includeBinders: Boolean = false): Path = {
    def bind(ob: Option[ValDef], to: Expr): Path = {
      if (!includeBinders) {
        Path.empty
      } else {
        ob.map(v => Path.empty withBinding (v -> to)).getOrElse(Path.empty)
      }
    }

    def rec(in: Expr, pattern: Pattern): Path = {
      pattern match {
        case WildcardPattern(ob) =>
          bind(ob, in)

        case InstanceOfPattern(ob, ct) =>
          val tcd = ct.tcd
          if (tcd.root == tcd) {
            bind(ob, in)
          } else {
            Path(IsInstanceOf(in, ct)) merge bind(ob, in)
          }

        case CaseClassPattern(ob, cct, subps) =>
          val tccd = cct.tcd.toCase
          assert(tccd.fields.size == subps.size)
          val pairs = tccd.fields.map(_.id).toList zip subps.toList
          val subTests = pairs.map(p => rec(caseClassSelector(cct, in, p._1), p._2))
          Path(IsInstanceOf(in, cct)) merge bind(ob, in) merge subTests

        case TuplePattern(ob, subps) =>
          val TupleType(tpes) = in.getType
          assert(tpes.size == subps.size)
          val subTests = subps.zipWithIndex.map {
            case (p, i) => rec(tupleSelect(in, i+1, subps.size), p)
          }
          bind(ob, in) merge subTests

        case up @ UnapplyPattern(ob, id, tps, subps) =>
          val subs = unwrapTuple(up.get(in), subps.size).zip(subps) map (rec _).tupled
          bind(ob, in) withCond up.isSome(in) merge subs

        case LiteralPattern(ob, lit) =>
          Path(Equals(in, lit)) merge bind(ob, in)
      }
    }

    rec(in, pattern)
  }

  /** Converts the pattern applied to an input to a map between identifiers and expressions */
  def mapForPattern(in: Expr, pattern: Pattern): Map[Variable,Expr] = {
    def bindIn(ov: Option[ValDef], cast: Option[ClassType] = None): Map[Variable, Expr] = ov match {
      case None => Map()
      case Some(v) => Map(v.toVariable -> cast.map(asInstOf(in, _)).getOrElse(in))
    }

    pattern match {
      case CaseClassPattern(b, ct, subps) =>
        val tcd = ct.tcd.toCase
        assert(tcd.fields.size == subps.size)
        val pairs = tcd.fields.map(_.id).toList zip subps.toList
        val subMaps = pairs.map(p => mapForPattern(caseClassSelector(ct, asInstOf(in, ct), p._1), p._2))
        val together = subMaps.flatten.toMap
        bindIn(b, Some(ct)) ++ together

      case TuplePattern(b, subps) =>
        val TupleType(tpes) = in.getType
        assert(tpes.size == subps.size)

        val maps = subps.zipWithIndex.map{case (p, i) => mapForPattern(tupleSelect(in, i+1, subps.size), p)}
        val map = maps.flatten.toMap
        bindIn(b) ++ map

      case up @ UnapplyPattern(b, _, _, subps) =>
        bindIn(b) ++ unwrapTuple(up.getUnsafe(in), subps.size).zip(subps).flatMap {
          case (e, p) => mapForPattern(e, p)
        }.toMap

      case InstanceOfPattern(b, ct) =>
        bindIn(b, Some(ct))

      case other =>
        bindIn(other.binder)
    }
  }

  /** Rewrites all pattern-matching expressions into if-then-else expressions
    * Introduces additional error conditions. Does not introduce additional variables.
    */
  def matchToIfThenElse(expr: Expr): Expr = {

    def rewritePM(e: Expr): Option[Expr] = e match {
      case m @ MatchExpr(scrut, cases) =>
        // println("Rewriting the following PM: " + e)

        val condsAndRhs = for (cse <- cases) yield {
          val map = mapForPattern(scrut, cse.pattern)
          val patCond = conditionForPattern(scrut, cse.pattern, includeBinders = false)
          val realCond = cse.optGuard match {
            case Some(g) => patCond withCond replaceFromSymbols(map, g)
            case None => patCond
          }
          val newRhs = replaceFromSymbols(map, cse.rhs)
          (realCond.toClause, newRhs, cse)
        }

        val bigIte = condsAndRhs.foldRight[Expr](Error(m.getType, "Match is non-exhaustive").copiedFrom(m))((p1, ex) => {
          if(p1._1 == BooleanLiteral(true)) {
            p1._2
          } else {
            IfExpr(p1._1, p1._2, ex).copiedFrom(p1._3)
          }
        })

        Some(bigIte)

      case _ => None
    }

    preMap(rewritePM)(expr)
  }

  /** For each case in the [[purescala.Expressions.MatchExpr MatchExpr]], concatenates the path condition with the newly induced conditions.
   *
   *  Each case holds the conditions on other previous cases as negative.
   *
    * @see [[purescala.ExprOps#conditionForPattern conditionForPattern]]
    * @see [[purescala.ExprOps#mapForPattern mapForPattern]]
    */
  def matchExprCaseConditions(m: MatchExpr, path: Path): Seq[Path] = {
    val MatchExpr(scrut, cases) = m
    var pcSoFar = path

    for (c <- cases) yield {
      val g = c.optGuard getOrElse BooleanLiteral(true)
      val cond = conditionForPattern(scrut, c.pattern, includeBinders = true)
      val localCond = pcSoFar merge (cond withCond g)

      // These contain no binders defined in this MatchCase
      val condSafe = conditionForPattern(scrut, c.pattern)
      val gSafe = replaceFromSymbols(mapForPattern(scrut, c.pattern), g)
      pcSoFar = pcSoFar merge (condSafe withCond gSafe).negate

      localCond
    }
  }

  /** Condition to pass this match case, expressed w.r.t scrut only */
  def matchCaseCondition(scrut: Expr, c: MatchCase): Path = {

    val patternC = conditionForPattern(scrut, c.pattern, includeBinders = false)

    c.optGuard match {
      case Some(g) =>
        // guard might refer to binders
        val map  = mapForPattern(scrut, c.pattern)
        patternC withCond replaceFromSymbols(map, g)

      case None =>
        patternC
    }
  }

  private def hasInstance(tcd: TypedClassDef): Boolean = {
    val recursive = Set(tcd, tcd.root)

    def isRecursive(tpe: Type, seen: Set[TypedClassDef]): Boolean = tpe match {
      case ct: ClassType =>
        val ctcd = ct.tcd
        if (seen(ctcd)) {
          false
        } else if (recursive(ctcd)) {
          true
        } else ctcd match {
          case tcc: TypedCaseClassDef =>
            tcc.fieldsTypes.exists(isRecursive(_, seen + ctcd))
          case _ => false
        }
      case _ => false
    }

    val tcds = tcd match {
      case tacd: TypedAbstractClassDef => tacd.ccDescendants
      case tccd: TypedCaseClassDef => Seq(tccd)
    }

    tcds.exists { tcd =>
      tcd.fieldsTypes.forall(tpe => !isRecursive(tpe, Set.empty))
    }
  }

  /** Returns simplest value of a given type */
  def simplestValue(tpe: Type): Expr = tpe match {
    case StringType                 => StringLiteral("")
    case Int32Type                  => IntLiteral(0)
    case RealType               	  => FractionLiteral(0, 1)
    case IntegerType                => IntegerLiteral(0)
    case CharType                   => CharLiteral('a')
    case BooleanType                => BooleanLiteral(false)
    case UnitType                   => UnitLiteral()
    case SetType(baseType)          => FiniteSet(Seq(), baseType)
    case BagType(baseType)          => FiniteBag(Seq(), baseType)
    case MapType(fromType, toType)  => FiniteMap(Seq(), simplestValue(toType), fromType)
    case TupleType(tpes)            => Tuple(tpes.map(simplestValue))

    case ct @ ClassType(id, tps) =>
      val tcd = ct.lookupClass.getOrElse(throw ClassLookupException(id))
      if (!hasInstance(tcd)) scala.sys.error(ct +" does not seem to be well-founded")

      val tccd @ TypedCaseClassDef(cd, tps) = tcd match {
        case tacd: TypedAbstractClassDef =>
          tacd.ccDescendants.filter(hasInstance(_)).sortBy(_.fields.size).head
        case tccd: TypedCaseClassDef => tccd
      }

      CaseClass(ClassType(cd.id, tps), tccd.fieldsTypes.map(simplestValue))

    case tp: TypeParameter =>
      GenericValue(tp, 0)

    case ft @ FunctionType(from, to) =>
      Lambda(from.map(tpe => ValDef(FreshIdentifier("x", true), tpe)), simplestValue(to))

    case _ => scala.sys.error("I can't choose simplest value for type " + tpe)
  }

  def valuesOf(tp: Type): Stream[Expr] = {
    import utils.StreamUtils._
    tp match {
      case BooleanType =>
        Stream(BooleanLiteral(false), BooleanLiteral(true))
      case BVType(size) =>
        val count = BigInt(2).pow(size - 1)
        def rec(i: BigInt): Stream[BigInt] = 
          if (i <= count) Stream.cons(i, Stream.cons(-i - 1, rec(i + 1)))
          else Stream.empty
        rec(0) map (BVLiteral(_, size))
      case IntegerType =>
        Stream.iterate(BigInt(0)) { prev =>
          if (prev > 0) -prev else -prev + 1
        } map IntegerLiteral
      case UnitType =>
        Stream(UnitLiteral())
      case tp: TypeParameter =>
        Stream.from(0) map (GenericValue(tp, _))
      case TupleType(stps) =>
        cartesianProduct(stps map (tp => valuesOf(tp))) map Tuple
      case SetType(base) =>
        def elems = valuesOf(base)
        elems.scanLeft(Stream(FiniteSet(Seq(), base): Expr)){ (prev, curr) =>
          prev flatMap { case fs @ FiniteSet(elems, tp) => Stream(fs, FiniteSet(elems :+ curr, tp)) }
        }.flatten
      case BagType(base) =>
        def elems = valuesOf(base)
        def counts = Stream.iterate(BigInt(1))(prev => prev + 1) map IntegerLiteral
        val pairs = interleave(elems.map(e => counts.map(c => e -> c)))
        pairs.scanLeft(Stream(FiniteBag(Seq(), base): Expr)) { (prev, curr) =>
          prev flatMap { case fs @ FiniteBag(elems, tp) => Stream(fs, FiniteBag(elems :+ curr, tp)) }
        }.flatten
      case MapType(from, to) =>
        def elems = cartesianProduct(valuesOf(from), valuesOf(to))
        val seqs = elems.scanLeft(Stream(Seq[(Expr, Expr)]())) { (prev, curr) =>
          prev flatMap { case seq => Stream(seq, seq :+ curr) }
        }.flatten
        cartesianProduct(seqs, valuesOf(to)) map { case (values, default) => FiniteMap(values, default, from) }
      case ct: ClassType => ct.lookupClass match {
        case Some(tccd: TypedCaseClassDef) =>
          cartesianProduct(tccd.fieldsTypes map valuesOf) map (CaseClass(ct, _))
        case Some(accd: TypedAbstractClassDef) =>
          interleave(accd.ccDescendants.map(tccd => valuesOf(tccd.toType)))
        case None => throw ClassLookupException(ct.id)
      }
    }
  }


  /** Hoists all IfExpr at top level.
    *
    * Guarantees that all IfExpr will be at the top level and as soon as you
    * encounter a non-IfExpr, then no more IfExpr can be found in the
    * sub-expressions
    *
    * Assumes no match expressions
    */
  def hoistIte(expr: Expr): Expr = {
    def transform(expr: Expr): Option[Expr] = expr match {
      case IfExpr(c, t, e) => None

      case nop@Deconstructor(ts, op) => {
        val iteIndex = ts.indexWhere{ case IfExpr(_, _, _) => true case _ => false }
        if(iteIndex == -1) None else {
          val (beforeIte, startIte) = ts.splitAt(iteIndex)
          val afterIte = startIte.tail
          val IfExpr(c, t, e) = startIte.head
          Some(IfExpr(c,
            op(beforeIte ++ Seq(t) ++ afterIte).copiedFrom(nop),
            op(beforeIte ++ Seq(e) ++ afterIte).copiedFrom(nop)
          ))
        }
      }
      case _ => None
    }

    postMap(transform, applyRec = true)(expr)
  }

  def collectWithPC[T](f: PartialFunction[Expr, T])(expr: Expr): Seq[(T, Path)] = {

    def rec(expr: Expr, path: Path): Seq[(T, Path)] = {
      val seq = if (f.isDefinedAt(expr)) {
        Seq(f(expr) -> path)
      } else {
        Seq.empty[(T, Path)]
      }

      val rseq = expr match {
        case Let(i, v, b) =>
          rec(v, path) ++
          rec(b, path withBinding (i -> v))

        case Ensuring(Require(pre, body), Lambda(Seq(arg), post)) =>
          rec(pre, path) ++
          rec(body, path withCond pre) ++
          rec(post, path withCond pre withBinding (arg -> body))

        case Ensuring(body, Lambda(Seq(arg), post)) =>
          rec(body, path) ++
          rec(post, path withBinding (arg -> body))

        case Require(pre, body) =>
          rec(pre, path) ++
          rec(body, path withCond pre)

        case Assert(pred, err, body) =>
          rec(pred, path) ++
          rec(body, path withCond pred)

        case MatchExpr(scrut, cases) =>
          val rs = rec(scrut, path)
          var soFar = path

          rs ++ cases.flatMap { c =>
            val patternPathPos = conditionForPattern(scrut, c.pattern, includeBinders = true)
            val patternPathNeg = conditionForPattern(scrut, c.pattern, includeBinders = false)
            val map = mapForPattern(scrut, c.pattern)
            val guardOrTrue = c.optGuard.getOrElse(BooleanLiteral(true))
            val guardMapped = replaceFromSymbols(map, guardOrTrue)

            val rc = rec((patternPathPos withCond guardOrTrue).fullClause, soFar)
            val subPath = soFar merge (patternPathPos withCond guardOrTrue)
            val rrhs = rec(c.rhs, subPath)

            soFar = soFar merge (patternPathNeg withCond guardMapped).negate
            rc ++ rrhs
          }

        case IfExpr(cond, thenn, elze) =>
          rec(cond, path) ++
          rec(thenn, path withCond cond) ++
          rec(elze, path withCond Not(cond))

        case And(es) =>
          var soFar = path
          es.flatMap { e =>
            val re = rec(e, soFar)
            soFar = soFar withCond e
            re
          }

        case Or(es) =>
          var soFar = path
          es.flatMap { e =>
            val re = rec(e, soFar)
            soFar = soFar withCond Not(e)
            re
          }

        case Implies(lhs, rhs) =>
          rec(lhs, path) ++
          rec(rhs, path withCond lhs)

        case Operator(es, _) =>
          es.flatMap(rec(_, path))

        case _ => sys.error("Expression " + expr + "["+expr.getClass+"] is not extractable")
      }

      seq ++ rseq
    }

    rec(expr, Path.empty)
  }

  /** Returns the value for an identifier given a model. */
  def valuateWithModel(model: Map[ValDef, Expr])(vd: ValDef): Expr = {
    model.getOrElse(vd, simplestValue(vd.getType))
  }

  /** Substitute (free) variables in an expression with values form a model.
    *
    * Complete with simplest values in case of incomplete model.
    */
  def valuateWithModelIn(expr: Expr, vars: Set[ValDef], model: Map[ValDef, Expr]): Expr = {
    val valuator = valuateWithModel(model) _
    replace(vars.map(vd => vd.toVariable -> valuator(vd)).toMap, expr)
  }

  /** Simple, local optimization on string */
  def simplifyString(expr: Expr): Expr = {
    def simplify0(expr: Expr): Expr = (expr match {
      case StringConcat(StringLiteral(""), b) => b
      case StringConcat(b, StringLiteral("")) => b
      case StringConcat(StringLiteral(a), StringLiteral(b)) => StringLiteral(a + b)
      case StringLength(StringLiteral(a)) => IntLiteral(a.length)
      case StringBigLength(StringLiteral(a)) => IntegerLiteral(a.length)
      case SubString(StringLiteral(a), IntLiteral(start), IntLiteral(end)) => StringLiteral(a.substring(start.toInt, end.toInt))
      case BigSubString(StringLiteral(a), IntegerLiteral(start), IntegerLiteral(end)) => StringLiteral(a.substring(start.toInt, end.toInt))
      case _ => expr
    }).copiedFrom(expr)
    simplify0(expr)
    fixpoint(simplePostTransform(simplify0))(expr)
  }

  /** Simple, local simplification on arithmetic
    *
    * You should not assume anything smarter than some constant folding and
    * simple cancellation. To avoid infinite cycle we only apply simplification
    * that reduce the size of the tree. The only guarantee from this function is
    * to not augment the size of the expression and to be sound.
    */
  def simplifyArithmetic(expr: Expr): Expr = {
    def simplify0(expr: Expr): Expr = (expr match {
      case Plus(IntegerLiteral(i1), IntegerLiteral(i2)) => IntegerLiteral(i1 + i2)
      case Plus(IntegerLiteral(zero), e) if zero == BigInt(0) => e
      case Plus(e, IntegerLiteral(zero)) if zero == BigInt(0) => e
      case Plus(e1, UMinus(e2)) => Minus(e1, e2)
      case Plus(Plus(e, IntegerLiteral(i1)), IntegerLiteral(i2)) => Plus(e, IntegerLiteral(i1+i2))
      case Plus(Plus(IntegerLiteral(i1), e), IntegerLiteral(i2)) => Plus(IntegerLiteral(i1+i2), e)

      case Minus(e, IntegerLiteral(zero)) if zero == BigInt(0) => e
      case Minus(IntegerLiteral(zero), e) if zero == BigInt(0) => UMinus(e)
      case Minus(IntegerLiteral(i1), IntegerLiteral(i2)) => IntegerLiteral(i1 - i2)
      case Minus(e1, UMinus(e2)) => Plus(e1, e2)
      case Minus(e1, Minus(UMinus(e2), e3)) => Plus(e1, Plus(e2, e3))

      case UMinus(IntegerLiteral(x)) => IntegerLiteral(-x)
      case UMinus(UMinus(x)) => x
      case UMinus(Plus(UMinus(e1), e2)) => Plus(e1, UMinus(e2))
      case UMinus(Minus(e1, e2)) => Minus(e2, e1)

      case Times(IntegerLiteral(i1), IntegerLiteral(i2)) => IntegerLiteral(i1 * i2)
      case Times(IntegerLiteral(one), e) if one == BigInt(1) => e
      case Times(IntegerLiteral(mone), e) if mone == BigInt(-1) => UMinus(e)
      case Times(e, IntegerLiteral(one)) if one == BigInt(1) => e
      case Times(IntegerLiteral(zero), _) if zero == BigInt(0) => IntegerLiteral(0)
      case Times(_, IntegerLiteral(zero)) if zero == BigInt(0) => IntegerLiteral(0)
      case Times(IntegerLiteral(i1), Times(IntegerLiteral(i2), t)) => Times(IntegerLiteral(i1*i2), t)
      case Times(IntegerLiteral(i1), Times(t, IntegerLiteral(i2))) => Times(IntegerLiteral(i1*i2), t)
      case Times(IntegerLiteral(i), UMinus(e)) => Times(IntegerLiteral(-i), e)
      case Times(UMinus(e), IntegerLiteral(i)) => Times(e, IntegerLiteral(-i))
      case Times(IntegerLiteral(i1), Division(e, IntegerLiteral(i2))) if i2 != BigInt(0) && i1 % i2 == BigInt(0) => Times(IntegerLiteral(i1/i2), e)

      case Division(IntegerLiteral(i1), IntegerLiteral(i2)) if i2 != BigInt(0) => IntegerLiteral(i1 / i2)
      case Division(e, IntegerLiteral(one)) if one == BigInt(1) => e

      //here we put more expensive rules
      //btw, I know those are not the most general rules, but they lead to good optimizations :)
      case Plus(UMinus(Plus(e1, e2)), e3) if e1 == e3 => UMinus(e2)
      case Plus(UMinus(Plus(e1, e2)), e3) if e2 == e3 => UMinus(e1)
      case Minus(e1, e2) if e1 == e2 => IntegerLiteral(0)
      case Minus(Plus(e1, e2), Plus(e3, e4)) if e1 == e4 && e2 == e3 => IntegerLiteral(0)
      case Minus(Plus(e1, e2), Plus(Plus(e3, e4), e5)) if e1 == e4 && e2 == e3 => UMinus(e5)

      case StringConcat(StringLiteral(""), a) => a
      case StringConcat(a, StringLiteral("")) => a
      case StringConcat(StringLiteral(a), StringLiteral(b)) => StringLiteral(a+b)
      case StringConcat(StringLiteral(a), StringConcat(StringLiteral(b), c)) => StringConcat(StringLiteral(a+b), c)
      case StringConcat(StringConcat(c, StringLiteral(a)), StringLiteral(b)) => StringConcat(c, StringLiteral(a+b))
      case StringConcat(a, StringConcat(b, c)) => StringConcat(StringConcat(a, b), c)
      //default
      case e => e
    }).copiedFrom(expr)

    fixpoint(simplePostTransform(simplify0))(expr)
  }

  /**
   * Some helper methods for FractionLiterals
   */
  def normalizeFraction(fl: FractionLiteral) = {
    val FractionLiteral(num, denom) = fl
    val modNum = if (num < 0) -num else num
    val modDenom = if (denom < 0) -denom else denom
    val divisor = modNum.gcd(modDenom)
    val simpNum = num / divisor
    val simpDenom = denom / divisor
    if (simpDenom < 0)
      FractionLiteral(-simpNum, -simpDenom)
    else
      FractionLiteral(simpNum, simpDenom)
  }

  val realzero = FractionLiteral(0, 1)
  def floor(fl: FractionLiteral): FractionLiteral = {
    val FractionLiteral(n, d) = normalizeFraction(fl)
    if (d == 0) throw new IllegalStateException("denominator zero")
    if (n == 0) realzero
    else if (n > 0) {
      //perform integer division
      FractionLiteral(n / d, 1)
    } else {
      //here the number is negative
      if (n % d == 0)
        FractionLiteral(n / d, 1)
      else {
        //perform integer division and subtract 1
        FractionLiteral(n / d - 1, 1)
      }
    }
  }

  /* =================
   * Body manipulation
   * =================
   */

  /** Returns whether a particular [[Expressions.Expr]] contains specification
    * constructs, namely [[Expressions.Require]] and [[Expressions.Ensuring]].
    */
  def hasSpec(e: Expr): Boolean = exists {
    case Require(_, _) => true
    case Ensuring(_, _) => true
    case Let(i, e, b) => hasSpec(b)
    case _ => false
  } (e)

  /** Merges the given [[Path]] into the provided [[Expressions.Expr]].
    *
    * This method expects to run on a [[Definitions.FunDef.fullBody]] and merges into
    * existing pre- and postconditions.
    *
    * @param expr The current body
    * @param path The path that should be wrapped around the given body
    * @see [[Expressions.Ensuring]]
    * @see [[Expressions.Require]]
    */
  def withPath(expr: Expr, path: Path): Expr = expr match {
    case Let(i, e, b) => withPath(b, path withBinding (i -> e))
    case Require(pre, b) => path specs (b, pre)
    case Ensuring(Require(pre, b), post) => path specs (b, pre, post)
    case Ensuring(b, post) => path specs (b, post = post)
    case b => path specs b
  }

  /** Replaces the precondition of an existing [[Expressions.Expr]] with a new one.
    *
    * If no precondition is provided, removes any existing precondition.
    * Else, wraps the expression with a [[Expressions.Require]] clause referring to the new precondition.
    *
    * @param expr The current expression
    * @param pred An optional precondition. Setting it to None removes any precondition.
    * @see [[Expressions.Ensuring]]
    * @see [[Expressions.Require]]
    */
  def withPrecondition(expr: Expr, pred: Option[Expr]): Expr = (pred, expr) match {
    case (Some(newPre), Require(pre, b))              => req(newPre, b)
    case (Some(newPre), Ensuring(Require(pre, b), p)) => Ensuring(req(newPre, b), p)
    case (Some(newPre), Ensuring(b, p))               => Ensuring(req(newPre, b), p)
    case (Some(newPre), Let(i, e, b)) if hasSpec(b)   => Let(i, e, withPrecondition(b, pred))
    case (Some(newPre), b)                            => req(newPre, b)
    case (None, Require(pre, b))                      => b
    case (None, Ensuring(Require(pre, b), p))         => Ensuring(b, p)
    case (None, Let(i, e, b)) if hasSpec(b)           => Let(i, e, withPrecondition(b, pred))
    case (None, b)                                    => b
  }

  /** Replaces the postcondition of an existing [[Expressions.Expr]] with a new one.
    *
    * If no postcondition is provided, removes any existing postcondition.
    * Else, wraps the expression with a [[Expressions.Ensuring]] clause referring to the new postcondition.
    *
    * @param expr The current expression
    * @param oie An optional postcondition. Setting it to None removes any postcondition.
    * @see [[Expressions.Ensuring]]
    * @see [[Expressions.Require]]
    */
  def withPostcondition(expr: Expr, oie: Option[Expr]): Expr = (oie, expr) match {
    case (Some(npost), Ensuring(b, post))          => ensur(b, npost)
    case (Some(npost), Let(i, e, b)) if hasSpec(b) => Let(i, e, withPostcondition(b, oie))
    case (Some(npost), b)                          => ensur(b, npost)
    case (None, Ensuring(b, p))                    => b
    case (None, Let(i, e, b)) if hasSpec(b)        => Let(i, e, withPostcondition(b, oie))
    case (None, b)                                 => b
  }

  /** Adds a body to a specification
    *
    * @param expr The specification expression [[Expressions.Ensuring]] or [[Expressions.Require]]. If none of these, the argument is discarded.
    * @param body An option of [[Expressions.Expr]] possibly containing an expression body.
    * @return The post/pre condition with the body. If no body is provided, returns [[Expressions.NoTree]]
    * @see [[Expressions.Ensuring]]
    * @see [[Expressions.Require]]
    */
  def withBody(expr: Expr, body: Option[Expr]): Expr = expr match {
    case Let(i, e, b) if hasSpec(b)      => Let(i, e, withBody(b, body))
    case Require(pre, _)                 => Require(pre, body.getOrElse(NoTree(expr.getType)))
    case Ensuring(Require(pre, _), post) => Ensuring(Require(pre, body.getOrElse(NoTree(expr.getType))), post)
    case Ensuring(_, post)               => Ensuring(body.getOrElse(NoTree(expr.getType)), post)
    case _                               => body.getOrElse(NoTree(expr.getType))
  }

  object InvocationExtractor {
    private def flatInvocation(expr: Expr): Option[(Identifier, Seq[Type], Seq[Expr])] = expr match {
      case fi @ FunctionInvocation(id, tps, args) => Some((id, tps, args))
      case Application(caller, args) => flatInvocation(caller) match {
        case Some((id, tps, prevArgs)) => Some((id, tps, prevArgs ++ args))
        case None => None
      }
      case _ => None
    }

    def unapply(expr: Expr): Option[(Identifier, Seq[Type], Seq[Expr])] = expr match {
      case IsTyped(f: FunctionInvocation, ft: FunctionType) => None
      case IsTyped(f: Application, ft: FunctionType) => None
      case FunctionInvocation(id, tps, args) => Some((id, tps, args))
      case f: Application => flatInvocation(f)
      case _ => None
    }
  }

  def firstOrderCallsOf(expr: Expr): Set[(Identifier, Seq[Type], Seq[Expr])] =
    collect { e => InvocationExtractor.unapply(e).toSet[(Identifier, Seq[Type], Seq[Expr])] }(expr)

  object ApplicationExtractor {
    private def flatApplication(expr: Expr): Option[(Expr, Seq[Expr])] = expr match {
      case Application(fi: FunctionInvocation, _) => None
      case Application(caller: Application, args) => flatApplication(caller) match {
        case Some((c, prevArgs)) => Some((c, prevArgs ++ args))
        case None => None
      }
      case Application(caller, args) => Some((caller, args))
      case _ => None
    }

    def unapply(expr: Expr): Option[(Expr, Seq[Expr])] = expr match {
      case IsTyped(f: Application, ft: FunctionType) => None
      case f: Application => flatApplication(f)
      case _ => None
    }
  }

  def firstOrderAppsOf(expr: Expr): Set[(Expr, Seq[Expr])] =
    collect[(Expr, Seq[Expr])] {
      case ApplicationExtractor(caller, args) => Set(caller -> args)
      case _ => Set.empty
    } (expr)

  def simplifyHOFunctions(expr: Expr): Expr = {

    def liftToLambdas(expr: Expr) = {
      def apply(expr: Expr, args: Seq[Expr]): Expr = expr match {
        case IfExpr(cond, thenn, elze) =>
          IfExpr(cond, apply(thenn, args), apply(elze, args))
        case Let(i, e, b) =>
          Let(i, e, apply(b, args))
        case LetTuple(is, es, b) =>
          letTuple(is, es, apply(b, args))
        //case l @ Lambda(params, body) =>
        //  l.withParamSubst(args, body)
        case _ => Application(expr, args)
      }

      def lift(expr: Expr): Expr = expr.getType match {
        case FunctionType(from, to) => expr match {
          case _ : Lambda => expr
          case _ : Variable => expr
          case e =>
            val args = from.map(tpe => ValDef(FreshIdentifier("x", true), tpe))
            val application = apply(expr, args.map(_.toVariable))
            Lambda(args, lift(application))
        }
        case _ => expr
      }

      def extract(expr: Expr, build: Boolean) = if (build) lift(expr) else expr

      def rec(expr: Expr, build: Boolean): Expr = expr match {
        case Application(caller, args) =>
          val newArgs = args.map(rec(_, true))
          val newCaller = rec(caller, false)
          extract(Application(newCaller, newArgs), build)
        case FunctionInvocation(id, tps, args) =>
          val newArgs = args.map(rec(_, true))
          extract(FunctionInvocation(id, tps, newArgs), build)
        case l @ Lambda(args, body) =>
          val newBody = rec(body, true)
          extract(Lambda(args, newBody), build)
        case Deconstructor(es, recons) => recons(es.map(rec(_, build)))
      }

      rec(lift(expr), true)
    }

    liftToLambdas(
      matchToIfThenElse(
        expr
      )
    )
  }

  // Use this only to debug isValueOfType
  private implicit class BooleanAdder(b: Boolean) {
    @inline def <(msg: => String) = {/*if(!b) println(msg); */b}
  }

  /** Returns true if expr is a value of type t */
  def isValueOfType(e: Expr, t: Type): Boolean = {
    def unWrapSome(s: Expr) = s match {
      case CaseClass(_, Seq(a)) => a
      case _ => s
    }
    (e, t) match {
      case (StringLiteral(_), StringType) => true
      case (IntLiteral(_), Int32Type) => true
      case (IntegerLiteral(_), IntegerType) => true
      case (CharLiteral(_), CharType) => true
      case (FractionLiteral(_, _), RealType) => true
      case (BooleanLiteral(_), BooleanType) => true
      case (UnitLiteral(), UnitType) => true
      case (GenericValue(t, _), tp) => t == tp
      case (Tuple(elems), TupleType(bases)) =>
        elems zip bases forall (eb => isValueOfType(eb._1, eb._2))
      case (FiniteSet(elems, tbase), SetType(base)) =>
        tbase == base &&
        (elems forall isValue)
      case (FiniteBag(elements, fbtpe), BagType(tpe)) =>
        fbtpe == tpe &&
        elements.forall{ case (key, value) => isValueOfType(key, tpe) && isValueOfType(value, IntegerType) }
      case (FiniteMap(elems, tk, tv), MapType(from, to)) =>
        (tk == from) < s"$tk not equal to $from" && (tv == to) < s"$tv not equal to $to" &&
        (elems forall (kv => isValueOfType(kv._1, from) < s"${kv._1} not a value of type ${from}" && isValueOfType(unWrapSome(kv._2), to) < s"${unWrapSome(kv._2)} not a value of type ${to}" ))
      case (CaseClass(ct, args), ct2: ClassType) =>
        isSubtypeOf(ct, ct2) < s"$ct not a subtype of $ct2" &&
        ((args zip ct.tcd.toCase.fieldsTypes) forall (argstyped => isValueOfType(argstyped._1, argstyped._2) < s"${argstyped._1} not a value of type ${argstyped._2}" ))
      case (Lambda(valdefs, body), FunctionType(ins, out)) =>
        variablesOf(e).isEmpty &&
        (valdefs zip ins forall (vdin => isSubtypeOf(vdin._2, vdin._1.getType) < s"${vdin._2} is not a subtype of ${vdin._1.getType}")) &&
        (isSubtypeOf(body.getType, out)) < s"${body.getType} is not a subtype of ${out}"
      case _ => false
    }
  }

  /** Returns true if expr is a value. Stronger than isGround */
  def isValue(e: Expr) = isValueOfType(e, e.getType)
  
  /** Returns a nested string explaining why this expression is typed the way it is.*/
  def explainTyping(e: Expr): String = {
    fold[String]{ (e, se) =>
      e match {
        case FunctionInvocation(id, tps, args) =>
          val tfd = getFunction(id, tps)
          s"$e is of type ${e.getType}" + se.map(child => "\n  " + "\n".r.replaceAllIn(child, "\n  ")).mkString + s" because ${tfd.fd.id.name} was instantiated with ${tfd.fd.tparams.zip(args).map(k => k._1 +":="+k._2).mkString(",")} with type ${tfd.fd.params.map(_.getType).mkString(",")} => ${tfd.fd.returnType}"
        case e =>
          s"$e is of type ${e.getType}" + se.map(child => "\n  " + "\n".r.replaceAllIn(child, "\n  ")).mkString
      }
    }(e)
  }

  def typeParamsOf(expr: Expr): Set[TypeParameter] = {
    collect(e => typeParamsOf(e.getType))(expr)
  }

  // Helpers for instantiateType
  class TypeInstantiator(tps: Map[TypeParameter, Type]) extends TreeTransformer {
    override def transform(tpe: Type): Type = tpe match {
      case tp: TypeParameter => tps.getOrElse(tp, tpe)
      case _ => tpe
    }
  }

  def instantiateType(e: Expr, tps: Map[TypeParameter, Type]): Expr = {
    if (tps.isEmpty) {
      e
    } else {
      new TypeInstantiator(tps).transform(e)
    }
  }
}
