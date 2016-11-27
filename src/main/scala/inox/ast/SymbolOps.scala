/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

import utils._

import scala.collection.mutable.{Map => MutableMap}

/** Provides functions to manipulate [[Expressions.Expr]] in cases where
  * a symbol table is available (and required: see [[ExprOps]] for
  * simpler tree manipulations).
  */
trait SymbolOps { self: TypeOps =>
  import trees._
  import trees.exprOps._
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
      case ADTSelector(e, sel) => Some(adtSelector(e, sel))
      case AsInstanceOf(e, ct) => Some(asInstOf(e, ct))
      case Equals(t1, t2) => Some(equality(t1, t2))
      case Implies(t1, t2) => Some(implies(t1, t2))
      case Plus(t1, t2) => Some(plus(t1, t2))
      case Minus(t1, t2) => Some(minus(t1, t2))
      case Times(t1, t2) => Some(times(t1, t2))
      case And(args) => Some(andJoin(args))
      case Or(args) => Some(orJoin(args))
      case Tuple(args) => Some(tupleWrap(args))
      case Application(e, es) => Some(application(e, es))
      case _ => None
    }
    postMap(step)(expr)
  }

  /** Normalizes the expression expr */
  def normalizeExpression(expr: Expr): Expr = {
    def rec(e: Expr): Option[Expr] = e match {
      case TupleSelect(Let(id, v, b), ts) =>
        Some(Let(id, v, tupleSelect(b, ts, true)))

      case ADTSelector(cc: ADT, id) =>
        Some(adtSelector(cc, id).copiedFrom(e))

      case IfExpr(c, thenn, elze) if thenn == elze =>
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

  /** Returns '''true''' iff the evaluation of expression [[expr]] cannot lead to a crash. */
  def isPure(expr: Expr): Boolean = {
    val callees = collect {
      case fi: FunctionInvocation => Set(fi.tfd.fd)
      case _ => Set.empty[FunDef]
    } (expr)

    val allCallees = callees ++ callees.flatMap(transitiveCallees)
    !(expr +: allCallees.toSeq.map(_.fullBody)).exists {
      expr => exists(isImpureExpr)(expr)
    }
  }

  protected def isImpureExpr(expr: Expr): Boolean = expr match {
    case (_: Assume) | (_: Choose) |
         (_: Division) | (_: Remainder) | (_: Modulo) | (_: AsInstanceOf) => true
    case _ => false
  }

  private val typedIds: MutableMap[Type, List[Identifier]] =
    MutableMap.empty.withDefaultValue(List.empty)

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
  def normalizeStructure(args: Seq[ValDef], expr: Expr, preserveApps: Boolean, onlySimple: Boolean):
                        (Seq[ValDef], Expr, Seq[(Variable, Expr)]) = synchronized {

    val subst: MutableMap[Variable, Expr] = MutableMap.empty
    val varSubst: MutableMap[Identifier, Identifier] = MutableMap.empty

    // Note: don't use clone here, we want to drop the `withDefaultValue` feature of [[typeIds]]
    val remainingIds: MutableMap[Type, List[Identifier]] = MutableMap.empty ++ typedIds.toMap

    def getId(e: Expr, store: Boolean = true): Identifier = {
      val tpe = e.getType
      val newId = remainingIds.get(tpe) match {
        case Some(x :: xs) =>
          remainingIds += tpe -> xs
          x
        case _ =>
          val x = FreshIdentifier("x", true)
          typedIds(tpe) = typedIds(tpe) :+ x
          x
      }
      if (store) subst += Variable(newId, tpe) -> e
      newId
    }

    def transformId(id: Identifier, tpe: Type, store: Boolean = true): Identifier =
      subst.get(Variable(id, tpe)) match {
        case Some(Variable(newId, _)) => newId
        case Some(_) => id
        case None => varSubst.get(id) match {
          case Some(newId) => newId
          case None =>
            val newId = getId(Variable(id, tpe), store = store)
            varSubst += id -> newId
            newId
        }
      }

    def extractMatcher(e: Expr): (Seq[Expr], Seq[Expr] => Expr) = e match {
      case Application(caller, args) =>
        val (es, recons) = extractMatcher(caller)
        (args ++ es, es => {
          val (newArgs, newEs) = es.splitAt(args.size)
          Application(recons(newEs), newArgs)
        })

      case ADTSelector(adt, id) =>
        val (es, recons) = extractMatcher(adt)
        (es, es => ADTSelector(recons(es), id))

      case ElementOfSet(elem, set) =>
        val (es, recons) = extractMatcher(set)
        (elem +: es, { case elem +: es => ElementOfSet(elem, recons(es)) })

      case MultiplicityInBag(elem, bag) =>
        val (es, recons) = extractMatcher(bag)
        (elem +: es, { case elem +: es => MultiplicityInBag(elem, recons(es)) })

      case MapApply(map, key) =>
        val (es, recons) = extractMatcher(map)
        (key +: es, { case key +: es => MapApply(recons(es), key) })

      case FunctionInvocation(id, tps, args) =>
        (args, es => FunctionInvocation(id, tps, es))

      case _ => (Seq(e), es => es.head)
    }

    def outer(vars: Set[Variable], body: Expr): Expr = {
      // this registers the argument images into subst
      val tvars = vars map (v => v.copy(id = transformId(v.id, v.tpe, store = false)))

      def isLocal(e: Expr, path: Path): Boolean = {
        val vs = variablesOf(e)
        val bindings = path.bindings.map(p => p._1.toVariable -> p._2).toMap
        (tvars & (vs.flatMap { v =>
          val tv = varSubst.get(v.id).map(Variable(_, v.tpe))
          tv.toSet ++ tv.flatMap(v => bindings.get(v)).toSet.flatMap(variablesOf)
        })).isEmpty
      }

      def isSatisfiable(path: Path): Option[Boolean] = path.conditions match {
        case Seq() => Some(true)
        case conds =>
          val (posConds, posRest) = conds.partition {
            case IsInstanceOf(v: Variable, adt) if tvars(v) => true
            case _ => false
          }

          val (negConds, negRest) = posRest.partition {
            case Not(IsInstanceOf(v: Variable, adt)) if tvars(v) => true
            case _ => false
          }

          if (negRest.nonEmpty) {
            None
          } else {
            val posAdts = posConds.collect {
              case IsInstanceOf(v: Variable, tpe) if tpe != tpe.getADT.root.toType => v -> tpe
            }.groupBy(_._1).mapValues(_.map(_._2).toSet)

            val negAdts = negConds.collect {
              case Not(IsInstanceOf(v: Variable, tpe)) => v -> tpe
            }.groupBy(_._1).mapValues(_.map(_._2).toSet)

            val results = for (v: Variable <- (posAdts.keys ++ negAdts.keys).toSet) yield {
              val pos = posAdts.getOrElse(v, Set.empty)
              val neg = negAdts.getOrElse(v, Set.empty)

              if (pos.size > 1 || (pos & neg).nonEmpty) {
                Some(false)
              } else {
                val constructors = ((pos ++ neg).head.getADT.root match {
                  case tsort: TypedADTSort => tsort.constructors
                  case tcons: TypedADTConstructor => Seq(tcons)
                }).map(_.toType).toSet

                if (neg == constructors) {
                  Some(false)
                } else {
                  None
                }
              }
            }

            if (results.exists(_ contains false)) {
              Some(false)
            } else if (results.forall(_ contains true)) {
              Some(true)
            } else {
              None
            }
          }
      }

      object normalizer extends transformers.TransformerWithPC {
        val trees: self.trees.type = self.trees
        val symbols: self.symbols.type = self.symbols
        val initEnv = Path.empty

        override protected def rec(e: Expr, path: Path): Expr = e match {
          case Variable(id, tpe) =>
            Variable(transformId(id, tpe), tpe)

          case (_: Application) | (_: MultiplicityInBag) | (_: ElementOfSet) | (_: MapApply) if (
            !isLocal(e, path) &&
            preserveApps
          ) =>
            val (es, recons) = extractMatcher(e)
            val newEs = es.map(rec(_, path))
            recons(newEs)

          case Let(vd, e, b) if (
            isLocal(e, path) &&
            (isSimple(e) || !onlySimple) &&
            ((isSatisfiable(path) contains true) || isPure(e))
          ) =>
            val newId = getId(e)
            rec(replaceFromSymbols(Map(vd.toVariable -> Variable(newId, vd.tpe)), b), path)

          case expr if (
            isLocal(expr, path) &&
            (isSimple(expr) || !onlySimple) &&
            ((isSatisfiable(path) contains true) || isPure(expr))
          ) =>
            Variable(getId(expr), expr.getType)

          case f: Forall =>
            val newBody = outer(vars ++ f.args.map(_.toVariable), f.body)
            Forall(f.args.map(vd => vd.copy(id = varSubst(vd.id))), newBody)

          case l: Lambda =>
            val newBody = outer(vars ++ l.args.map(_.toVariable), l.body)
            Lambda(l.args.map(vd => vd.copy(id = varSubst(vd.id))), newBody)

          case _ =>
            val (vs, es, tps, recons) = deconstructor.deconstruct(e)
            val newVs = vs.map(v => v.copy(id = transformId(v.id, v.tpe, store = false)))
            super.rec(recons(newVs, es, tps), path)
        }
      }

      normalizer.transform(body)
    }

    val newExpr = outer(args.map(_.toVariable).toSet, expr)
    val bindings = args.map(vd => vd.copy(id = varSubst(vd.id)))

    def rec(v: Variable): Seq[Variable] =
      (variablesOf(subst(v)) & subst.keySet - v).toSeq.flatMap(rec) :+ v
    val deps = subst.keys.toSeq.flatMap(rec).distinct.map(v => v -> subst(v))

    (bindings, newExpr, deps)
  }

  def normalizeStructure(e: Expr, onlySimple: Boolean = true): (Expr, Seq[(Variable, Expr)]) = e match {
    case lambda: Lambda =>
      val (args, body, subst) = normalizeStructure(lambda.args, lambda.body, false, onlySimple)
      (Lambda(args, body), subst)

    case forall: Forall =>
      val (args, body, subst) = normalizeStructure(forall.args, forall.body, true, onlySimple)
      (Forall(args, body), subst)

    case _ =>
      val (_, body, subst) = normalizeStructure(Seq.empty, e, false, onlySimple)
      (body, subst)
  }

  /** Ensures the closure [[l]] can only be equal to some other closure if they share
    * the same integer identifier [[id]]. This method makes sure this property is
    * preserved after going through [[normalizeStructure(Lambda)]]. */
  def uniquateClosure(id: Int, res: Lambda): Lambda = {
    def allArgs(l: Lambda): Seq[ValDef] = l.args ++ (l.body match {
      case l2: Lambda => allArgs(l2)
      case _ => Seq.empty
    })

    val resArgs = allArgs(res)
    val unique = if (resArgs.isEmpty) res else {
      /* @nv: This is a hack to ensure that the notion of equality we define on closures
       *      is respected by those returned by the model. */
      Lambda(res.args, Let(
        ValDef(FreshIdentifier("id"), tupleTypeWrap(List.fill(id)(resArgs.head.tpe))),
        tupleWrap(List.fill(id)(resArgs.head.toVariable)),
        res.body
      ))
    }

    val (nl, subst) = normalizeStructure(unique)
    replaceFromSymbols(subst.toMap, nl).asInstanceOf[Lambda]
  }

  /** Generates an instance of type [[tpe]] such that the following holds:
    * {{{constructExpr(i, tpe) == constructExpr(j, tpe)}}} iff {{{i == j}}}.
    */
  def constructExpr(i: Int, tpe: Type): Expr = tpe match {
    case _ if typeCardinality(tpe).exists(_ >= i) =>
      throw FatalError(s"Cardinality ${typeCardinality(tpe)} of type $tpe too high for index $i")
    case BooleanType => BooleanLiteral(i == 0)
    case IntegerType => IntegerLiteral(i)
    case BVType(size) => BVLiteral(i, size)
    case CharType => CharLiteral(i.toChar)
    case RealType => FractionLiteral(i, 1)
    case UnitType => UnitLiteral()
    case tp: TypeParameter => GenericValue(tp, i)
    case TupleType(tps) =>
      val (0, args) = tps.foldLeft((i, Seq[Expr]())) {
        case ((i, args), tpe) => typeCardinality(tpe) match {
          case Some(card) =>
            val fieldCard = i min card
            val arg = constructExpr(fieldCard, tpe)
            (i - fieldCard, args :+ arg)

          case None =>
            val arg = constructExpr(i, tpe)
            (0, args :+ arg)
        }
      }
      Tuple(args)

    case adt: ADTType => adt.getADT match {
      case tcons: TypedADTConstructor =>
        val es = unwrapTuple(constructExpr(i, tupleTypeWrap(tcons.fieldsTypes)), tcons.fieldsTypes.size)
        ADT(tcons.toType, es)

      case tsort: TypedADTSort =>
        def rec(i: Int, tconss: Seq[TypedADTConstructor]): (Int, TypedADTConstructor) = tconss match {
          case tcons +: rest => typeCardinality(tcons.toType) match {
            case None => i -> tcons
            case Some(card) if card > i => i -> tcons
            case Some(card) => rec(i - card, rest)
          }
          case _ => sys.error("Should never happen")
        }

        val (ni, tcons) = rec(i, tsort.constructors)
        constructExpr(ni, tcons.toType)
    }

    case SetType(base) => typeCardinality(base) match {
      case None => FiniteSet(Seq(constructExpr(i, base)), base)
      case Some(card) if card > i => FiniteSet(Seq(constructExpr(i, base)), base)
      case Some(card) =>
        def rec(i: Int, c: Int): Seq[Expr] = {
          val elem = if (i % 2 == 0) None else Some(constructExpr(c, base))
          elem.toSeq ++ rec(i / 2, c + 1)
        }
        FiniteSet(rec(i, 0), base)
    }

    case MapType(from, to) => (typeCardinality(from), typeCardinality(to)) match {
      case (_, Some(1)) =>
        FiniteMap(Seq.empty, constructExpr(0, to), from, to)
      case (Some(x), _) if x <= 1 =>
        FiniteMap(Seq.empty, constructExpr(i, to), from, to)
      case (_, None) =>
        FiniteMap(Seq.empty, constructExpr(i, to), from, to)
      case (None, _) =>
        FiniteMap(Seq(constructExpr(i, from) -> constructExpr(1, to)), constructExpr(0, to), from, to)
      case (Some(i1), Some(i2)) =>
        val dfltIndex = i % i2
        val default = constructExpr(dfltIndex, to)
        def rec(i: Int, c: Int): Seq[(Expr, Expr)] = {
          val elem = if (i % i2 == 0) None else {
            val mod = (i % i2) - 1
            val index = if (mod == dfltIndex) i2 - 1 else mod
            Some(constructExpr(c, from) -> constructExpr(index, to))
          }
          elem.toSeq ++ rec(i / i2, c + 1)
        }
        FiniteMap(rec(i, 0), default, from, to)
    }

    case BagType(base) => if (i == 0) FiniteBag(Seq.empty, base) else {
      val key = constructExpr(0, base)
      FiniteBag(Seq(key -> IntegerLiteral(i)), base)
    }

    case FunctionType(Seq(), to) =>
      Lambda(Seq.empty, constructExpr(i, to))

    case FunctionType(from, to) =>
      uniquateClosure(i, Lambda(from.map(tpe => ValDef(FreshIdentifier("x", true), tpe)), constructExpr(0, to)))
  }

  /** Pre-processing for solvers that handle universal quantification
    * in order to increase the precision of polarity analysis for
    * quantification instantiations.
    */
  def simplifyForalls(e: Expr): Expr = {

    def inlineFunctions(e: Expr): Expr = {
      val fds = functionCallsOf(e).flatMap { fi =>
        val fd = fi.tfd.fd
        transitiveCallees(fd) + fd
      }

      val fdsToInline = fds
        .filterNot(fd => transitivelyCalls(fd, fd))
        .filter(fd => exists { case _: Forall => true case _ => false }(fd.fullBody))
      
      def inline(e: Expr): Expr = {
        val subst = functionCallsOf(e)
          .filter(fi => fdsToInline(fi.tfd.fd))
          .map(fi => fi -> fi.inlined)
        replace(subst.toMap, e)
      }

      fixpoint(inline)(e)
    }

    def inlineForalls(e: Expr): Expr = {
      def liftForalls(args: Seq[ValDef], es: Seq[Expr], recons: Seq[Expr] => Expr): Expr = {
        val (allArgs, allBodies) = es.map {
          case f: Forall =>
            val Forall(args, body) = freshenLocals(f)
            (args, body)
          case e =>
            (Seq[ValDef](), e)
        }.unzip

        forall(args ++ allArgs.flatten, recons(allBodies))
      }

      postMap {
        case Forall(args1, Forall(args2, body)) =>
          Some(forall(args1 ++ args2, body))

        case Forall(args, And(es)) =>
          Some(liftForalls(args, es, andJoin))

        case Forall(args, Or(es)) =>
          Some(liftForalls(args, es, orJoin))

        case Forall(args, Implies(e1, e2)) =>
          Some(liftForalls(args, Seq(e1, e2), es => implies(es(0), es(1))))

        case And(es) => Some(andJoin(SeqUtils.groupWhile(es)(_.isInstanceOf[Forall]).map {
          case Seq(e) => e
          case foralls =>
            val pairs = foralls.collect { case Forall(args, body) => (args, body) }
            val (allArgs, allBodies) = pairs.foldLeft((Seq[ValDef](), Seq[Expr]())) {
              case ((allArgs, bodies), (args, body)) =>
                val available = allArgs.groupBy(_.tpe).mapValues(_.sortBy(_.id.uniqueName))
                val (_, map) = args.foldLeft((available, Map[ValDef, ValDef]())) {
                  case ((available, map), vd) => available.get(vd.tpe) match {
                    case Some(x +: xs) =>
                      val newAvailable = if (xs.isEmpty) {
                        available - vd.tpe
                      } else {
                        available + (vd.tpe -> xs)
                      }
                      (newAvailable, map + (vd -> x))
                    case _ =>
                      (available, map + (vd -> vd))
                  }
                }

                val newBody = replaceFromSymbols(map.mapValues(_.toVariable), body)
                val newArgs = allArgs ++ map.map(_._2).filterNot(allArgs contains _)
                val newBodies = bodies :+ newBody
                (newArgs, newBodies)
            }

            forall(allArgs, andJoin(allBodies))
        }))

        case _ => None
      } (e)
    }

    /* Weaker variant of disjunctive normal form */
    def normalizeClauses(e: Expr): Expr = e match {
      case Not(Not(e)) => normalizeClauses(e)
      case Not(Or(es)) => andJoin(es.map(e => normalizeClauses(Not(e))))
      case Not(Implies(e1, e2)) => and(normalizeClauses(e1), normalizeClauses(Not(e2)))
      case And(es) => andJoin(es map normalizeClauses)
      case _ => e
    }

    normalizeClauses(inlineForalls(inlineFunctions(e)))
  }

  def simplifyLets(expr: Expr): Expr = postMap({
    case Let(v1, Let(v2, e2, b2), b1) =>
      Some(Let(v2, e2, Let(v1, b2, b1)))

    case Let(v, e, v2) if v.toVariable == v2 =>
      Some(e)

    case Let(v, ts @ (
      TupleSelect(_: Variable, _) |
      ADTSelector(_: Variable, _) |
      FiniteMap(Seq(), _, _, _)   |
      FiniteBag(Seq(), _)         |
      FiniteSet(Seq(), _)
    ), b) =>
      Some(replaceFromSymbols(Map(v -> ts), b))

    case Let(vd, e, b) =>
      exprOps.count { case v: Variable if vd.toVariable == v => 1 case _ => 0 } (b) match {
        case 0 if isPure(e) => Some(b)
        case 1 if isPure(e) => Some(replaceFromSymbols(Map(vd -> e), b))
        case _ => None
      }

    case _ => None
  }, applyRec = true)(expr)

  /** Fully expands all let expressions. */
  def expandLets(expr: Expr): Expr = {
    def rec(ex: Expr, s: Map[Variable,Expr]) : Expr = ex match {
      case v: Variable if s.isDefinedAt(v) => rec(s(v), s)
      case l @ Let(i,e,b) => rec(b, s + (i.toVariable -> rec(e, s)))
      case i @ IfExpr(t1,t2,t3) => IfExpr(rec(t1, s),rec(t2, s),rec(t3, s)).copiedFrom(i)
      case n @ Operator(args, recons) =>
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

    rec(expr, Map.empty)
  }

  /** Lifts lets to top level.
    *
    * Does not push any used variable out of scope.
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

  private def hasInstance(tadt: TypedADTDefinition): Boolean = {
    def rec(adt: TypedADTDefinition, seen: Set[TypedADTDefinition]): Boolean = {
      if (seen(adt)) false else (adt match {
        case tsort: TypedADTSort =>
          tsort.constructors.exists(rec(_, seen + tsort))

        case tcons: TypedADTConstructor =>
          tcons.fieldsTypes.flatMap(tpe => typeOps.collect {
            case t: ADTType => Set(t.getADT)
            case _ => Set.empty[TypedADTDefinition]
          } (tpe)).forall(rec(_, seen + tcons))
      })
    }

    rec(tadt, Set.empty)
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
    case MapType(fromType, toType)  => FiniteMap(Seq(), simplestValue(toType), fromType, toType)
    case TupleType(tpes)            => Tuple(tpes.map(simplestValue))

    case adt @ ADTType(id, tps) =>
      val tadt = adt.getADT
      if (!hasInstance(tadt)) scala.sys.error(adt +" does not seem to be well-founded")

      val tcons @ TypedADTConstructor(cons, tps) = tadt match {
        case tsort: TypedADTSort =>
          tsort.constructors.filter(hasInstance(_)).sortBy(_.fields.size).head
        case tcons: TypedADTConstructor => tcons
      }

      ADT(tcons.toType, tcons.fieldsTypes.map(simplestValue))

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
        cartesianProduct(seqs, valuesOf(to)) map { case (values, default) => FiniteMap(values, default, from, to) }
      case adt: ADTType => adt.getADT match {
        case tcons: TypedADTConstructor =>
          cartesianProduct(tcons.fieldsTypes map valuesOf) map (ADT(adt, _))
        case tsort: TypedADTSort =>
          interleave(tsort.constructors.map(tcons => valuesOf(tcons.toType)))
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

      case nop @ Deconstructor(ts, op) => {
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

  def collectWithPaths[T](f: PartialFunction[Expr, T])(expr: Expr): Seq[(T, Path)] = {

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

        case Assume(pred, body) =>
          rec(pred, path) ++
          rec(body, path withCond pred)

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

        case Deconstructor(es, _) =>
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

  object InvocationExtractor {
    type Invocation = (Identifier, Seq[Type], Seq[Either[Identifier, Int]], Seq[Expr])

    private def flatSelectors(expr: Expr): Option[Invocation] = expr match {
      case ADTSelector(IsTyped(e, FunctionContainerType()), sid) => flatSelectors(e).map {
        case (id, tps, path, args) => (id, tps, path :+ Left(sid), args)
      }
      case TupleSelect(IsTyped(e, FunctionContainerType()), i) => flatSelectors(e).map {
        case (id, tps, path, args) => (id, tps, path :+ Right(i), args)
      }
      case fi @ FunctionInvocation(id, tps, args) => Some((id, tps, Seq.empty, args))
      case _ => None
    }

    private def flatInvocation(expr: Expr, specialize: Boolean): Option[Invocation] = expr match {
      case fi @ FunctionInvocation(id, tps, args) => Some((id, tps, Seq.empty, args))
      case Application(caller, args) => flatInvocation(caller, specialize) match {
        case Some((id, tps, path, prevArgs)) => Some((id, tps, path, prevArgs ++ args))
        case None => None
      }
      case _ => if (specialize) flatSelectors(expr) else None
    }

    def extract(expr: Expr, specialize: Boolean = true): Option[Invocation] = expr match {
      case IsTyped(f: FunctionInvocation, ft: FunctionType) => None
      case IsTyped(f: Application, ft: FunctionType) => None
      case IsTyped(f: FunctionInvocation, FunctionContainerType()) if specialize => None
      case FunctionInvocation(id, tps, args) => Some((id, tps, Seq.empty, args))
      case f: Application => flatInvocation(f, specialize)
      case _ => None
    }

    object Specialized { def unapply(expr: Expr): Option[Invocation] = extract(expr, specialize = true) }
    object Unspecialized { def unapply(expr: Expr): Option[Invocation] = extract(expr, specialize = false) }
  }

  def firstOrderCallsOf(expr: Expr, specialize: Boolean = true): Set[InvocationExtractor.Invocation] =
    collect { e => InvocationExtractor.extract(e, specialize).toSet }(expr)

  object ApplicationExtractor {
    private def flatApplication(expr: Expr): Option[(Expr, Seq[Expr])] = expr match {
      case Application(caller: Application, args) => flatApplication(caller) match {
        case Some((c, prevArgs)) => Some((c, prevArgs ++ args))
        case None => None
      }
      case Application(caller, args) => Some((caller, args))
      case _ => None
    }

    def extract(expr: Expr, specialize: Boolean = true): Option[(Expr, Seq[Expr])] = expr match {
      case IsTyped(f: Application, ft: FunctionType) => None
      case _ => InvocationExtractor.extract(expr, specialize) match {
        case Some(_) => None
        case None => expr match {
          case f: Application => flatApplication(f)
          case _ => None
        }
      }
    }

    object Specialized { def unapply(expr: Expr): Option[(Expr, Seq[Expr])] = extract(expr, specialize = true) }
    object Unspecialized { def unapply(expr: Expr): Option[(Expr, Seq[Expr])] = extract(expr, specialize = false) }
  }

  def firstOrderAppsOf(expr: Expr, specialize: Boolean = true): Set[(Expr, Seq[Expr])] =
    collect[(Expr, Seq[Expr])](e => ApplicationExtractor.extract(e).toSet)(expr)

  def simplifyHOFunctions(expr: Expr, simplify: Boolean = true): Expr = {

    def pushDown(expr: Expr, recons: Expr => Expr): Expr = expr match {
      case IfExpr(cond, thenn, elze) =>
        IfExpr(cond, pushDown(thenn, recons), pushDown(elze, recons))
      case Let(i, e, b) =>
        Let(i, e, pushDown(b, recons))
      case Assume(pred, body) =>
        Assume(pred, pushDown(body, recons))
      case _ => recons(expr)
    }

    def traverse(expr: Expr, lift: Expr => Expr): Expr = {
      def extract(expr: Expr, build: Boolean) = if (build) lift(expr) else expr

      def rec(expr: Expr, build: Boolean): Expr = extract(expr match {
        case Application(caller, args) =>
          val newArgs = args.map(rec(_, true))
          val newCaller = rec(caller, false)
          Application(newCaller, newArgs)
        case FunctionInvocation(id, tps, args) =>
          val newArgs = args.map(rec(_, true))
          FunctionInvocation(id, tps, newArgs)
        case l @ Lambda(args, body) =>
          val newBody = rec(body, true)
          Lambda(args, newBody)
        case Deconstructor(es, recons) => recons(es.map(rec(_, build)))
      }, build)

      rec(lift(expr), true)
    }

    def liftToLambdas(expr: Expr) = {
      def lift(expr: Expr): Expr = expr.getType match {
        case FunctionType(from, to) => expr match {
          case _ : Lambda => expr
          case _ : Variable => expr
          case e =>
            val args = from.map(tpe => ValDef(FreshIdentifier("x", true), tpe))
            val application = pushDown(expr, Application(_, args.map(_.toVariable)))
            Lambda(args, lift(application))
        }
        case _ => expr
      }

      traverse(expr, lift)
    }

    def liftContainers(expr: Expr): Expr = {
      def lift(expr: Expr): Expr = expr.getType match {
        case tpe @ FunctionContainerType() => expr match {
          case _ : ADT => expr
          case _ : Tuple => expr
          case _ : Variable => expr
          case e => tpe match {
            case adt @ RecordType(tcons) =>
              val castExpr = if (tcons.id == adt.id) expr else AsInstanceOf(expr, tcons.toType)
              val fields = tcons.fields.map(vd => pushDown(castExpr, ADTSelector(_, vd.id)))
              ADT(tcons.toType, fields)
            case TupleType(tpes) =>
              Tuple(tpes.indices.map(i => pushDown(expr, TupleSelect(_, i + 1))))
          }
        }
        case _ => expr
      }

      traverse(expr, lift)
    }

    def simplifyContainers(expr: Expr): Expr = postMap {
      case ADTSelector(IsTyped(e, FunctionContainerType()), id) =>
        val newExpr = pushDown(e, adtSelector(_, id))
        if (newExpr != expr) Some(newExpr) else None
      case TupleSelect(IsTyped(e, FunctionContainerType()), i) =>
        val newExpr = pushDown(e, tupleSelect(_, i, true))
        if (newExpr != expr) Some(newExpr) else None
      case _ => None
    } (expr)

    liftToLambdas(if (simplify) {
      simplifyContainers(liftContainers(expr))
    } else {
      expr
    })
  }

  def liftAssumptions(expr: Expr): (Seq[Expr], Expr) = {
    val vars = variablesOf(expr)
    var assumptions: Seq[Expr] = Seq.empty

    object transformer extends transformers.TransformerWithPC {
      val trees: self.trees.type = self.trees
      val symbols: self.symbols.type = self.symbols
      val initEnv = Path.empty

      override protected def rec(e: Expr, path: Path): Expr = e match {
        case Assume(pred, body) if (variablesOf(pred) ++ path.variables) subsetOf vars =>
          assumptions :+= path implies pred
          rec(body, path withCond pred)
        case _ => super.rec(e, path)
      }
    }

    val newExpr = transformer.transform(expr)
    (assumptions, newExpr)
  }

  def simplifyAssumptions(expr: Expr): Expr = postMap {
    case Assume(pred, body) =>
      val (predAssumptions, newPred) = liftAssumptions(pred)
      val (bodyAssumptions, newBody) = liftAssumptions(body)
      Some(assume(andJoin(predAssumptions ++ (newPred +: bodyAssumptions)), newBody))
    case _ => None
  } (expr)

  def simplifyFormula(e: Expr, simplify: Boolean = true): Expr = {
    if (simplify) {
      val simp: Expr => Expr =
        ((e: Expr) => simplifyHOFunctions(e))    compose
        ((e: Expr) => simplifyByConstructors(e)) compose
        ((e: Expr) => simplifyAssumptions(e))    compose
        ((e: Expr) => simplifyForalls(e))        compose
        ((e: Expr) => simplifyLets(e))
      fixpoint(simp)(e)
    } else {
      simplifyHOFunctions(e, simplify = false)
    }
  }

  // Use this only to debug isValueOfType
  private implicit class BooleanAdder(b: Boolean) {
    @inline def <(msg: => String) = {/*if(!b) println(msg); */b}
  }

  /** Returns true if expr is a value of type t */
  def isValueOfType(e: Expr, t: Type): Boolean = {
    def unWrapSome(s: Expr) = s match {
      case ADT(_, Seq(a)) => a
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
      case (FiniteMap(elems, default, kt, vt), MapType(from, to)) =>
        (kt == from) < s"$kt not equal to $from" && (vt == to) < s"${default.getType} not equal to $to" &&
        isValueOfType(default, to) < s"${default} not a value of type $to" &&
        (elems forall (kv => isValueOfType(kv._1, from) < s"${kv._1} not a value of type $from" && isValueOfType(unWrapSome(kv._2), to) < s"${unWrapSome(kv._2)} not a value of type ${to}" ))
      case (ADT(adt, args), adt2: ADTType) =>
        isSubtypeOf(adt, adt2) < s"$adt not a subtype of $adt2" &&
        ((args zip adt.getADT.toConstructor.fieldsTypes) forall (argstyped => isValueOfType(argstyped._1, argstyped._2) < s"${argstyped._1} not a value of type ${argstyped._2}" ))
      case (Lambda(valdefs, body), FunctionType(ins, out)) =>
        variablesOf(e).isEmpty &&
        (valdefs zip ins forall (vdin => isSubtypeOf(vdin._2, vdin._1.getType) < s"${vdin._2} is not a subtype of ${vdin._1.getType}")) &&
        isSubtypeOf(body.getType, out) < s"${body.getType} is not a subtype of $out"
      case _ => false
    }
  }

  /** Returns true if expr is a value. Stronger than isGround */
  def isValue(e: Expr) = isValueOfType(e, e.getType)

  /** Returns a nested string explaining why this expression is typed the way it is.*/
  def explainTyping(e: Expr)(implicit opts: PrinterOptions): String = {
    fold[String]{ (e, se) =>
      e match {
        case FunctionInvocation(id, tps, args) =>
          lookupFunction(id, tps) match {
            case Some(tfd) =>
              s"${e.asString} is of type ${e.getType.asString}" +
              se.map(child => "\n  " + "\n".r.replaceAllIn(child, "\n  ")).mkString +
              s" because ${tfd.fd.id.name} was instantiated with " +
              s"${tfd.fd.tparams.zip(tps).map(k => k._1.asString + ":=" + k._2.asString).mkString(",")} " +
              s"with type ${tfd.fd.params.map(_.getType.asString).mkString("(", ",", ")")} => " +
              s"${tfd.fd.returnType.asString}"
            case None =>
              s"${e.asString} is of type ${e.getType.asString}" +
              se.map(child => "\n  " + "\n".r.replaceAllIn(child, "\n  ")).mkString +
              s" but couldn't find function $id"
          }
        case e =>
          s"${e.asString} is of type ${e.getType.asString}" +
          se.map(child => "\n  " + "\n".r.replaceAllIn(child, "\n  ")).mkString
      }
    }(e)
  }

  def typeParamsOf(expr: Expr): Set[TypeParameter] = {
    collect(e => typeParamsOf(e.getType))(expr)
  }

  // Helpers for instantiateType
  class TypeInstantiator(tps: Map[TypeParameter, Type]) extends SelfTreeTransformer {
    override def transform(tpe: Type): Type = tpe match {
      case tp: TypeParameter => tps.getOrElse(tp, super.transform(tpe))
      case _ => super.transform(tpe)
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
