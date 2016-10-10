/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

import utils._

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

    class Normalizer extends SelfTreeTransformer {
      var subst: Map[Variable, Expr] = Map.empty
      var varSubst: Map[Identifier, Identifier] = Map.empty
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
        case None => varSubst.get(id) match {
          case Some(newId) => (newId, tpe)
          case None =>
            val newId = getId(Variable(id, tpe))
            varSubst += id -> newId
            (newId, tpe)
        }
      }

      override def transform(e: Expr): Expr = e match {
        case expr if (!onlySimple || isSimple(expr)) && (variablesOf(expr) & vars).isEmpty =>
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
    val normalized = n.transform(expr)

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

  /** Ensures the closure [[l]] can only be equal to some other closure if they share
    * the same integer identifier [[id]]. This method makes sure this property is
    * preserved after going through [[normalizeStructure(Lambda)]]. */
  def uniquateClosure(id: BigInt, res: Lambda): Lambda = {
    def allArgs(l: Lambda): Seq[ValDef] = l.args ++ (l.body match {
      case l2: Lambda => allArgs(l2)
      case _ => Seq.empty
    })

    val resArgs = allArgs(res)
    if (resArgs.isEmpty) res else {
      /* @nv: This is a hack to ensure that the notion of equality we define on closures
       *      is respected by those returned by the model. The second `Let` is necessary
       *      to keep [[normalizeStructure(Lambda)]] from lifting the first one out of
       *      the closure's body. */
      Lambda(res.args,
        Let(ValDef(FreshIdentifier("id"), IntegerType), IntegerLiteral(id),
          Let(ValDef(FreshIdentifier("denormalize"), resArgs.head.tpe), resArgs.head.toVariable,
            res.body)))
    }
  }

  /** Pre-processing for solvers that handle universal quantification
    * in order to increase the precision of polarity analysis for
    * quantification instantiations.
    */
  def simplifyQuantifications(e: Expr): Expr = {

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

    /* Weaker variant of disjunctive normal form */
    def normalizeClauses(e: Expr): Expr = e match {
      case Not(Not(e)) => normalizeClauses(e)
      case Not(Or(es)) => andJoin(es.map(e => normalizeClauses(Not(e))))
      case Not(Implies(e1, e2)) => and(normalizeClauses(e1), normalizeClauses(Not(e2)))
      case And(es) => andJoin(es map normalizeClauses)
      case _ => e
    }

    normalizeClauses(inlineFunctions(e))
  }

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
    val recursive = Set(tadt, tadt.root)

    def isRecursive(tpe: Type, seen: Set[TypedADTDefinition]): Boolean = tpe match {
      case adt: ADTType =>
        val tadt = adt.getADT
        if (seen(tadt)) {
          false
        } else if (recursive(tadt)) {
          true
        } else tadt match {
          case tcons: TypedADTConstructor =>
            tcons.fieldsTypes.exists(isRecursive(_, seen + tadt))
          case _ => false
        }
      case _ => false
    }

    val tconss = tadt match {
      case tsort: TypedADTSort => tsort.constructors
      case tcons: TypedADTConstructor => Seq(tcons)
    }

    tconss.exists { tcons =>
      tcons.fieldsTypes.forall(tpe => !isRecursive(tpe, Set.empty))
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
        cartesianProduct(seqs, valuesOf(to)) map { case (values, default) => FiniteMap(values, default, from) }
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

    liftToLambdas(expr)
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
      case (FiniteMap(elems, default, kt), MapType(from, to)) =>
        (kt == from) < s"$kt not equal to $from" && (default.getType == to) < s"${default.getType} not equal to $to" &&
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
          val tfd = getFunction(id, tps)
          s"${e.asString} is of type ${e.getType.asString}" +
          se.map(child => "\n  " + "\n".r.replaceAllIn(child, "\n  ")).mkString +
          s" because ${tfd.fd.id.name} was instantiated with " +
          s"${tfd.fd.tparams.zip(tps).map(k => k._1.asString + ":=" + k._2.asString).mkString(",")} " +
          s"with type ${tfd.fd.params.map(_.getType.asString).mkString(",")} => ${tfd.fd.returnType.asString}"
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
