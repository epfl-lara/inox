/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package certificates

/** Checks the simplifications of a certificate (see `certificates/README.md`): the steps that
  * rewrite the body of each function of the program that the solver was given into the body
  * that the source definitions define it with, and each expression that the solver was given
  * into the expression of its source.
  *
  * The steps are the ones that the simplifiers of the solver recorded as they ran: the checker
  * doesn't simplify, it checks each step. What a step shows is that the rewritten term refines
  * the term: wherever the term has a value, the rewritten term has the same value. A solution of
  * the original query over the original program is then one of the simplified query over the
  * simplified program, which the rest of the certificate shows has none. This is not enough
  * where functions are compared, by what they give on each input, including where they have no
  * value: the steps are not checked when the program compares functions, and the certificate
  * then holds over the simplified program only.
  *
  * A step `(<rule> <position> <subterm>)` gives the rule that the simplifier applied, a position
  * of the term (the indices of the operands to descend into, where the operator of a term is at
  * index 0), and the subterm that the step puts there. The position is that of the smallest
  * subterm outside of which the step leaves the term as it is. The checker checks that the rule
  * rewrites the subterm at the position, or one of the subterms around it, into what it becomes,
  * under the facts of its position: the conditions that hold where evaluation reaches it (those
  * of the conditionals, the operands before it of a conjunction or a disjunction, and the
  * assumptions on the way),
  * and the values of the `let`s above it. The rules are:
  *  - `logic`: the atoms of the two subterms are their maximal subterms that are not `not`,
  *    `and`, `or`, `=>`, `ite`, `assume`, `let` or a Boolean literal. The step holds if, however
  *    the atoms evaluate (to no value, or to a value, which for a Boolean atom is `true` or
  *    `false`) consistently with the facts and with the constructors (a value is of one
  *    constructor of its datatype, and a construction is of its constructor), the subterm
  *    evaluates to no value, or to the value of the rewritten one. The connectives evaluate from
  *    left to right, as Inox's do. A comparison `(<= a b)` is the negation of `(> a b)`,
  *    `(< a b)` that of `(>= a b)`, an equality is that of its operands in either order, and
  *    `(= t t)` has no value or holds;
  *  - `unfold`: a call of a function of the program becomes the function's original body, at the
  *    sorts of the call, under `let`s that bind its parameters to the arguments, where no
  *    argument mentions a parameter that is bound before it;
  *  - `beta`: the application of a lambda becomes the lambda's body, under `let`s that bind its
  *    parameters to the arguments;
  *  - `expand`: a variable becomes the value that a `let` above binds it to;
  *  - `select`: a selector of a construction, or of a variable that a `let` above binds to a
  *    construction, becomes the field of the construction, and the selection of an element of a
  *    tuple becomes the element;
  *  - `eta`: the construction of the fields of a term, which is of the constructor, becomes the
  *    term;
  *  - `bind`: a term becomes itself under a `let` that binds a variable that it doesn't mention
  *    to one of its subterms that is evaluated whenever the term has a value;
  *  - `lift`: a `let` or an assumption that is an operand of a term, and is evaluated whenever
  *    the term is (the first operand of a connective, or any operand of an application), becomes
  *    the term's parent, where the other operands don't mention the variables of the `let`;
  *  - `merge`: a `forall` over a `forall`, or an `exists` over an `exists`, becomes one quantifier
  *    over the variables of both;
  *  - `unused`: a quantifier loses variables that its body doesn't mention and whose sorts have
  *    values, a `forall` over `true` becomes `true`, and an `exists` over `false` becomes `false`;
  *  - `prenex`: a `forall` over a conjunction, a disjunction or an implication, takes the
  *    variables of some of the `forall`s that are operands of the connective, whose sorts have
  *    values. A quantifier doesn't come out of the premise of an implication, where it would be
  *    existential;
  *  - `arith`: a term over `+`, `-` and `*` becomes one that is the same polynomial, over
  *    subterms that are evaluated whenever the term is, an equality between terms that are the
  *    same polynomial becomes `true`, and one between literals that differ becomes `false`;
  *  - `rename`: a term becomes itself, up to the names of the variables that it binds.
  * Substitutions refuse to capture a variable.
  *
  * The simplifiers name each of their rewrites, including those that no rule above tells (the
  * evaluation of a ground term, say). A step of a rule that the checker doesn't know is applied
  * as it is given, and the certificate then holds over the simplified program only: the checker
  * reports the rules. A step of a rule that it knows, and which doesn't hold, makes the
  * certificate fail, and so does a step of `unrecorded`: what a simplifier did without naming it,
  * which is a simplifier to fix.
  *
  * The source of an expression names subterms (the lambdas, and the instantiations of
  * quantifiers): the steps end at the source where each name is its subterm. A name is a symbol
  * that is neither of the original expression nor of the program. That it stands for its subterm
  * is trusted, as it is by the check of the sources. The source also has `(assume q true)` for a
  * quantifier `q` that must hold for the expression to, which the checker checks of where it is:
  * the expression then holds wherever the one with `q` does. */
object Simplifications {
  import Checker._

  private def app(op: String, args: SExpr*): SExpr = SList(Atom(op) :: args.toList)

  private val quantifiers = Set("forall", "exists", "lambda", "choose")

  // Terms

  /** The kind of a binder, the names of its variables, its declarations and its body. */
  private object Binder {
    def unapply(t: SExpr): Option[(String, List[String], List[SExpr], SExpr)] = t match {
      case SList(List(Atom(q), SList(vars), body)) if quantifiers(q) =>
        val names = vars.map { case SList(Atom(x) :: _) => x; case other => fail(s"$other is not a variable") }
        Some((q, names, vars, body))
      case SList(List(Atom("let"), SList(bindings), body)) =>
        val names = bindings.map { case SList(List(Atom(x), _)) => x; case other => fail(s"$other is not a binding") }
        Some(("let", names, bindings, body))
      case _ => None
    }
  }

  private def free(t: SExpr): Set[String] = t match {
    case Atom(x) => Set(x)
    case Binder(kind, names, decls, body) =>
      val inDecls = decls.flatMap {
        case SList(_ :: rest) => rest.flatMap(free)
        case _ => Nil
      }
      inDecls.toSet ++ (free(body) -- names)
    case SList(items) => items.flatMap(free).toSet
  }

  /** `t` where the free atoms that `m` maps are their values. It fails rather than capture a
    * variable. */
  private def subst(t: SExpr, m: Map[String, SExpr]): SExpr = if (m.isEmpty) t else t match {
    case Atom(x) => m.getOrElse(x, t)
    case Binder(kind, names, decls, body) =>
      val inner = m -- names
      val used = inner.filter((x, _) => free(body)(x))
      val captured = names.toSet & used.values.flatMap(free).toSet
      if (captured.nonEmpty) fail(s"the substitution in $t captures ${captured.mkString(", ")}")
      val newDecls = decls.map {
        case SList(List(x, v)) if kind == "let" => SList(List(x, subst(v, m)))
        case SList(x :: sorts) => SList(x :: sorts.map(subst(_, m)))
        case d => d
      }
      SList(List(Atom(kind), SList(newDecls), subst(body, inner)))
    case SList(items) => SList(items.map(subst(_, m)))
  }

  /** Whether `a` and `b` are the same up to the names of their bound variables. */
  def alpha(a: SExpr, b: SExpr, env: Map[String, String] = Map(), rev: Map[String, String] = Map()): Boolean = (a, b) match {
    case (Atom(x), Atom(y)) => env.get(x) match {
      // the innermost binders of `x` and of `y` are the same one
      case Some(z) => z == y && rev.get(y).contains(x)
      case None => !rev.contains(y) && x == y
    }
    case (Binder(k1, n1, d1, b1), Binder(k2, n2, d2, b2)) =>
      k1 == k2 && n1.size == n2.size && n1.distinct.size == n1.size && n2.distinct.size == n2.size && (d1 zip d2).forall {
        case (SList(_ :: r1), SList(_ :: r2)) => r1.size == r2.size && (r1 zip r2).forall(alpha(_, _, env, rev))
        case _ => false
      } && alpha(b1, b2, env ++ (n1 zip n2), rev ++ (n2 zip n1))
    case (SList(i1), SList(i2)) => i1.size == i2.size && (i1 zip i2).forall(alpha(_, _, env, rev))
    case _ => false
  }

  /** `t` with its bound variables named by their depth, so that terms that are the same up to the
    * names of their bound variables are equal. */
  private def canonical(t: SExpr, env: Map[String, String] = Map(), depth: Int = 0, prefix: String = "%"): SExpr = t match {
    case Atom(x) => env.get(x).map(Atom(_)).getOrElse(t)
    case Binder(kind, names, decls, body) =>
      val fresh = names.zipWithIndex.map((x, i) => x -> s"$prefix${depth}_$i")
      val inner = env ++ fresh
      val newDecls = decls.zip(fresh).map {
        case (SList(List(_, v)), (_, n)) if kind == "let" => SList(List(Atom(n), canonical(v, env, depth, prefix)))
        case (SList(_ :: sorts), (_, n)) => SList(Atom(n) :: sorts.map(canonical(_, env, depth, prefix)))
        case (d, _) => d
      }
      SList(List(Atom(kind), SList(newDecls), canonical(body, inner, depth + 1, prefix)))
    case SList(items) => SList(items.map(canonical(_, env, depth, prefix)))
  }

  private type Pos = List[Int]

  private def at(t: SExpr, pos: Pos): SExpr = pos match {
    case Nil => t
    case i :: rest => t match {
      case SList(items) if i >= 0 && i < items.size => at(items(i), rest)
      case _ => fail(s"$t has no subterm at ${pos.mkString(" ")}")
    }
  }

  private def replace(t: SExpr, pos: Pos, by: SExpr): SExpr = pos match {
    case Nil => by
    case i :: rest => t match {
      case SList(items) if i >= 0 && i < items.size => SList(items.updated(i, replace(items(i), rest, by)))
      case _ => fail(s"$t has no subterm at ${pos.mkString(" ")}")
    }
  }

  private val keywords = quantifiers ++ Set("let", "as", "_", "not", "and", "or", "=>", "ite", "assume", "=", "match")

  /** An application of a symbol to its arguments, `(f args)` or `((as f S) args)`, or a constant,
    * `f` or `(as f S)`. */
  private object Applied {
    def unapply(t: SExpr): Option[(String, List[SExpr])] = t match {
      case SList(Atom("as") :: Atom(f) :: _) => Some((f, Nil))
      case SList(SList(Atom("as") :: Atom(f) :: _) :: args) => Some((f, args))
      case SList(Atom(f) :: args) if !keywords(f) => Some((f, args))
      case Atom(f) => Some((f, Nil))
      case _ => None
    }
  }

  /** The sorts that `((as f (S ..)) ..)` or `(as f (S ..))` instantiates `f` at. */
  private def sortArguments(t: SExpr): List[SExpr] = t match {
    case SList(List(Atom("as"), _, SList(sorts))) => sorts
    case SList(SList(List(Atom("as"), _, SList(sorts))) :: _) => sorts
    case _ => Nil
  }

  /** A selection `((_ tuple.select i) e)` or `((as (_ tuple.select i) S) e)`: the index and the term. */
  private object TupleSelect {
    def unapply(t: SExpr): Option[(Int, SExpr)] = t match {
      case SList(List(SList(List(Atom("_"), Atom("tuple.select"), Atom(i))), e)) if i.toIntOption.nonEmpty => Some((i.toInt, e))
      case SList(List(SList(List(Atom("as"), SList(List(Atom("_"), Atom("tuple.select"), Atom(i))), _)), e)) if i.toIntOption.nonEmpty => Some((i.toInt, e))
      case _ => None
    }
  }

  /** A tester `((_ is C) e)`, `((as (_ is C) S) e)` or `(is-C e)`: the constructor and the term. */
  private object Tester {
    def unapply(t: SExpr): Option[(String, SExpr)] = t match {
      case SList(List(SList(List(Atom("_"), Atom("is"), Atom(c))), e)) => Some((c, e))
      case SList(List(SList(List(Atom("as"), SList(List(Atom("_"), Atom("is"), Atom(c))), _)), e)) => Some((c, e))
      case SList(List(Atom(tester), e)) if tester.startsWith("is-") => Some((tester.drop(3), e))
      case _ => None
    }
  }

  // The program

  /** A function of the program: its parameters, the parameters of its sorts, and its body. */
  private final case class Function(params: List[String], tparams: List[String], body: SExpr)

  /** The functions that `commands` define, by symbol, the constructors of their datatypes, by
    * symbol, with the constructors of the datatype, and their selectors, with their constructor
    * and index. */
  private final class Program(commands: List[SExpr]) {
    val functions = scala.collection.mutable.Map[String, Function]()
    val constructors = scala.collection.mutable.Map[String, List[String]]()
    val selectors = scala.collection.mutable.Map[String, (String, Int)]()
    /** The datatypes, by name: their parameters, and the sorts of the fields of each constructor. */
    val datatypes = scala.collection.mutable.Map[String, (List[String], List[List[SExpr]])]()

    private def params(ps: List[SExpr]) = ps.map { case SList(Atom(x) :: _) => x; case other => fail(s"$other is not a parameter") }
    private def datatype(cs: List[SExpr]): Unit = {
      val names = cs.collect { case SList(Atom(c) :: _) => c }
      cs.foreach {
        case SList(Atom(c) :: fields) =>
          constructors(c) = names
          for (case (SList(Atom(s) :: _), i) <- fields.zipWithIndex) selectors(s) = (c, i)
        case _ =>
      }
    }

    commands.foreach {
      case SList(List(Atom("define-fun" | "define-fun-rec"), Atom(f), SList(ps), _, body)) => functions(f) = Function(params(ps), Nil, body)
      case SList(List(Atom("define-fun" | "define-fun-rec"), SList(List(Atom("par"), SList(tps), SList(List(Atom(f), SList(ps), _, body)))))) =>
        functions(f) = Function(params(ps), tps.map(_.toString), body)
      case SList(List(Atom("define-funs-rec"), SList(decls), SList(bodies))) if decls.size == bodies.size => (decls zip bodies).foreach {
        case (SList(List(Atom(f), SList(ps), _)), body) => functions(f) = Function(params(ps), Nil, body)
        case (SList(List(Atom("par"), SList(tps), SList(List(Atom(f), SList(ps), _)))), body) =>
          functions(f) = Function(params(ps), tps.map(_.toString), body)
        case (other, _) => fail(s"$other is not the declaration of a function")
      }
      case SList(List(Atom("declare-datatypes"), SList(names), SList(decls))) if names.size == decls.size => (names zip decls).foreach {
        case (SList(Atom(d) :: _), SList(List(Atom("par"), SList(ps), SList(cs)))) => datatype(cs); declare(d, ps.map(_.toString), cs)
        case (SList(Atom(d) :: _), SList(cs)) => datatype(cs); declare(d, Nil, cs)
        case _ =>
      }
      case SList(List(Atom("declare-datatype"), Atom(d), SList(cs))) => datatype(cs); declare(d, Nil, cs)
      case _ =>
    }

    private def declare(d: String, params: List[String], cs: List[SExpr]): Unit =
      datatypes(d) = (params, cs.collect { case SList(Atom(_) :: fields) => fields.collect { case SList(List(_, s)) => s } })

    /** Whether the sort `s` has values, as far as the checker can tell: it doesn't decide the
      * sorts with a refinement, nor the sort parameters, which may stand for sorts without values. */
    def inhabited(s: SExpr, seen: Set[String] = Set()): Boolean = s match {
      case Atom("Int" | "Bool" | "Real" | "String" | "Char" | "UnitTuple") => true
      case SList(List(Atom("_"), Atom("BitVec"), _)) => true
      case SList(Atom("!") :: base :: annotations) =>
        !annotations.contains(Atom(":restrict")) && inhabited(base, seen)
      case SList(List(Atom("Set" | "Bag"), _)) => true
      case SList(List(Atom("Array"), _, to)) => inhabited(to, seen)
      case SList(Atom("->") :: sorts) if sorts.nonEmpty => inhabited(sorts.last, seen)
      case SList(Atom("Tuple") :: sorts) => sorts.forall(inhabited(_, seen))
      case Atom(d) if datatypes.contains(d) => datatypeInhabited(d, Nil, seen)
      case SList(Atom(d) :: args) if datatypes.contains(d) => datatypeInhabited(d, args, seen)
      case _ => false
    }

    private def datatypeInhabited(d: String, args: List[SExpr], seen: Set[String]): Boolean = {
      val (params, constructors) = datatypes(d)
      val key = (d :: args.map(_.toString)).mkString(" ")
      !seen(key) && params.size == args.size && constructors.exists(_.forall { field =>
        inhabited(subst(field, params.zip(args).toMap), seen + key)
      })
    }

    /** Whether `t` is a construction: the constructor, if it is one. */
    def construction(t: SExpr): Option[(String, List[SExpr])] = t match {
      case Applied(c, args) if constructors.contains(c) => Some((c, args))
      case _ => None
    }
  }

  // Facts

  /** What holds at a position: the conditions that hold where evaluation reaches it, and the
    * values of the `let`s above it. */
  private final case class Facts(conditions: List[SExpr], bindings: Map[String, SExpr]) {
    def ++(cs: Seq[SExpr]): Facts = copy(conditions = conditions ++ cs)
    /** Without what mentions the variables `names`, which a binder rebinds. */
    def without(names: Set[String]): Facts =
      Facts(conditions.filter(c => (free(c) & names).isEmpty),
        bindings.filter((x, v) => !names(x) && (free(v) & names).isEmpty))
  }

  /** The facts at position `pos` of `t`. */
  private def facts(t: SExpr, pos: Pos, outer: Facts = Facts(Nil, Map())): Facts = pos match {
    case Nil => outer
    case i :: rest =>
      val inner: Facts = t match {
        case SList(Atom("and") :: es) => outer ++ es.take(i - 1)
        case SList(Atom("or") :: es) => outer ++ es.take(i - 1).map(app("not", _))
        case SList(Atom("=>") :: es) => outer ++ es.take(i - 1)
        case SList(List(Atom("ite"), c, _, _)) if i == 2 => outer ++ List(c)
        case SList(List(Atom("ite"), c, _, _)) if i == 3 => outer ++ List(app("not", c))
        case SList(List(Atom("assume"), p, _)) if i == 2 => outer ++ List(p)
        case Binder("let", names, bindings, _) if i == 2 =>
          val values = bindings.collect { case SList(List(Atom(x), v)) => x -> v }
          val f = outer.without(names.toSet)
          f.copy(bindings = f.bindings ++ values.filter((_, v) => (free(v) & names.toSet).isEmpty))
        case Binder(q, names, _, _) if i == 2 =>
          outer.without(names.toSet)
        case _ => outer
      }
      t match {
        case SList(items) if i >= 0 && i < items.size => facts(items(i), rest, inner)
        case _ => fail(s"$t has no subterm at ${pos.mkString(" ")}")
      }
  }

  // The logic rule

  /** What an atom evaluates to: no value, `true`, `false`, or a value that isn't known. */
  private enum Value { case NoValue, True, False, Known }

  /** The result of a term: no value, a Boolean, or the value of a term. */
  private sealed trait Result
  private case object Stuck extends Result
  private final case class Bool(b: Boolean) extends Result
  private final case class Term(t: SExpr) extends Result

  /** An atom whose value evaluation needs, as a Boolean or as a value. */
  private final case class Need(atom: SExpr, boolean: Boolean) extends Exception(null, null, false, false)

  /** The symbols of `t` that are not those of the syntax of terms. */
  private def symbolsOf(t: SExpr): Set[String] = t match {
    case Atom(x) => if (keywords(x) || x == "true" || x == "false" || x.headOption.forall(c => c.isDigit || c == '"' || c == '#')) Set() else Set(x)
    case SList(items) => items.flatMap(symbolsOf).toSet
  }

  /** Checks that `rhs` refines `lhs` under `allFacts`, and says how they differ otherwise. A `let`
    * binds its variables to the values of their terms, when all of them have one. */
  private final class Logic(program: Program, allFacts: List[SExpr]) {
    // the atoms are named apart from the terms, whose bound variables are named by `canonical` too
    private def canonical(t: SExpr): SExpr = Simplifications.canonical(t, prefix = "^")

    /** Only the facts that share symbols with the terms, through other facts or not, bear on them. */
    private def relevant(lhs: SExpr, rhs: SExpr): List[SExpr] = {
      var symbols = symbolsOf(lhs) ++ symbolsOf(rhs)
      var kept = List.empty[SExpr]
      var rest = allFacts.map(f => f -> symbolsOf(f))
      var changed = true
      while (changed) {
        val (in, out) = rest.partition((_, syms) => (syms & symbols).nonEmpty)
        changed = in.nonEmpty
        kept = kept ++ in.map(_._1)
        symbols = symbols ++ in.flatMap(_._2)
        rest = out
      }
      // in the order of the facts, which is that of their evaluation
      allFacts.filter(kept.contains)
    }

    /** The atom that `t` is, and whether it is negated. */
    private def atom(t: SExpr): (SExpr, Boolean) = t match {
      // `(exists xs p)` is `(not (forall xs (not p)))`
      case SList(List(Atom("exists"), vars, SList(List(Atom("not"), body)))) => (canonical(app("forall", vars, body)), true)
      case SList(List(Atom("exists"), vars, body)) => (canonical(app("forall", vars, app("not", body))), true)
      case SList(List(Atom("<="), a, b)) => (canonical(app(">", a, b)), true)
      case SList(List(Atom("<"), a, b)) => (canonical(app(">=", a, b)), true)
      case SList(List(Atom("distinct"), a, b)) => atom(app("=", a, b)) match { case (e, n) => (e, !n) }
      case SList(List(Atom("="), a, b)) =>
        val (ca, cb) = (canonical(a), canonical(b))
        (if (cb.toString < ca.toString) app("=", cb, ca) else app("=", ca, cb), false)
      case _ => (canonical(t), false)
    }

    /** Whether atom `a` may have no value: a symbol that is not a function of the program, or a
      * literal, always has one. */
    private def total(a: SExpr): Boolean = a match {
      case Atom(x) => !program.functions.contains(x)
      case SList(List(Atom("as"), Atom(x), _)) => !program.functions.contains(x)
      case _ => false
    }

    /** The values that atom `a` may take, as a Boolean or as a value. */
    private def values(a: SExpr, boolean: Boolean, current: Option[Value]): List[Value] = {
      import Value._
      val all =
        if (boolean) current match {
          case Some(Known) => List(True, False)
          case _ => List(NoValue, True, False)
        } else List(NoValue, Value.Known)
      val reflexive = a match {
        case SList(List(Atom("="), x, y)) => x == y
        case _ => false
      }
      all.filter(v => !(reflexive && v == False)).filter(v => !(total(a) && v == NoValue))
    }

    private def eval(t: SExpr, boolean: Boolean, rho: Map[SExpr, Value]): Result = t match {
      case Atom("true") => Bool(true)
      case Atom("false") => Bool(false)
      case SList(List(Atom("not"), a)) => eval(a, true, rho) match {
        case Bool(b) => Bool(!b)
        case other => other
      }
      case SList(Atom("and") :: es) => es.foldLeft[Result](Bool(true)) {
        case (Bool(true), e) => eval(e, true, rho)
        case (done, _) => done
      }
      case SList(Atom("or") :: es) => es.foldLeft[Result](Bool(false)) {
        case (Bool(false), e) => eval(e, true, rho)
        case (done, _) => done
      }
      case SList(Atom("=>") :: es) if es.nonEmpty =>
        // right associative: (=> a b c) is (=> a (=> b c))
        def imp(es: List[SExpr]): Result = es match {
          case List(last) => eval(last, true, rho)
          case e :: rest => eval(e, true, rho) match {
            case Bool(true) => imp(rest)
            case Bool(false) => Bool(true)
            case other => other
          }
          case Nil => Bool(true)
        }
        imp(es)
      case SList(List(Atom("ite"), c, a, b)) => eval(c, true, rho) match {
        case Bool(true) => eval(a, boolean, rho)
        case Bool(false) => eval(b, boolean, rho)
        case other => other
      }
      case SList(List(Atom("assume"), p, b)) => eval(p, true, rho) match {
        case Bool(true) => eval(b, boolean, rho)
        case _ => Stuck
      }
      case Binder("let", _, bindings, body) =>
        val values = bindings.map {
          case SList(List(Atom(x), v)) => x -> eval(v, false, rho)
          case other => fail(s"$other is not a binding")
        }
        if (values.exists(_._2 == Stuck)) Stuck
        else eval(subst(body, values.collect {
          case (x, Bool(b)) => x -> Atom(b.toString)
          case (x, Term(v)) => x -> v
        }.toMap), boolean, rho)
      case _ =>
        val (a, negated) = atom(t)
        rho.get(a) match {
          case None => throw Need(a, boolean)
          case Some(Value.NoValue) => Stuck
          case Some(Value.True) => Bool(!negated)
          case Some(Value.False) => Bool(negated)
          case Some(Value.Known) if boolean => throw Need(a, true)
          case Some(Value.Known) => Term(known(t, rho))
        }
    }

    /** `t` where each atom with a Boolean value, outside of binders that capture it, is that value. */
    private def known(t: SExpr, rho: Map[SExpr, Value]): SExpr = {
      val bools = rho.collect { case (a, Value.True) => a -> Atom("true"); case (a, Value.False) => a -> Atom("false") }
      def rec(t: SExpr, bound: Set[String]): SExpr = {
        val (a, negated) = atom(t)
        bools.get(a).filter(_ => (free(t) & bound).isEmpty) match {
          case Some(Atom(v)) => Atom(if (negated) (if (v == "true") "false" else "true") else v)
          case _ => t match {
            case Binder(_, names, _, _) => t match {
              case SList(List(k, decls, body)) => SList(List(k, rec(decls, bound), rec(body, bound ++ names)))
              case other => other
            }
            case SList(items) => SList(items.map(rec(_, bound)))
            case other => other
          }
        }
      }
      canonical(rec(t, Set()))
    }

    /** Whether the values of the testers in `rho` are consistent: a value is of one constructor of
      * its datatype, and a construction is of its constructor. */
    private def consistent(rho: Map[SExpr, Value]): Boolean = {
      val testers = rho.toList.collect { case (Tester(c, e), v) if program.constructors.contains(c) => (e, c, v) }
      testers.groupBy(_._1).forall { (subject, ts) =>
        val stuck = ts.exists(_._3 == Value.NoValue)
        val subjectValue = rho.get(subject)
        val noValue = ts.forall(_._3 == Value.NoValue)
        // a tester has no value exactly when its subject has none
        (!stuck || (noValue && !subjectValue.exists(_ != Value.NoValue))) &&
        (stuck || !subjectValue.contains(Value.NoValue)) && {
          val holds = ts.filter(_._3 == Value.True).map(_._2).distinct
          val fails = ts.filter(_._3 == Value.False).map(_._2).toSet
          holds.size <= 1 && holds.forall(c => !fails(c)) && {
            // the constructors of the datatype, when the testers are on a constructor of a known datatype
            val siblings = ts.flatMap(t => program.constructors.get(t._2)).headOption
            siblings.forall(cs => stuck || holds.nonEmpty || !cs.forall(fails))
          } && (program.construction(subject) match {
            case Some((c, _)) => holds.forall(_ == c) && !fails(c)
            case None => true
          })
        }
      }
    }

    /** Checks the refinement, and says how the terms differ otherwise. */
    def check(lhs: SExpr, rhs: SExpr): Option[String] = {
      val facts = relevant(lhs, rhs)
      var explored = 0
      def explore(rho: Map[SExpr, Value]): Option[String] = {
        explored += 1
        if (explored > 200000) fail(s"the logic of $lhs has too many cases")
        try {
          if (!consistent(rho)) None
          else if (facts.exists(f => eval(f, true, rho) != Bool(true))) None
          else {
            val l = eval(lhs, false, rho)
            if (l == Stuck) None
            else {
              val r = eval(rhs, false, rho)
              if (sameResult(l, r)) None
              else Some(s"where ${rho.map((a, v) => s"$a is $v").mkString(", ")}, $lhs is $l and $rhs is $r")
            }
          }
        } catch {
          case Need(a, boolean) =>
            values(a, boolean, rho.get(a)).iterator.map(v => explore(rho + (a -> v))).collectFirst { case Some(why) => why }
        }
      }
      explore(Map())
    }

    private def sameResult(l: Result, r: Result): Boolean = (l, r) match {
      case (Term(a), Term(b)) => a == b
      case _ => l == r
    }
  }

  // Steps

  /** Checks the steps of `simplifications`, the section of a certificate, where the program is the
    * one that `definitions` (the source definitions) define with the simplified bodies, and the
    * simplified expressions are `expressions`, by template. */
  def check(simplifications0: List[SExpr], definitions: List[SExpr], expressions: Int => Option[SExpr]): List[String] = {
    // The steps refine terms, which is not enough under a lambda, nor in the body of a function
    // that a lambda may call, when the program compares functions: no steps are checked then.
    val (refining, simplifications) = simplifications0 match {
      case SList(List(Atom("function-equality"), Atom(mode))) :: rest => (mode == "none", rest)
      case _ => fail("the simplifications don't say how the program compares functions")
    }
    val unexplained = List.newBuilder[String]
    // Replays the steps of the simplification of `what`, and reports those that are not checked:
    // all of them when the program compares functions, and the ones of rules that the checker
    // doesn't know, which name what a simplifier did that no rule tells.
    def replayed(what: String, original: SExpr, simplified: SExpr, steps: SExpr, program: Program): Unit = steps match {
      case SList(List(Atom("steps"))) => replay(original, simplified, steps, program)
      case _ if !refining =>
        unexplained += s"the steps of the simplification of $what are not checked: the program compares functions"
      case _ =>
        val unknown = try replay(original, simplified, steps, program)
          catch { case e: Failure => fail(s"the simplification of $what doesn't hold: ${e.getMessage}") }
        if (unknown.nonEmpty)
          unexplained += s"the simplification of $what has steps of rules that the checker doesn't know: ${unknown.mkString(", ")}"
    }
    val program = new Program(definitions)
    val simplified = program.functions.toMap
    // the program before simplifications: the original bodies, which are the definitions' bodies
    // for the functions that the section doesn't give
    val originals: Map[String, SExpr] = simplifications.collect {
      case SList(Atom("function") :: Atom(f) :: original :: _) => f -> original
    }.toMap
    for ((f, fs) <- simplifications.collect { case SList(Atom("function") :: Atom(f) :: _) => f }.groupBy(identity) if fs.size > 1)
      fail(s"the simplifications give the function $f twice")
    val original = new Program(definitions)
    for ((f, body) <- originals) original.functions.get(f) match {
      case Some(fn) => original.functions(f) = fn.copy(body = body)
      case None => fail(s"the simplifications give the function $f, which the source definitions don't define")
    }

    for (entry <- simplifications) entry match {
      case SList(List(Atom("function"), Atom(f), o, steps)) =>
        replayed(f, o, simplified(f).body, steps, original)
      case SList(List(Atom("expression"), Atom(i), o, SList(Atom("names") :: names), steps)) =>
        val index = if (i.nonEmpty && i.forall(_.isDigit)) i.toIntOption.getOrElse(fail(s"$i is not the index of a template"))
          else fail(s"$i is not the index of a template")
        val source = expressions(index).getOrElse(fail(s"template $i has no expression to simplify into"))
        // A name is a symbol that the solver made for a subterm (a lambda, or the instantiations
        // of a quantifier, which the source may negate): it is not one of the original expression
        // nor of the program, so that replacing it only puts back what the source left out. That
        // the name stands for its subterm in the clauses is what the check of the sources trusts
        // too. The source also has `(assume q true)` for a quantifier `q` that must hold.
        def symbol(x: String): Unit =
          if (free(o)(x) || original.functions.contains(x) || original.constructors.contains(x) ||
              original.selectors.contains(x) || x == "true" || x == "false" ||
              x.headOption.forall(c => c.isDigit || c == '"' || c == '#'))
            fail(s"$x is not a name that the solver made for a subterm")
        val pairs: Map[SExpr, SExpr] = names.map {
          case SList(List(n @ Atom(x), t)) => symbol(x); n -> t
          case SList(List(n @ SList(List(Atom("not"), Atom(x))), t)) => symbol(x); n -> t
          case SList(List(n @ SList(List(Atom("assume"), q, Atom("true"))), t)) if q == t =>
            mustHold(source, n); n -> t
          case other => fail(s"$other is not a name")
        }.toMap
        if (pairs.size != names.size) fail(s"the simplification of the expression of template $i names two subterms the same")
        def named(t: SExpr): SExpr = pairs.getOrElse(t, t match {
          case SList(items) => SList(items.map(named))
          case a => a
        })
        replayed(s"the expression of template $i", o, named(source), steps, original)
      case other => fail(s"$other is not a simplification")
    }
    unexplained.result()
  }

  /** Checks that `axiom` only occurs in the expression `t`, which holds, where it must hold for
    * `t` to: where evaluation reaches the occurrence, `t` only holds if the occurrence does. Then
    * `t` holds wherever `t` with `q` for each occurrence `(assume q true)` does. */
  private def mustHold(t: SExpr, axiom: SExpr): Unit = {
    def rec(t: SExpr, must: Boolean): Unit =
      if (t == axiom) { if (!must) fail(s"$axiom is where it doesn't have to hold") }
      else t match {
        case SList(Atom("and") :: es) => es.foreach(rec(_, must))
        case SList(Atom("or" | "=>") :: es) if es.nonEmpty => es.init.foreach(rec(_, false)); rec(es.last, must)
        case SList(List(Atom("ite"), c, a, b)) => rec(c, false); rec(a, must); rec(b, must)
        // an assumption that doesn't hold leaves the expression without a value
        case SList(List(Atom("assume"), p, b)) => rec(p, true); rec(b, must)
        case SList(List(Atom("let"), bindings, body)) => rec(bindings, false); rec(body, must)
        case SList(items) => items.foreach(rec(_, false))
        case _ =>
      }
    rec(t, true)
  }

  /** The rules that the checker knows (see [[rewrite]]). */
  private val rules = Set("logic", "unfold", "beta", "expand", "select", "eta", "bind", "lift", "merge", "unused",
    "prenex", "arith", "rename")

  /** Checks that `steps` rewrite `original` into `simplified`: the steps of the rules that the
    * checker knows, which hold, and the others, whose rules it returns. A step of a rule that it
    * doesn't know is what a simplifier did that no rule tells: it is taken as it is given, except
    * for what the simplifier didn't name (`unrecorded`). */
  private def replay(original: SExpr, simplified: SExpr, steps: SExpr, program: Program): List[String] = {
    val unknown = List.newBuilder[String]
    val list = steps match {
      case SList(Atom("steps") :: list) => list
      case other => fail(s"$other are not steps")
    }
    var term = original
    for (step <- list) {
      val (rule, deepest, subterm) = step match {
        case SList(List(Atom(rule), SList(pos), subterm)) =>
          (rule, pos.map { case Atom(i) if i.nonEmpty && i.length < 9 && i.forall(_.isDigit) => i.toInt; case p => fail(s"$p is not a position") }, subterm)
        case other => fail(s"$other is not a step")
      }
      val (current, rewritten) = (canonical(term), replace(term, deepest, subterm))
      val target = canonical(rewritten)
      // what a simplifier did without naming it is not a simplification that is known of at all
      if (rule == "unrecorded") fail(s"the step at ${deepest.mkString("(", " ", ")")} that gives $subterm was not recorded by a simplifier")
      else if (!rules(rule)) unknown += rule
      else if (target != current) {
        // The rule rewrites the subterm at the position, outside of which the terms are the
        // same, or one around it. The facts of these positions are the same in the two terms.
        val failures = deepest.inits.map { pos =>
          try { rewrite(rule, at(current, pos), at(target, pos), facts(current, pos), program); None }
          catch { case e: Failure => Some(e.getMessage) }
        }
        val reasons = failures.takeWhile(_.nonEmpty).flatten.toList
        if (reasons.size == deepest.size + 1) fail(s"no $rule step at ${deepest.mkString("(", " ", ")")} gives $subterm: ${reasons.head}")
      }
      term = rewritten
    }
    val current = canonical(term)
    if (!alpha(current, simplified)) fail(s"the steps give $current, and not $simplified")
    unknown.result().distinct
  }

  /** `bindings` around `body`, each in a `let` of its own, from the outermost on. */
  private def nest(bindings: List[(String, SExpr)], body: SExpr): SExpr =
    bindings.foldRight(body) { case ((x, v), b) => app("let", SList(List(SList(List(Atom(x), v)))), b) }

  /** Fails unless `computed`, what a rule makes of a term, is `rhs`. */
  private def same(computed: SExpr, rhs: SExpr): Unit =
    if (!alpha(computed, rhs)) fail(s"the step gives $computed, and not $rhs")

  /** The subterms of `t` that are evaluated whenever `t` has a value: `t`, and those of the
    * operands that are always evaluated (all those of an application, of a negation or of an
    * equality, the first one of the other connectives, and the values of a `let`). */
  private def strict(t: SExpr): List[SExpr] = t :: (t match {
    case SList(Atom("not" | "=" | "distinct") :: es) => es.flatMap(strict)
    case SList(Atom("and" | "or" | "=>" | "ite" | "assume") :: e :: _) => strict(e)
    case Binder("let", _, bindings, _) => bindings.collect { case SList(List(_, v)) => v }.flatMap(strict)
    case SList(Atom(k) :: _) if keywords(k) => Nil
    case SList(_ :: es) => es.flatMap(strict)
    case _ => Nil
  })

  /** Whether the operand `i` of `parent` is evaluated whenever `parent` is: the first operand of a
    * connective, and any operand of an application. */
  private def evaluated(parent: SExpr, i: Int): Boolean = parent match {
    case SList(Atom("not" | "and" | "or" | "=>" | "ite" | "assume") :: _) => i == 1
    case SList(Atom("=" | "distinct") :: _) => i >= 1
    case SList(Atom(k) :: _) if keywords(k) => false
    case SList(_ :: _) => i >= 1
    case _ => false
  }

  /** A term over `+`, `-` and `*` as a polynomial: the coefficient of each product of the
    * subterms that are not such terms nor numerals. */
  private def polynomial(t: SExpr): Map[List[String], BigInt] = {
    type Poly = Map[List[String], BigInt]
    def plus(a: Poly, b: Poly): Poly = (a.keySet ++ b.keySet).map(k => k -> (a.getOrElse(k, BigInt(0)) + b.getOrElse(k, BigInt(0)))).toMap.filter(_._2 != 0)
    def times(a: Poly, b: Poly): Poly = (for ((ka, ca) <- a.toList; (kb, cb) <- b.toList) yield (ka ++ kb).sorted -> ca * cb)
      .groupMapReduce(_._1)(_._2)(_ + _).filter(_._2 != 0)
    def neg(a: Poly): Poly = a.view.mapValues(-_).toMap
    t match {
      case Atom(n) if n.nonEmpty && n.forall(_.isDigit) => if (BigInt(n) == 0) Map() else Map(Nil -> BigInt(n))
      case SList(Atom("+") :: es) if es.nonEmpty => es.map(polynomial).reduce(plus)
      case SList(Atom("*") :: es) if es.nonEmpty => es.map(polynomial).reduce(times)
      case SList(List(Atom("-"), e)) => neg(polynomial(e))
      case SList(Atom("-") :: e :: es) if es.nonEmpty => es.map(polynomial).foldLeft(polynomial(e))((a, b) => plus(a, neg(b)))
      case other => Map(List(canonical(other).toString) -> BigInt(1))
    }
  }

  /** The literal that `t` is, if it is one whose text is its value. */
  private def literal(t: SExpr): Option[String] = t match {
    case Atom(a) if a == "true" || a == "false" || a.startsWith("\"") || a.startsWith("#x") || a.startsWith("#b") => Some(a)
    case SList(Atom("!") :: (l: Atom) :: annotations) if annotations.forall(_.isInstanceOf[Atom]) => literal(l).map(_ + annotations.mkString(" ", " ", ""))
    case _ => None
  }

  /** Checks that the rule `rule` rewrites `lhs` into `rhs` under `facts`, and fails otherwise. */
  private def rewrite(rule: String, lhs: SExpr, rhs: SExpr, facts: Facts, program: Program): Unit = rule match {
    case "logic" =>
      new Logic(program, facts.conditions).check(lhs, rhs).foreach(why => fail(s"$lhs is not $rhs by logic: $why"))

    case "rename" => same(lhs, rhs)

    case "unfold" => lhs match {
      case Applied(fn, args) if program.functions.contains(fn) =>
        val Function(params, tparams, body) = program.functions(fn)
        val callArgs = lhs match {
          case Atom(_) | SList(Atom("as") :: _) => Nil
          case _ => args
        }
        val sorts = sortArguments(lhs)
        if (callArgs.size != params.size) fail(s"$lhs doesn't call $fn on ${params.size} arguments")
        if (tparams.size != sorts.size) fail(s"$lhs doesn't instantiate the ${tparams.size} sorts of $fn")
        for ((a, i) <- callArgs.zipWithIndex; p <- params.take(i) if free(a)(p))
          fail(s"the argument $a of $lhs mentions the parameter $p of $fn")
        same(nest(params.zip(callArgs), subst(body, tparams.zip(sorts).toMap)), rhs)
      case _ => fail(s"$lhs is not a call of a function of the program")
    }

    case "beta" => lhs match {
      case Applied("@", SList(List(Atom("lambda"), SList(params), body)) :: args) if params.size == args.size =>
        val names = params.map { case SList(Atom(x) :: _) => x; case p => fail(s"$p is not a parameter") }
        for ((a, i) <- args.zipWithIndex; p <- names.take(i) if free(a)(p)) fail(s"the argument $a of $lhs mentions $p")
        same(nest(names.zip(args), body), rhs)
      case _ => fail(s"$lhs is not the application of a lambda")
    }

    case "expand" => lhs match {
      case Atom(x) if facts.bindings.contains(x) => same(facts.bindings(x), rhs)
      case _ => fail(s"$lhs is not a variable that a let binds")
    }

    case "select" => lhs match {
      case Applied(sel, List(e)) if program.selectors.contains(sel) =>
        val (cons, index) = program.selectors(sel)
        program.construction(e) match {
          case Some((`cons`, fields)) if index < fields.size => same(fields(index), rhs)
          case _ => fail(s"$lhs doesn't select a field of a construction of $cons")
        }
      case TupleSelect(index, Applied("tuple", elements)) if index < elements.size => same(elements(index), rhs)
      case _ => fail(s"$lhs is not a selector of a construction")
    }

    case "bind" => rhs match {
      case Binder("let", List(x), List(SList(List(_, value))), body) =>
        if (free(body)(x)) fail(s"$body mentions $x")
        same(lhs, body)
        if (!strict(lhs).exists(alpha(_, value))) fail(s"$value is not evaluated whenever $lhs has a value")
      case _ => fail(s"$rhs doesn't bind a variable")
    }

    case "lift" => (lhs, rhs) match {
      case (SList(items), Binder("let", names, bindings, _)) =>
        val lifted = items.indices.filter(i => evaluated(lhs, i)).collect { i => items(i) match {
          case Binder("let", ns, bs, body) if alpha(SList(bs), SList(bindings)) &&
              items.patch(i, Nil, 1).forall(o => ns.forall(x => !free(o)(x))) =>
            app("let", SList(bs), SList(items.updated(i, body)))
        }}
        if (!lifted.exists(alpha(_, rhs))) fail(s"$rhs is not $lhs with a let lifted from an operand that is always evaluated")
      case (SList(items), SList(List(Atom("assume"), pred, _))) =>
        val lifted = items.indices.filter(i => evaluated(lhs, i)).collect { i => items(i) match {
          case SList(List(Atom("assume"), p, body)) => app("assume", p, SList(items.updated(i, body)))
        }}
        if (!lifted.exists(alpha(_, rhs))) fail(s"$rhs is not $lhs with an assumption lifted from an operand that is always evaluated")
      case _ => fail(s"$rhs is not a let nor an assumption that is lifted from $lhs")
    }

    case "merge" => lhs match {
      case SList(List(Atom(q @ ("forall" | "exists")), SList(vs1), SList(List(Atom(q2), SList(vs2), body)))) if q == q2 =>
        val names1 = vs1.collect { case SList(Atom(x) :: _) => x }
        val names2 = vs2.collect { case SList(Atom(x) :: _) => x }
        if ((names1 ++ names2).distinct.size != vs1.size + vs2.size) fail(s"the quantifiers of $lhs bind a variable twice")
        if (vs2.exists { case SList(_ :: sorts) => sorts.exists(s => (free(s) & names1.toSet).nonEmpty); case _ => true })
          fail(s"the sorts of the inner quantifier of $lhs depend on the outer one")
        same(SList(List(Atom(q), SList(vs1 ++ vs2), body)), rhs)
      case _ => fail(s"$lhs is not a quantifier over a quantifier")
    }

    case "unused" => lhs match {
      case Binder("forall", _, _, body @ Atom("true")) if rhs == body =>
      case Binder("exists", _, _, body @ Atom("false")) if rhs == body =>
      case Binder(q @ ("forall" | "exists"), names, decls, body) =>
        // the variables that are dropped are the first ones that give the quantifier of `rhs`
        val unused = names.zip(decls).filter((x, _) => !free(body)(x))
        val candidates = unused.toSet.subsets().toList.sortBy(_.size).filter(_.nonEmpty)
        val found = candidates.find { dropped =>
          val kept = names.zip(decls).filterNot(dropped).map(_._2)
          alpha(if (kept.isEmpty) body else SList(List(Atom(q), SList(kept), body)), rhs)
        }
        found match {
          case Some(dropped) =>
            for (case (_, SList(List(_, sort))) <- dropped if !program.inhabited(sort))
              fail(s"the checker can't tell that the sort $sort of $lhs has values")
            if (dropped.exists { case (_, SList(List(_, _))) => false; case _ => true }) fail(s"$lhs binds what is not a variable")
          case None => fail(s"$rhs is not $lhs without variables that its body doesn't mention")
        }
      case _ => fail(s"$lhs is not a quantifier")
    }

    case "prenex" => lhs match {
      case Binder("forall", names, decls, SList(Atom(op @ ("and" | "or" | "=>")) :: operands)) =>
        // The quantifiers that come out are operands that may: not the premise of an implication,
        // where the quantifier would be an existential one, and over sorts that have values. The
        // others stay, and so may any: the step is one for some of those that may come out.
        val candidates = operands.zipWithIndex.collect {
          case (Binder("forall", _, ds, _), i) if !(op == "=>" && i < operands.size - 1) && ds.forall {
            case SList(List(_, sort)) => program.inhabited(sort)
            case _ => false
          } => i
        }
        if (candidates.size > 12) fail(s"$lhs has too many quantifiers to lift")
        def lift(chosen: Set[Int]): SExpr = {
          // each quantifier comes out under names of its own
          var fresh = 0
          val lifted = operands.zipWithIndex.map {
            case (Binder("forall", ns, ds, body), i) if chosen(i) =>
              val renamed = ns.map { x => fresh += 1; x -> s"%p$fresh" }
              val sorts = ds.map { case SList(List(_, sort)) => sort; case d => fail(s"$d is not a variable") }
              (renamed.map(_._2).zip(sorts).map((x, sort) => SList(List(Atom(x), sort))), subst(body, renamed.map((x, y) => x -> Atom(y)).toMap))
            case (e, _) => (Nil, e)
          }
          SList(List(Atom("forall"), SList(decls ++ lifted.flatMap(_._1)), SList(Atom(op) :: lifted.map(_._2))))
        }
        if (!candidates.toSet.subsets().filter(_.nonEmpty).exists(chosen => alpha(lift(chosen), rhs)))
          fail(s"$rhs is not $lhs with quantifiers lifted from where they may be: not from the premise of an implication, nor over sorts that the checker can't tell have values")
      case _ => fail(s"$lhs is not a quantifier over a connective")
    }

    case "arith" => (lhs, rhs) match {
      case (SList(List(Atom("="), a, b)), Atom("true")) =>
        if (!alpha(a, b) && polynomial(a) != polynomial(b)) fail(s"$a and $b are not the same")
      case (SList(List(Atom("="), a, b)), Atom("false")) =>
        val distinctLiterals = literal(a).exists(x => literal(b).exists(_ != x))
        val difference = polynomial(SList(List(Atom("-"), a, b)))
        if (!distinctLiterals && !(difference.keySet == Set(Nil))) fail(s"$a and $b are not literals that differ")
      case _ =>
        // the result has the value of the term, and has one whenever it does
        val (l, r) = (polynomial(lhs), polynomial(rhs))
        if (l != r) fail(s"$lhs and $rhs are not the same polynomial")
        val evaluated = strict(lhs).map(canonical(_).toString).toSet
        for (k <- r.keys; x <- k if !evaluated(x)) fail(s"$x of $rhs is not evaluated whenever $lhs has a value")
    }

    case "eta" => lhs match {
      case Applied(cons, fields) if program.constructors.contains(cons) && fields.nonEmpty =>
        val selectors = program.selectors.collect { case (sel, (`cons`, i)) => i -> sel }
        for ((field, i) <- fields.zipWithIndex) field match {
          case Applied(sel, List(e)) if selectors.get(i).contains(sel) && alpha(e, rhs) =>
          case _ => fail(s"$field is not the field $i of $rhs")
        }
        // the term is of the constructor
        if (program.constructors(cons).size > 1)
          new Logic(program, facts.conditions).check(app(s"is-$cons", rhs), Atom("true"))
            .foreach(why => fail(s"$rhs may not be of the constructor $cons: $why"))
      case _ => fail(s"$lhs is not a construction")
    }

    case _ => fail(s"$rule is not a rule")
  }
}
