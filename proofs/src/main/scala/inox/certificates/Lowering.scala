/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package certificates

/** Lowers the sources of the templates of a certificate, which Inox's SMT-LIB 3 printer prints,
  * to the syntax of the solver's session, in which the clauses of the templates are, so that
  * [[Sources]] can relate them (see `certificates/README.md`).
  *
  * The lowering only reads the certificate's symbol tables:
  *  - the `source-definitions`: the datatypes and the definitions of the functions that the
  *    sources name, in SMT-LIB 3, whose bodies are the sources of the templates of those
  *    functions (see [[Sources.Definition]]);
  *  - the `source-symbols`: the Inox definition that each symbol of the sources stands for, and
  *    the SMT-LIB 3 sort of each variable;
  *  - the `solver-symbols`: the Inox definition that each symbol of the session stands for,
  *    and for the symbols that a type determines (sorts, constructors, selectors, testers,
  *    dynamic applications and instances of generic functions), the SMT-LIB 3 sort of that type
  *    (for an instance, the list of the sorts of its type arguments).
  *
  * The printer writes each symbol of a source whose session symbol depends on a type under the
  * key that the `solver-symbols` record for it, `(as x k)`, so that the lowering infers no sort:
  * it picks the session symbol of the same Inox definition and of the same key. A symbol without
  * a key is that of the one session symbol of its definition. Sorts are compared without their
  * refinements (the `:var` and `:restrict` attributes), which the session's sorts don't have;
  * they keep `:unsigned`. The lowering relies on distinct types printing as distinct sorts, which
  * the solver checks as it prints them. The bodies of the `source-definitions` are generic: their
  * keys mention the type parameters of the definition, which the type arguments of a call, the
  * key of its head, replace.
  *
  * Each construct lowers as follows, where `t'` is the lowering of `t` and `S'` that of the sort
  * `S`:
  *  - literals, variables, `let`, `assume`, `ite`, and the Boolean, arithmetic, bit-vector and
  *    array operations are the same; `(! t :unsigned)`, `(! t :signed)` and `(! t :char)` are `t'`;
  *  - `(error S "message")` is `(assume false (error S'))`: an assumption that never holds, of a
  *    value that stands for no other;
  *  - `C`, `(C ts)`, `(s t)` and `((_ is C) t)` are the session's constructor, selector and
  *    tester of a datatype without type parameters, and `(as C S)`, `((as C S) ts)`,
  *    `((as s S) t)` and `((as (_ is C) S) t)` those of the datatype sort `S`; `((as tuple S) ts)`
  *    and `((as (_ tuple.select i) S) t)` are the constructor and the selector of the session's
  *    tuple sort of `S`;
  *  - `f` and `(f ts)` are the session's function `f`, and `(as f (S ..))` and
  *    `((as f (S ..)) ts)` its instance at the type arguments `S ..`, for a function of the
  *    program and for an uninterpreted function that the source definitions declare;
  *  - `((as @ S) f ts)` is `(f ts')` when the session declares `f` as a function of its own (a
  *    predicate), and `(d f' ts')` for the session's dynamic application `d` of the sort `S`;
  *  - `(forall ((x S) ..) t)` is `(forall ((x S') ..) t')`, and `(exists ((x S) ..) t)` is
  *    `(not (forall ((x S') ..) u'))` where `u` is `(not t)`, or `v` when `t` is `(not v)`;
  *  - `(as emptyset S)` is `(as set.empty (Set S'))`, `(insert s t)` is `(set.insert t' s')`, and
  *    the set `(insert (as emptyset S) t1 .. tn)` is `(set.insert t2' .. tn' (set.singleton t1'))`
  *    when `t1` has no variable, and `(set.insert t1' .. tn' (as set.empty (Set S')))` otherwise,
  *    as the session builds them. With one element `t1` and no variable, this is also how the
  *    printer prints adding `t1` to the empty set, which is the same set; `member`, `union`,
  *    `intersection`, `setminus` and `subset` are `set.member`, `set.union`, `set.inter`,
  *    `set.minus` and `set.subset`;
  *  - the markers of the sources, `((as m S) ts)` and `(as m S)` for the uninterpreted functions
  *    that the source declarations don't declare, keep their head, and their arguments lower;
  *  - the sorts lower to themselves for `Bool`, `Int`, `Real`, `String` and the bit vectors,
  *    `(_ BitVec 16)` for `Char`, `Int` for the function sorts `(-> ..)`, elementwise for `Array`
  *    and `Set`, and to the session's sort of the same SMT-LIB 3 sort otherwise.
  *
  * It refuses a symbol of which the session has no symbol, outside of an assumption, which it
  * leaves out then, or one for which it has several, and
  * the constructs that the corpus doesn't use and that it doesn't lower: lambdas, `tuple.unit`,
  * bags, strings operations and floating points. */
object Lowering {
  import Checker._

  sealed class Refused(val why: String) extends Exception(why)
  /** The refusal of a symbol of which the session has no symbol. */
  private final class Missing(why: String) extends Refused(why)
  private def refuse(why: String): Nothing = throw new Refused(why)

  private val Bool = Atom("Bool")
  private val IntSort = Atom("Int")
  private def app(op: String, args: SExpr*): SExpr = SList(Atom(op) :: args.toList)

  private def quoted(e: SExpr): Boolean = e match {
    case Atom(t) => t.startsWith("\"")
    case _ => false
  }

  /** A symbol of a table: its name, its kind, the descriptions of the Inox definition that it
    * stands for, and the SMT-LIB 3 sort that it records, if any. */
  final case class Entry(name: Atom, kind: String, descriptions: List[String], sort: Option[SExpr])

  /** The entry of the line `(name kind "description".. [sort])` of a symbol table. */
  def entry(line: SExpr): Entry = line match {
    case SList((name: Atom) :: Atom(kind) :: rest) =>
      val (descriptions, sort) = rest.span(quoted)
      sort match {
        case Nil => Entry(name, kind, descriptions.map(_.toString), None)
        case List(s) => Entry(name, kind, descriptions.map(_.toString), Some(erase(s)))
        case _ => fail(s"$line doesn't describe a symbol")
      }
    case other => fail(s"$other doesn't describe a symbol")
  }

  /** The sort `s` without its refinements: the attributes `:var` and `:restrict` of its
    * annotations `(! ..)`, which the session's sorts don't have. */
  def erase(s: SExpr): SExpr = s match {
    case SList(Atom("!") :: base :: attributes) =>
      def kept(as: List[SExpr]): List[SExpr] = as match {
        case Atom(":var" | ":restrict") :: _ :: rest => kept(rest)
        case a :: rest => a :: kept(rest)
        case Nil => Nil
      }
      kept(attributes) match {
        case Nil => erase(base)
        case as => SList(Atom("!") :: erase(base) :: as)
      }
    case SList(items) => SList(items.map(erase))
    case atom => atom
  }

  private def bitVector(n: Int): SExpr = SList(List(Atom("_"), Atom("BitVec"), Atom(n.toString)))

  /** The size of the bit vector sort `s`, and whether it is unsigned. */
  private def bitVectorOf(s: SExpr): Option[(Int, Boolean)] = s match {
    case SList(List(Atom("_"), Atom("BitVec"), Atom(n))) if n.forall(_.isDigit) => Some((n.toInt, false))
    case SList(List(Atom("!"), b, Atom(":unsigned"))) => bitVectorOf(b).collect { case (n, false) => (n, true) }
    case _ => None
  }

  /** The definition of a function of the sources, of type parameters `params`. */
  private final case class Definition(params: List[Atom], arguments: List[Atom], body: SExpr)

  /** The symbol `x` under the key `k` that picks its symbol of the session, `(as x k)`, and the
    * arguments that it is applied to. */
  private object Keyed {
    def unapply(e: SExpr): Option[(SExpr, SExpr, List[SExpr])] = e match {
      case SList(List(Atom("as"), x, k)) => Some((x, k, Nil))
      case SList(SList(List(Atom("as"), x, k)) :: args) => Some((x, k, args))
      case _ => None
    }
  }

  /** The tables of a certificate: its `script` (with that of its templates), its session's
    * `solverSymbols`, and its `declarations` and `sourceSymbols`. */
  final class Tables(script: Seq[SExpr], solverSymbols: Seq[SExpr], declarations: Seq[SExpr], sourceSymbols: Seq[SExpr]) {
    private val session: Seq[Entry] = solverSymbols.map(entry)
    private val sessionNames: Map[Atom, Entry] = session.map(e => e.name -> e).toMap
    private val sources: Map[Atom, Entry] = sourceSymbols.map(entry).map(e => e.name -> e).toMap

    /** The definitions of the sources' functions: `define-fun` and `define-fun-rec` of
      * `f ((x S) ..) R body` or of `(par (A ..) (f ((x S) ..) R body))`, and `define-funs-rec` of
      * the lists of the signatures, each `(f ((x S) ..) R)` or `(par (A ..) (f ((x S) ..) R))`,
      * and of the bodies. */
    private val definitions: Map[Atom, Definition] = {
      def parameters(ps: List[SExpr]): List[(Atom, SExpr)] = ps.map {
        case SList(List(x: Atom, s)) => x -> s
        case other => fail(s"$other is not a parameter")
      }
      def sortParameters(ps: List[SExpr]): List[Atom] = ps.map { case p: Atom => p; case p => fail(s"$p is not a sort parameter") }
      def signature(dec: SExpr): (Atom, List[Atom], List[(Atom, SExpr)], SExpr) = dec match {
        case SList(List(Atom("par"), SList(ps), SList(List(f: Atom, SList(xs), range)))) => (f, sortParameters(ps), parameters(xs), range)
        case SList(List(f: Atom, SList(xs), range)) => (f, Nil, parameters(xs), range)
        case other => fail(s"$other is not the signature of a function")
      }
      declarations.flatMap {
        case SList(List(Atom("define-fun" | "define-fun-rec"), f: Atom, SList(xs), range, body)) =>
          List(f -> Definition(Nil, parameters(xs).map(_._1), body))
        case SList(List(Atom("define-fun" | "define-fun-rec"), SList(List(Atom("par"), SList(ps), SList(List(f: Atom, SList(xs), range, body)))))) =>
          List(f -> Definition(sortParameters(ps), parameters(xs).map(_._1), body))
        case SList(List(Atom("define-funs-rec"), SList(decs), SList(bodies))) if decs.size == bodies.size =>
          (decs zip bodies).map { case (dec, body) =>
            val (f, ps, xs, range) = signature(dec)
            f -> Definition(ps, xs.map(_._1), body)
          }
        case d @ SList(Atom("define-fun" | "define-fun-rec" | "define-funs-rec") :: _) => fail(s"$d is not a definition")
        case _ => Nil
      }.toMap
    }

    /** The uninterpreted functions that the sources declare, which the markers are not. */
    private val declared: Set[Atom] = declarations.collect {
      case SList(List(Atom("declare-fun"), f: Atom, _, _)) => f
      case SList(List(Atom("declare-fun"), SList(List(Atom("par"), _, SList((f: Atom) :: _))))) => f
    }.toSet

    /** The session's functions of their own, which an application applies directly. */
    private val predicates: Set[Atom] =
      script.collect { case SList(List(Atom("declare-fun"), f: Atom, SList(_ :: _), _)) => f }.toSet

    private def source(a: Atom, kind: String): Option[Entry] = sources.get(a).filter(_.kind == kind)
    /** A marker: an uninterpreted function of the sources that the declarations don't declare. */
    private def isMarker(a: Atom): Boolean = source(a, "uninterpreted").nonEmpty && !declared(a)

    /** The one session symbol that `p` holds of. */
    private def unique(what: => String, p: Entry => Boolean): Atom = session.filter(p) match {
      case Seq(e) => e.name
      case Seq() => throw new Missing(s"the session has no $what")
      case es => refuse(s"the session has several ${what}s: ${es.map(_.name).mkString(", ")}")
    }

    /** The session's sort of the sort `s` (see [[Lowering]]). */
    def lowerSort(s: SExpr): SExpr = erase(s) match {
      case b @ Atom("Bool" | "Int" | "Real" | "String") => b
      case Atom("Char") => bitVector(16)
      case SList(Atom("->") :: _) => IntSort
      case SList(List(Atom("Array"), k, v)) => app("Array", lowerSort(k), lowerSort(v))
      case SList(List(Atom("Set"), e)) => app("Set", lowerSort(e))
      case b if bitVectorOf(b).nonEmpty => bitVector(bitVectorOf(b).get._1)
      case other => unique(s"sort $other", e => e.kind == "sort" && e.sort.contains(other))
    }

    private def instantiate(s: SExpr, subst: Map[Atom, SExpr]): SExpr = s match {
      case a: Atom => subst.getOrElse(a, a)
      case SList(items) => SList(items.map(instantiate(_, subst)))
    }

    /** The operations that lower to themselves, applied to their lowered arguments. */
    private val same = Set("not", "and", "or", "=>", "xor", "=", "distinct", "<", "<=", ">", ">=",
      "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
      "+", "-", "*", "div", "mod", "abs", "bvadd", "bvsub", "bvmul", "bvudiv", "bvsdiv",
      "bvurem", "bvsrem", "bvsmod", "bvneg", "bvnot", "bvand", "bvor", "bvxor", "bvshl", "bvashr", "bvlshr",
      "store", "/", "bv2nat", "ite", "select")
    private val setOperations = Map("member" -> "set.member", "subset" -> "set.subset", "union" -> "set.union",
      "intersection" -> "set.inter", "setminus" -> "set.minus")

    private def bindings(bs: List[SExpr]): List[(Atom, SExpr)] = bs.map {
      case SList(List(x: Atom, s)) => x -> s
      case other => refuse(s"$other is not a binding")
    }

    private def isLiteral(t: String): Boolean =
      t == "true" || t == "false" || t.nonEmpty && t.forall(_.isDigit) || t.matches("[0-9]+\\.[0-9]+") ||
      t.matches("#b[01]+") || t.matches("#x[0-9a-fA-F]+") || t.startsWith("\"")

    private def isVariable(a: Atom, bound: Set[Atom]): Boolean = bound(a) || source(a, "variable").nonEmpty

    /** Whether `e` has no variable, for a set's first element. */
    private def ground(e: SExpr, bound: Set[Atom]): Boolean = e match {
      case a: Atom => !isVariable(a, bound)
      case SList(items) => items.forall(ground(_, bound))
    }

    /** The session's symbol of the symbol `head` of the sources: the one of the same Inox
      * definition, and of the sort `key` when the source gives one. */
    private def symbol(head: SExpr, key: Option[SExpr]): Atom = {
      def pick(what: String, p: Entry => Boolean): Atom =
        unique(what + key.fold("")(k => s" at $k"), e => p(e) && key.forall(e.sort.contains))
      def index(i: String) = "\"" + i + "\""
      head match {
        case Atom("tuple") => pick("tuple constructor", e => e.kind == "constructor" && e.descriptions.size == 1)
        case SList(List(Atom("_"), Atom("tuple.select"), Atom(i))) =>
          pick(s"tuple selector $i", e => e.kind == "selector" && e.descriptions.size == 2 && e.descriptions(1) == index(i))
        case SList(List(Atom("_"), Atom("is"), c: Atom)) =>
          val id = source(c, "constructor").getOrElse(refuse(s"$c is not a constructor of the sources")).descriptions.head
          pick(s"tester of $id", e => e.kind == "tester" && e.descriptions.size == 2 && e.descriptions.head == id)
        case a: Atom => sources.get(a) match {
          case Some(Entry(_, "constructor", id :: _, _)) =>
            pick(s"constructor $id", e => e.kind == "constructor" && e.descriptions.size == 2 && e.descriptions.head == id)
          case Some(Entry(_, "selector", List(id, _, i), _)) =>
            pick(s"selector $i of $id", e => e.kind == "selector" && e.descriptions.size == 3 && e.descriptions.head == id && e.descriptions(2) == i)
          case Some(Entry(_, "function", id :: _, _)) =>
            pick(s"instance of $id", e => e.kind == "function" && e.descriptions.headOption.contains(id))
          case Some(Entry(_, "uninterpreted", id, _)) if !isMarker(a) =>
            unique(s"uninterpreted function ${id.mkString(" ")}", e => e.kind == "uninterpreted" && e.descriptions == id)
          case _ => refuse(s"$a is no symbol of the sources")
        }
        case other => refuse(s"$other is no symbol of the sources")
      }
    }

    private def applied(head: SExpr, args: List[SExpr]): SExpr = if (args.isEmpty) head else SList(head :: args)

    /** The lowering of the term `e`, whose bound variables are `bound`. */
    def lower(e: SExpr, bound: Set[Atom] = Set.empty): SExpr = {
      def rec(t: SExpr) = lower(t, bound)
      e match {
        case Atom(t) if isLiteral(t) => e
        case a: Atom if bound(a) => a
        case a: Atom if source(a, "variable").nonEmpty =>
          for (s <- sessionNames.get(a) if s.kind != "variable" || s.descriptions != source(a, "variable").get.descriptions)
            refuse(s"the variable $a of the sources is ${s.kind} ${s.descriptions.mkString(" ")} in the session")
          a
        case a: Atom => symbol(a, None)

        case SList(List(Atom("!"), t, Atom(":unsigned" | ":signed" | ":char"))) => rec(t)

        case Keyed(Atom("emptyset"), s, Nil) => app("as", Atom("set.empty"), app("Set", lowerSort(s)))
        case Keyed(Atom("const"), s, List(d)) => SList(List(app("as", Atom("const"), lowerSort(s)), rec(d)))
        case Keyed(m: Atom, k, args) if isMarker(m) => applied(app("as", m, k), args.map(rec))
        case Keyed(Atom("@"), _, (f: Atom) :: args) if predicates(f) && isVariable(f, bound) => SList(f :: args.map(rec))
        case Keyed(Atom("@"), k, f :: args) =>
          val sort = erase(k)
          SList(unique(s"application of sort $sort", s => s.kind == "application" && s.sort.contains(sort)) :: (f :: args).map(rec))
        case Keyed(head, k, args) => applied(symbol(head, Some(erase(k))), args.map(rec))

        case SList(List(head @ SList(Atom("_") :: Atom("int2bv" | "zero_extend" | "sign_extend" | "extract") :: _), t)) =>
          SList(List(head, rec(t)))

        case SList(List(Atom("let"), SList(bs), body)) =>
          val bindings = this.bindings(bs)
          SList(List(Atom("let"), SList(bindings.map { case (x, v) => SList(List(x, rec(v))) }), lower(body, bound ++ bindings.map(_._1))))
        case SList(List(Atom(q @ ("forall" | "exists")), SList(bs), body)) =>
          val bindings = this.bindings(bs)
          val lowered = SList(bindings.map { case (x, s) => SList(List(x, lowerSort(s))) })
          val inner = bound ++ bindings.map(_._1)
          if (q == "forall") SList(List(Atom("forall"), lowered, lower(body, inner)))
          else app("not", SList(List(Atom("forall"), lowered, lower(body match {
            case SList(List(Atom("not"), b)) => b
            case b => app("not", b)
          }, inner))))

        case SList(List(Atom("insert"), SList(List(Atom("as"), Atom("emptyset"), s)), first, rest*)) =>
          if (ground(first, bound)) {
            val singleton = app("set.singleton", rec(first))
            if (rest.isEmpty) singleton else SList(Atom("set.insert") :: rest.map(rec).toList ::: List(singleton))
          } else SList(Atom("set.insert") :: (first :: rest.toList).map(rec) ::: List(rec(SList(List(Atom("as"), Atom("emptyset"), s)))))
        case SList(List(Atom("insert"), s, t)) => app("set.insert", rec(t), rec(s))
        case SList(Atom(op) :: args) if setOperations.contains(op) => SList(Atom(setOperations(op)) :: args.map(rec))

        // no clause of the session states an assumption of whose symbols it has none, and the
        // expression without the assumption has the value of the one with it, wherever it has one
        case SList(List(Atom("assume"), p, body)) =>
          (try Some(rec(p)) catch { case _: Missing => None }) match {
            case Some(lowered) => app("assume", lowered, rec(body))
            case None => rec(body)
          }
        // an error is an assumption that never holds, of a value that stands for no other
        case SList(List(Atom("error"), s, _)) => app("assume", Atom("false"), app("error", lowerSort(s)))
        case SList(Atom(op) :: args) if same(op) => SList(Atom(op) :: args.map(rec))

        case SList(head :: args) => applied(symbol(head, None), args.map(rec))
        case other => refuse(s"$other can't be lowered")
      }
    }

    /** The lowering of the source `s`, and of its `where`: a symbol of the template that the left
      * of a pair names is kept. */
    def lower(s: Sources.Source): Sources.Source = {
      def pairs = s.where.map {
        case (l: Atom, r) => l -> lower(r)
        case (l, r) => lower(l) -> lower(r)
      }
      s match {
        case Sources.Function(call, body, _) => Sources.Function(lower(call), lower(body), pairs)
        case Sources.Expression(expr, _) => Sources.Expression(lower(expr), pairs)
        case Sources.Definition(call, names, _) => Sources.Function(lower(call), lower(defined(call, names)), pairs)
      }
    }

    /** The source of the template of the call `call` of a defined function: the body of the
      * function's definition at the sorts of its type arguments, which are the key of the call,
      * and at its arguments, where each outermost subterm that is the right of a pair of `names`
      * is the left of the pair. Sorts are compared without their refinements. It refuses a name
      * that names no subterm of the body. */
    private def defined(call: SExpr, names: List[(SExpr, SExpr)]): SExpr = {
      val (f, sorts, args) = call match {
        case Keyed(f: Atom, SList(sorts), args) => (f, sorts, args)
        case SList((f: Atom) :: args) => (f, Nil, args)
        case f: Atom => (f, Nil, Nil)
        case other => refuse(s"$other is not the call of a function")
      }
      val definition = definitions.getOrElse(f, refuse(s"the function $f has no definition"))
      if (definition.params.size != sorts.size) refuse(s"$call has ${sorts.size} type arguments, not ${definition.params.size}")
      if (definition.arguments.size != args.size) refuse(s"$call has ${args.size} arguments, not ${definition.arguments.size}")
      val body = instance(erase(instantiate(definition.body, (definition.params zip sorts).toMap ++ (definition.arguments zip args))))
      val named = names.map { case (name, original) => erase(original) -> name }
      if (named.map(_._1).distinct.size != named.size) refuse(s"the names of $call name a subterm twice")
      val table = named.toMap
      var used = Set.empty[SExpr]
      def rec(t: SExpr): SExpr = table.get(t) match {
        case Some(name) => used += t; name
        case None => t match {
          case SList(items) => SList(items.map(rec))
          case atom => atom
        }
      }
      val source = rec(body)
      for ((original, _) <- named if !used(original)) refuse(s"the body of $f has no subterm $original")
      source
    }

    /** The instantiated body `body` of a definition, where each uninterpreted function is the
      * one of its type arguments: each instantiation of an uninterpreted function is a symbol of
      * its own in the sources, whose entry ends with its type arguments, which are its key. */
    private def instance(body: SExpr): SExpr = body match {
      case SList(List(Atom("as"), u: Atom, k)) if source(u, "uninterpreted").exists(e => e.sort.nonEmpty && !e.sort.contains(k)) =>
        val id = source(u, "uninterpreted").get.descriptions
        sources.values.filter(o => o.kind == "uninterpreted" && o.descriptions == id && o.sort.contains(k)).toList match {
          case List(o) => app("as", o.name, k)
          case Nil => refuse(s"the sources have no instance of the uninterpreted function $u at $k")
          case _ => refuse(s"the sources have several instances of the uninterpreted function $u at $k")
        }
      case SList(items) => SList(items.map(instance))
      case atom => atom
    }
  }
}
