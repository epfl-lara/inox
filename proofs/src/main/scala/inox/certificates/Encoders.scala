/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package certificates

import Checker.{Atom, SExpr, SList, fail}
import Lowering.{Entry, entry}

/** Checks the input of a certificate: that each of its constraints is encoded as the certificate
  * states, by the encoders that it names.
  *
  * The input and the encoded terms are terms of Inox's SMT-LIB 3 syntax, the first over the
  * symbols of the input and the second over those of the sources. An encoder rewrites the terms of
  * its theory and leaves the others as they are, so the check goes through both terms at once:
  * they have the same shape, a symbol of the input facing the symbol of the sources that stands
  * for the same identifier, except where the input has a term of an encoder's theory, which
  * faces what the encoder makes of it. The sorts that an encoded term has and the input doesn't,
  * such as the sort of the elements of a bag whose multiplicity is taken, are not checked here:
  * they are those that type the encoded term.
  *
  * Of the encoders of `solvers.theories`, the check knows `propositions`, which changes no term,
  * `bags` and `map-merge`. With `bags` (see `solvers.theories.BagEncoder`), the sort `(Bag T)` is
  * the datatype `Bag` of the encoder at `T`, and
  * {{{
  * (as bag.empty T)            is  Leaf
  * (bag.insert b e)            is  (Node 0 b (Elem e 1))
  * (bag.union a b)             is  (Node 0 a b)
  * (bag.difference a b)        is  (Node 1 a b)
  * (bag.intersection a b)      is  (Node 2 a b)
  * (bag.multiplicity e b)      is  (get b e)
  * (bag.singleton k v)         is  (ite false Leaf (Node 0 Leaf <elem>))
  * }}}
  * where `<elem>` is `(Elem k v)` when `v` is a positive literal, `Leaf` when it is another
  * literal, and `(ite (> v 0) (Elem k v) Leaf)` otherwise. A bag of several elements, which the
  * input prints as the union of its singletons, is only accepted when it is encoded as that
  * union is. With `map-merge`, `(map.merge mask m1 m2)` is the call of the encoder's `mapMerge`.
  * The symbols of an encoder are those of the sources that stand for an identifier of its name
  * that the input doesn't have, and the source definitions of the datatype `Bag` and of its
  * functions `get` and `inv` must be those of the encoder.
  *
  * Each constraint also gives the steps of the solver's simplification of the encoded term, the
  * rule of each and the term after it, which lead to the source of the template of the
  * constraint. The check reads them, and doesn't check them yet. Each function of the source
  * definitions comes with its body after the encoders, which is what the encoders make of its
  * definition in the input, and the steps of its simplification, the last of which is the body
  * of its source definition. */
object Encoders {
  private val known = Set("propositions", "bags", "map-merge")

  /** Checks the input `input` of a certificate whose sources have the definitions
    * `sourceDefinitions` and the symbols `sourceSymbols`, and gives the number of constraints
    * and functions that it checked: none when the certificate has no input. */
  def check(input: List[SExpr], sourceDefinitions: Seq[SExpr], sourceSymbols: Seq[SExpr]): Int = input match {
    case Nil => 0
    // how the solver compares functions changes nothing of what the encoders make
    case (encoders @ SList(Atom("encoders") :: _)) :: SList(List(Atom("function-equality"), _)) :: rest =>
      check(encoders :: rest, sourceDefinitions, sourceSymbols)
    case SList(Atom("encoders") :: names) :: SList(Atom("definitions") :: definitions) :: rest if rest.nonEmpty =>
      val (lines, symbols) = (rest.init, rest.last match {
        case SList(Atom("symbols") :: lines) => lines.map(entry)
        case other => fail(s"$other is not the symbols of the input")
      })
      val encoders = names.map {
        case Atom(n) if n.startsWith("\"") && n.endsWith("\"") && n.length >= 2 => n.substring(1, n.length - 1)
        case other => fail(s"$other is not the name of an encoder")
      }
      for (n <- encoders if !known(n)) fail(s"the checker doesn't check the encoder $n")
      val relation = new Relation(encoders.toSet, symbols, sourceSymbols.map(entry))
      val (inFuns, outFuns) = (functions(definitions), functions(sourceDefinitions))
      val (inData, outData) = (datatypes(definitions), datatypes(sourceDefinitions))

      // the steps of a simplification are recorded, and not yet checked: the term after the last
      def simplified(term: SExpr, steps: List[SExpr]): SExpr = steps.foldLeft(term) {
        case (_, SList(List(Atom(_), t))) => t
        case (_, other) => fail(s"$other is not a step of a simplification")
      }
      // the variables that `xs` bind face those that `ys` bind, the sorts of parameters under `bound`
      def bind(xs: List[SExpr], ys: List[SExpr], bound: Map[Atom, Atom], in: SExpr, out: SExpr): Map[Atom, Atom] =
        if (xs.size != ys.size) relation.no(in, out) else (xs zip ys).map {
          case (x: Atom, y: Atom) => x -> y
          case (SList(List(x: Atom, s)), SList(List(y: Atom, s2))) => relation.relate(s, s2, bound); x -> y
          case _ => relation.no(in, out)
        }.toMap

      val defined = scala.collection.mutable.Set[Atom]()
      for (line <- lines) line match {
        case SList(List(Atom("constraint"), in, SList(List(Atom("encoded"), out)), SList(Atom("simplified") :: steps))) =>
          relation.relate(in, out, Map.empty)
          simplified(out, steps)

        // a function of the sources: its body after the encoders is the body of its definition
        // in the input, and its simplification the body of its source definition
        case SList(List(Atom("function"), call, SList(List(Atom("encoded"), body)), SList(Atom("simplified") :: steps))) =>
          val (f, args) = call match {
            case SList(List(Atom("as"), f: Atom, _)) => (f, Nil)
            case SList(SList(List(Atom("as"), f: Atom, _)) :: args) => (f, args)
            case SList((f: Atom) :: args) => (f, args)
            case f: Atom => (f, Nil)
            case other => fail(s"$other is not the call of a function")
          }
          val (ps2, xs2, range2, body2) = outFuns.getOrElse(f, fail(s"$f is not a function of the source definitions"))
          if (xs2.map { case SList(x :: _) => x; case x => x } != args) fail(s"$call is not the call of $f on its parameters")
          if (simplified(body, steps) != body2) fail(s"the body of $f is not the simplification of its encoded body")
          for (g <- relation.inputOf(f, inFuns.keys)) {
            val (ps, xs, range, inBody) = inFuns(g)
            val tparams = bind(ps, ps2, Map.empty, g, f)
            val params = bind(xs, xs2, tparams, g, f)
            relation.relate(range, range2, tparams)
            relation.relate(inBody, body, tparams ++ params)
          }
          defined += f
        case other => fail(s"$other is not a constraint or a function of the input")
      }
      for (f <- outFuns.keys if !defined(f)) fail(s"the input doesn't say what $f is the simplification of")

      // the datatypes of the input are those of the sources
      for ((d, decl) <- inData; d2 <- relation.sourceOf(d, outData.keys)) (decl, outData(d2)) match {
        case (SList(List(Atom("par"), SList(ps), cs)), SList(List(Atom("par"), SList(ps2), cs2))) =>
          relation.relate(cs, cs2, bind(ps, ps2, Map.empty, decl, outData(d2)))
        case (decl, decl2) => relation.relate(decl, decl2, Map.empty)
      }
      // the datatype and the functions of the encoder of bags are those of the encoder
      if (encoders.contains("bags")) {
        for ((d, decl) <- outData if relation.theory(d, "sort", "Bag")) relation.theoryDefinition(BagDatatype, decl)
        for ((f, (ps, xs, range, body)) <- outFuns; (name, pattern) <- List("get" -> BagGet, "inv" -> BagInvariant)
             if relation.theory(f, "function", name))
          relation.theoryDefinition(pattern, SList(List(SList(ps), SList(xs), range, body)))
      }
      lines.size
    case _ => fail("the input of the certificate is not one")
  }

  // The definitions of the encoder of bags (see `solvers.theories.BagEncoder`), as the sources
  // print them: each `?x` stands for a symbol, the same wherever it occurs. Those of a name of the
  // encoder (`?Bag`, `?Node`, `?op` ..) are its symbols, and the others are bound variables.
  private val BagDatatype = Checker.parse(
    "(par (?T) ((?Node (?op Int) (?left (?Bag ?T)) (?right (?Bag ?T))) (?Elem (?key ?T) (?value Int)) (?Leaf)))").head
  // the sort parameters, the parameters, the sort and the body of `get`
  private val BagGet = Checker.parse("""((?T) ((?b (?Bag ?T)) (?x ?T)) Int
    (ite ((as (_ is ?Node) (?Bag ?T)) ?b)
      (let ((?v1 ((as ?get (?T)) ((as ?left (?Bag ?T)) ?b) ?x)))
      (let ((?v2 ((as ?get (?T)) ((as ?right (?Bag ?T)) ?b) ?x)))
      (ite (= ((as ?op (?Bag ?T)) ?b) 0) (+ ?v1 ?v2)
      (ite (= ((as ?op (?Bag ?T)) ?b) 1) (ite (<= ?v1 ?v2) 0 (- ?v1 ?v2))
      (ite (<= ?v1 ?v2) ?v1 ?v2)))))
      (ite (and ((as (_ is ?Elem) (?Bag ?T)) ?b) (= ((as ?key (?Bag ?T)) ?b) ?x)) ((as ?value (?Bag ?T)) ?b) 0)))""").head
  // the invariant of the datatype: multiplicities are not negative
  private val BagInvariant = Checker.parse("""((?T) ((?b (?Bag ?T))) Bool
    (or (not ((as (_ is ?Elem) (?Bag ?T)) ?b)) (>= ((as ?value (?Bag ?T)) ?b) 0)))""").head
  // the kind of each symbol of the encoder that its definitions name
  private val BagSymbols: Map[String, Relation => Atom => Boolean] = Map(
    "Bag" -> (r => r.theory(_, "sort", "Bag")),
    "Node" -> (r => r.theory(_, "constructor", "Node")),
    "Elem" -> (r => r.theory(_, "constructor", "Elem")),
    "Leaf" -> (r => r.theory(_, "constructor", "Leaf")),
    "op" -> (r => r.selector(_, "Node", 0)),
    "left" -> (r => r.selector(_, "Node", 1)),
    "right" -> (r => r.selector(_, "Node", 2)),
    "key" -> (r => r.selector(_, "Elem", 0)),
    "value" -> (r => r.selector(_, "Elem", 1)),
    "get" -> (r => r.theory(_, "function", "get")))

  /** The functions that `commands`, declarations and definitions of SMT-LIB 3, define: each
    * defined symbol with its sort parameters, its parameters, its sort and its body. */
  private def functions(commands: Seq[SExpr]): Map[Atom, (List[SExpr], List[SExpr], SExpr, SExpr)] = {
    def signature(s: SExpr): (Atom, List[SExpr], List[SExpr], SExpr) = s match {
      case SList(List(Atom("par"), SList(ps), SList(List(f: Atom, SList(xs), range)))) => (f, ps, xs, range)
      case SList(List(f: Atom, SList(xs), range)) => (f, Nil, xs, range)
      case other => fail(s"$other is not the signature of a function")
    }
    commands.flatMap {
      case SList(List(Atom("define-fun" | "define-fun-rec"), f: Atom, SList(xs), range, body)) => List(f -> (Nil, xs, range, body))
      case SList(List(Atom("define-fun" | "define-fun-rec"), SList(List(Atom("par"), SList(ps), SList(List(f: Atom, SList(xs), range, body)))))) =>
        List(f -> (ps, xs, range, body))
      case SList(List(Atom("define-funs-rec"), SList(decs), SList(bodies))) if decs.size == bodies.size =>
        (decs zip bodies).map { (d, body) => val (f, ps, xs, range) = signature(d); f -> (ps, xs, range, body) }
      case _ => Nil
    }.toMap
  }

  /** The datatypes that `commands` declare: each sort with its sort parameters and constructors. */
  private def datatypes(commands: Seq[SExpr]): Map[Atom, SExpr] = commands.flatMap {
    case SList(List(Atom("declare-datatypes"), SList(sorts), SList(decls))) if sorts.size == decls.size =>
      (sorts zip decls).collect { case (SList(List(d: Atom, _)), decl) => d -> decl }
    case _ => Nil
  }.toMap

  private final class Relation(encoders: Set[String], input: Seq[Entry], sources: Seq[Entry]) {
    private val inputs: Map[Atom, Entry] = input.map(e => e.name -> e).toMap
    private val outputs: Map[Atom, Entry] = sources.map(e => e.name -> e).toMap
    private val inputIds: Set[(String, String)] = input.flatMap(e => id(e).map(e.kind -> _)).toSet

    // the identifier `name$id` that a symbol is described with: a sort is described with a type
    // `name$id[..]` of its datatype
    private def id(e: Entry): Option[String] = e.descriptions.headOption.map { d =>
      val text = d.stripPrefix("\"").stripSuffix("\"")
      val i = text.indexOf('[')
      if (i < 0) text else text.substring(0, i)
    }

    // what a symbol stands for, whatever the types: its kind and its identifier, and for a
    // selector the index of its field
    private def identifier(e: Entry): (String, Option[String], Option[String]) =
      (e.kind, id(e), if (e.kind == "selector") e.descriptions.lastOption else None)

    // the name of an identifier `name$id`
    private def nameOf(text: String): String = {
      val i = text.lastIndexOf('$')
      if (i < 0) text else text.substring(0, i)
    }

    // a sort of the theories, which both sides name alike and only one table may have
    private def builtin(e: Entry): Boolean = e.kind == "sort" && id(e).exists(!_.contains('$'))

    /** `a` is the symbol of an encoder: one of the sources of kind `kind` that stands for an
      * identifier of name `name` that the input doesn't have. */
    def theory(a: SExpr, kind: String, name: String): Boolean = a match {
      case a: Atom => outputs.get(a).exists(e => e.kind == kind && id(e).exists { d =>
        nameOf(d) == name && !inputIds(kind -> d)
      })
      case _ => false
    }

    /** The symbol of the input among `ins` that stands for the identifier that `a`, a symbol of
      * the sources, stands for. */
    def inputOf(a: Atom, ins: Iterable[Atom]): Option[Atom] =
      outputs.get(a).flatMap(y => ins.find(b => inputs.get(b).exists(x => identifier(x) == identifier(y))))

    /** The symbol of the sources among `outs` that stands for the identifier that `a`, a symbol
      * of the input, stands for. */
    def sourceOf(a: Atom, outs: Iterable[Atom]): Option[Atom] =
      inputs.get(a).flatMap(x => outs.find(b => outputs.get(b).exists(y => identifier(x) == identifier(y))))

    /** `a` is the selector of index `index` of the constructor `name` of an encoder: a selector
      * of the sources, described by a constructor of that name that the input doesn't have. */
    def selector(a: Atom, name: String, index: Int): Boolean = outputs.get(a).exists { e =>
      e.kind == "selector" && e.descriptions.lastOption.contains("\"" + index + "\"") && id(e).exists { d =>
        nameOf(d) == name && !inputIds("constructor" -> d)
      }
    }

    /** Checks that `definition`, of the sources, is `pattern`, a definition of an encoder. */
    def theoryDefinition(pattern: SExpr, definition: SExpr): Unit = {
      val binding = scala.collection.mutable.Map[String, Atom]()
      def matches(p: SExpr, t: SExpr): Boolean = (p, t) match {
        case (Atom(x), a: Atom) if x.startsWith("?") => binding.getOrElseUpdate(x, a) == a
        case (SList(ps), SList(ts)) => ps.size == ts.size && (ps zip ts).forall(matches(_, _))
        case _ => p == t
      }
      if (!matches(pattern, definition) ||
          binding.exists { (x, a) => Encoders.BagSymbols.get(x.drop(1)).exists(is => !is(this)(a)) } ||
          binding.values.toSeq.distinct.size != binding.size)
        fail(s"$definition is not the definition of the encoder")
    }

    def no(in: SExpr, out: SExpr): Nothing = fail(s"$out is not what the encoders make of $in")

    private def isInt(a: SExpr): Option[BigInt] = a match {
      case Atom(t) if t.nonEmpty && t.forall(_.isDigit) => Some(BigInt(t))
      case SList(List(Atom("-"), Atom(t))) if t.nonEmpty && t.forall(_.isDigit) => Some(-BigInt(t))
      case _ => None
    }

    // `out` is `(as c S)` for the constructor `name` of the encoder of bags, and `S` is its datatype
    private def bagConstructor(out: SExpr, name: String): Boolean = out match {
      case SList(List(Atom("as"), c, SList(List(b, _)))) => theory(c, "constructor", name) && theory(b, "sort", "Bag")
      case _ => false
    }

    private def node(out: SExpr): Option[(SExpr, SExpr, SExpr)] = out match {
      case SList(List(head, op, a, b)) if bagConstructor(head, "Node") => Some((op, a, b))
      case _ => None
    }

    // `out` is what the encoder of bags makes of the element `k` with the multiplicity `v`
    private def elem(k: SExpr, v: SExpr, out: SExpr, bound: Map[Atom, Atom]): Boolean = {
      def isElem(e: SExpr): Boolean = e match {
        case SList(List(head, k2, v2)) if bagConstructor(head, "Elem") => relate(k, k2, bound); relate(v, v2, bound); true
        case _ => false
      }
      isInt(v) match {
        case Some(i) if i > 0 => isElem(out)
        case Some(_) => bagConstructor(out, "Leaf")
        case None => out match {
          case SList(List(Atom("ite"), SList(List(Atom(">"), v2, Atom("0"))), e, leaf)) =>
            relate(v, v2, bound); isElem(e) && bagConstructor(leaf, "Leaf")
          case _ => false
        }
      }
    }

    /** Checks that `out` is what the encoders make of `in`, where the variables that `in` binds
      * face those that `bound` gives. */
    def relate(in: SExpr, out: SExpr, bound: Map[Atom, Atom]): Unit = (in, out) match {
      case (a: Atom, b: Atom) if bound.contains(a) => if (bound(a) != b) no(in, out)
      case (a: Atom, b: Atom) => (inputs.get(a), outputs.get(b)) match {
        case (Some(x), Some(y)) => if (identifier(x) != identifier(y)) no(in, out)
        case (None, None) => if (a != b) no(in, out)
        case (Some(x), None) => if (a != b || !builtin(x)) no(in, out)
        case (None, Some(y)) => if (a != b || !builtin(y)) no(in, out)
      }

      // bags
      case (SList(List(Atom("Bag"), t)), SList(List(b, t2))) if encoders("bags") =>
        if (!theory(b, "sort", "Bag")) no(in, out)
        relate(t, t2, bound)
      case (SList(List(Atom("as"), Atom("bag.empty"), t)), SList(List(Atom("as"), _, SList(List(_, t2))))) if encoders("bags") =>
        if (!bagConstructor(out, "Leaf")) no(in, out)
        relate(t, t2, bound)
      case (SList(List(Atom("bag.insert"), b, e)), _) if encoders("bags") => node(out) match {
        case Some((Atom("0"), b2, SList(List(head, e2, Atom("1"))))) if bagConstructor(head, "Elem") =>
          relate(b, b2, bound); relate(e, e2, bound)
        case _ => no(in, out)
      }
      case (SList(List(Atom(op @ ("bag.union" | "bag.difference" | "bag.intersection")), a, b)), _) if encoders("bags") =>
        val code = op match { case "bag.union" => "0"; case "bag.difference" => "1"; case _ => "2" }
        node(out) match {
          case Some((Atom(`code`), a2, b2)) => relate(a, a2, bound); relate(b, b2, bound)
          case _ => no(in, out)
        }
      case (SList(List(Atom("bag.multiplicity"), e, b)), SList(List(SList(List(Atom("as"), g, SList(List(_)))), b2, e2))) if encoders("bags") =>
        if (!theory(g, "function", "get")) no(in, out)
        relate(b, b2, bound); relate(e, e2, bound)
      case (SList(List(Atom("bag.singleton"), k, v)), SList(List(Atom("ite"), Atom("false"), leaf, sum))) if encoders("bags") =>
        (bagConstructor(leaf, "Leaf"), node(sum)) match {
          case (true, Some((Atom("0"), leaf2, e))) if bagConstructor(leaf2, "Leaf") && elem(k, v, e, bound) =>
          case _ => no(in, out)
        }
      case (SList(Atom("bag.empty" | "bag.insert" | "bag.union" | "bag.difference" | "bag.intersection" |
                       "bag.multiplicity" | "bag.singleton") :: _), _) if encoders("bags") => no(in, out)

      // the merge of two maps
      case (SList(List(Atom("map.merge"), mask, m1, m2)), SList(List(SList(List(Atom("as"), f, SList(List(_, _)))), mask2, n1, n2)))
          if encoders("map-merge") =>
        if (!theory(f, "function", "mapMerge")) no(in, out)
        relate(mask, mask2, bound); relate(m1, n1, bound); relate(m2, n2, bound)

      // binders: the variables that they bind face each other
      case (SList(List(Atom(q @ ("forall" | "exists" | "lambda" | "choose")), SList(xs), body)),
            SList(List(Atom(q2), SList(ys), body2))) if q == q2 && xs.size == ys.size =>
        val pairs = (xs zip ys).map {
          case (SList(List(x: Atom, s)), SList(List(y: Atom, s2))) => relate(s, s2, bound); x -> y
          case _ => no(in, out)
        }
        relate(body, body2, bound ++ pairs)
      case (SList(List(Atom("let"), SList(xs), body)), SList(List(Atom("let"), SList(ys), body2))) if xs.size == ys.size =>
        val pairs = (xs zip ys).map {
          case (SList(List(x: Atom, e)), SList(List(y: Atom, e2))) => relate(e, e2, bound); x -> y
          case _ => no(in, out)
        }
        relate(body, body2, bound ++ pairs)

      case (SList(xs), SList(ys)) if xs.size == ys.size => (xs zip ys).foreach { case (x, y) => relate(x, y, bound) }
      case _ => no(in, out)
    }
  }
}
