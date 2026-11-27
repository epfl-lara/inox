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
  * that the input doesn't have. */
object Encoders {
  private val known = Set("propositions", "bags", "map-merge")

  /** Checks the input `input` of a certificate whose sources have the symbols `sourceSymbols`,
    * and gives the number of constraints that it checked: none when the certificate has no
    * input. */
  def check(input: List[SExpr], sourceSymbols: Seq[SExpr]): Int = input match {
    case Nil => 0
    case SList(Atom("encoders") :: names) :: SList(Atom("definitions") :: _) :: rest if rest.nonEmpty =>
      val (constraints, symbols) = (rest.init, rest.last match {
        case SList(Atom("symbols") :: lines) => lines.map(entry)
        case other => fail(s"$other is not the symbols of the input")
      })
      val encoders = names.map {
        case Atom(n) if n.startsWith("\"") && n.endsWith("\"") && n.length >= 2 => n.substring(1, n.length - 1)
        case other => fail(s"$other is not the name of an encoder")
      }
      for (n <- encoders if !known(n)) fail(s"the checker doesn't check the encoder $n")
      val relation = new Relation(encoders.toSet, symbols, sourceSymbols.map(entry))
      for (c <- constraints) c match {
        case SList(List(Atom("constraint"), in, SList(List(Atom("encoded"), out)))) => relation.relate(in, out, Map.empty)
        case other => fail(s"$other is not a constraint of the input")
      }
      constraints.size
    case _ => fail("the input of the certificate is not one")
  }

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
    private def theory(a: SExpr, kind: String, name: String): Boolean = a match {
      case a: Atom => outputs.get(a).exists(e => e.kind == kind && id(e).exists { d =>
        nameOf(d) == name && !inputIds(kind -> d)
      })
      case _ => false
    }

    private def no(in: SExpr, out: SExpr): Nothing = fail(s"$out is not what the encoders make of $in")

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
