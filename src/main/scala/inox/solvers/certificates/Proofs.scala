/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package certificates

/** An s-expression of a proof. A symbol of the solver's session is a [[Sym]], with the Inox
  * variable, function, sort or constructor that it stands for. Other atoms keep the text that the
  * solver printed (numerals, keywords, strings, the solver's own symbols), since proof formats such
  * as CPC have literals that SMT-LIB doesn't, as `-1` or `1/2`. */
sealed trait SExpr {
  /** The s-expression where each atom that `table` maps (without its quotes `|...|`) is a symbol. */
  def resolve(table: String => Option[Ref]): SExpr = this match {
    case a @ Atom(text) =>
      val name = if (text.length >= 2 && text.head == '|' && text.last == '|') text.substring(1, text.length - 1) else text
      table(name).fold(a)(Sym(text, _))
    case SList(items) => SList(items.map(_.resolve(table)))
    case sym: Sym => sym
  }

  /** The symbols of the s-expression, by their text. */
  def symbols: Seq[Sym] = this match {
    case _: Atom => Seq()
    case SList(items) => items.flatMap(_.symbols)
    case sym: Sym => Seq(sym)
  }

  override def toString: String = {
    val sb = new StringBuilder
    def rec(e: SExpr): Unit = e match {
      case Atom(text) => sb ++= text
      case Sym(text, _) => sb ++= text
      case SList(items) =>
        sb += '('
        for ((item, i) <- items.zipWithIndex) {
          if (i > 0) sb += ' '
          rec(item)
        }
        sb += ')'
    }
    rec(this)
    sb.toString
  }
}

final case class Atom(text: String) extends SExpr
final case class SList(items: Seq[SExpr]) extends SExpr
/** A symbol of the solver's session, as the solver printed it, and what it stands for. */
final case class Sym(text: String, ref: Ref) extends SExpr

/** What a symbol of a solver's session stands for, in the Inox trees of the solver's program
  * (certificates are for programs of Inox trees). */
sealed trait Ref {
  /** What the symbol stands for, as a certificate prints it: its kind, then the identifier (with
    * its unique id), types and index that it has, as strings. */
  def describe: Seq[String] = {
    import inox.trees.PrinterOptions
    val opts = PrinterOptions(printUniqueIds = true)
    def tp(t: inox.trees.Type) = t.asString(using opts)
    this match {
      case Ref.Variable(v) => Seq("variable", v.id.uniqueName, tp(v.tpe))
      case Ref.Function(id, tps) => Seq("function", id.uniqueName) ++ tps.map(tp)
      case Ref.Uninterpreted(id) => Seq("uninterpreted", id.uniqueName)
      case Ref.Lambda(tpe) => Seq("application", tp(tpe))
      case Ref.Sort(tpe) => Seq("sort", tp(tpe))
      case Ref.Constructor(id, tpe) => Seq("constructor") ++ id.map(_.uniqueName) ++ Seq(tp(tpe))
      case Ref.Selector(id, tpe, index) => Seq("selector") ++ id.map(_.uniqueName) ++ Seq(tp(tpe), index.toString)
      case Ref.Tester(id, tpe) => Seq("tester") ++ id.map(_.uniqueName) ++ Seq(tp(tpe))
    }
  }
}
object Ref {
  import inox.trees as t

  final case class Variable(v: t.Variable) extends Ref
  /** A function, under its type arguments. */
  final case class Function(id: Identifier, tps: Seq[t.Type]) extends Ref
  /** An uninterpreted function of the underlying solver (see [[unrolling.Templates]]). */
  final case class Uninterpreted(id: Identifier) extends Ref
  /** The application of functions of type `tpe`. */
  final case class Lambda(tpe: t.FunctionType) extends Ref
  final case class Sort(tpe: t.Type) extends Ref
  /** The constructor of type `tpe`, which is `id` for an ADT constructor (and the constructor of a
    * tuple, of a type parameter or of unit otherwise), and its selectors and tester. */
  final case class Constructor(id: Option[Identifier], tpe: t.Type) extends Ref
  final case class Selector(id: Option[Identifier], tpe: t.Type, index: Int) extends Ref
  final case class Tester(id: Option[Identifier], tpe: t.Type) extends Ref
}

object SExpr {
  /** The s-expressions of `text`, without its comments, or why it has none. */
  def parse(text: String): Either[String, Seq[SExpr]] = {
    var stack = List(scala.collection.mutable.ArrayBuffer[SExpr]())
    var i = 0
    val n = text.length
    def until(end: Char): Int = {
      val j = text.indexOf(end, i + 1)
      if (j < 0) throw new IllegalArgumentException(s"unterminated $end at $i") else j + 1
    }
    try {
      while (i < n) text(i) match {
        case c if c.isWhitespace => i += 1
        case ';' => i = { val j = text.indexOf('\n', i); if (j < 0) n else j + 1 }
        case '(' =>
          stack = scala.collection.mutable.ArrayBuffer[SExpr]() :: stack
          i += 1
        case ')' =>
          if (stack.tail.isEmpty) throw new IllegalArgumentException(s"unbalanced ) at $i")
          val items = stack.head.toSeq
          stack = stack.tail
          stack.head += SList(items)
          i += 1
        case '|' =>
          val start = i
          val j = until('|')
          stack.head += Atom(text.substring(start, j))
          i = j
        case '"' =>
          val start = i
          // a quote in a string is doubled
          var j = until('"')
          while (j < n && text(j) == '"') { i = j; j = until('"') }
          stack.head += Atom(text.substring(start, j))
          i = j
        case _ =>
          var j = i
          while (j < n && !text(j).isWhitespace && "();|\"".indexOf(text(j)) < 0) j += 1
          stack.head += Atom(text.substring(i, j))
          i = j
      }
      if (stack.tail.nonEmpty) Left("unbalanced (") else Right(stack.head.toSeq)
    } catch {
      case e: IllegalArgumentException => Left(e.getMessage)
    }
  }
}

/** The proof of an unsat answer (see [[SolverResponses.UnsatWithProof]]), which `toString` prints. */
sealed trait Proof

/** A solver's proof that `script` has no model: the commands that declare its symbols and assert
  * its clauses, and the solver's CPC proof, whose assumptions are the asserts of `script`:
  * {{{
  * (script
  * <the commands>
  * (check-sat)
  * )
  * (cpc
  * <the proof>
  * )
  * }}}
  */
final case class ScriptProof(script: Seq[SExpr], cpc: Seq[SExpr]) extends Proof {
  /** The asserted terms of the script, in order. */
  def asserts: Seq[SExpr] = script.collect { case SList(Seq(Atom("assert"), t)) => t }

  override def toString: String = Proof.block("script", script :+ SList(Seq(Atom("check-sat")))) + "\n" + Proof.block("cpc", cpc)
}

object Proof {
  private[certificates] def block(name: String, es: Seq[Any]): String = s"($name\n${es.map(_.toString + "\n").mkString})"
}
