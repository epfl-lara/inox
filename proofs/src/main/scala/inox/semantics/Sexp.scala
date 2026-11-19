/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package semantics

/** S-expressions: atoms and lists, with `;` comments. */
enum Sexp {
  case Atom(name: String)
  case Lst(items: Seq[Sexp])

  override def toString: String = this match {
    case Atom(n) => n
    case Lst(items) => items.mkString("(", " ", ")")
  }
}

object Sexp {
  final class ParseError(msg: String) extends Exception(msg)

  def parseAll(text: String): Seq[Sexp] = {
    var pos = 0
    def skip(): Unit = {
      while (pos < text.length && (text(pos).isWhitespace || text(pos) == ';')) {
        if (text(pos) == ';') while (pos < text.length && text(pos) != '\n') pos += 1
        else pos += 1
      }
    }
    def line = text.take(pos).count(_ == '\n') + 1
    def one(): Sexp = {
      skip()
      if (pos >= text.length) throw ParseError("unexpected end")
      text(pos) match {
        case '(' =>
          pos += 1
          val items = Seq.newBuilder[Sexp]
          skip()
          while (pos < text.length && text(pos) != ')') { items += one(); skip() }
          if (pos >= text.length) throw ParseError(s"unclosed parenthesis before line $line")
          pos += 1
          Lst(items.result())
        case ')' => throw ParseError(s"unexpected ) at line $line")
        case _ =>
          val start = pos
          while (pos < text.length && !text(pos).isWhitespace && text(pos) != '(' && text(pos) != ')' && text(pos) != ';')
            pos += 1
          Atom(text.substring(start, pos))
      }
    }
    val res = Seq.newBuilder[Sexp]
    skip()
    while (pos < text.length) { res += one(); skip() }
    res.result()
  }
}
