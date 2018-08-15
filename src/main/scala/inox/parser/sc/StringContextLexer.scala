/* Copyright 2017 EPFL, Lausanne */

package inox
package parser
package sc

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.token._
import scala.util.parsing.input._

/** Contains methods for lexical parsing of StringContext objects and their arguments. */
trait StringContextLexer extends { self: Lexical =>

  /** Returns the token for a hole. */
  def toHole(index: Int): Token

  /** Returns a reader from a StringContext and its arguments. */
  def getReader(sc: StringContext): Reader[Token] = {

    // For string parts, we can create a Scanner.
    val stringReaders = sc.parts.zipWithIndex.map {
      case (string, index) => toPartReader(string, sc, index)
    }

    // Handle holes.
    val holeReaders = Seq.tabulate(sc.parts.size - 1) { (index: Int) =>
      toHoleReader(sc, index)
    }

    // Intercalates holeReaders between stringReaders.
    val readers = stringReaders.head +: {
      holeReaders.zip(stringReaders.tail).flatMap {
        case (argReader, stringReader) => Seq(argReader, stringReader)
      }
    }

    // Sequences all readers into a single one.
    readers.reduce(sequenceReader(_, _))
  }

  private def toHoleReader(context: StringContext, index: Int) = new Reader[Token] {
    override def atEnd: Boolean = false
    override def first: Token = toHole(index)
    override def pos: Position = InArgumentPosition(index + 1, context)
    override def rest: Reader[Token] = new Reader[Token] {
      override def atEnd: Boolean = true
      override def pos: Position = ???
      override def first: Token = ???
      override def rest: Reader[Token] = ???
    }
  }

  private def toPartReader(string: String, context: StringContext, index: Int) = {
    class Wrapper(reader: Reader[Token]) extends Reader[Token] {
      override def atEnd: Boolean = reader.atEnd
      override def first: Token = reader.first
      override def rest: Reader[Token] = new Wrapper(reader.rest)
      override def pos: Position = {
        val p = reader.pos

        InPartPosition(index + 1, context, p.line, p.column)
      }
    }

    new Wrapper(new Scanner(string))
  }

  /** Sequences two readers. */
  private def sequenceReader(a: Reader[Token], b: => Reader[Token]): Reader[Token] = {

    if (a.atEnd) {
      b
    }
    else {
      new Reader[Token] {
        override def atEnd: Boolean = false
        override def first: Token = a.first
        override def pos: Position = a.pos
        override def rest: Reader[Token] = {
          sequenceReader(a.rest, b)
        }
      }
    }
  }
}
