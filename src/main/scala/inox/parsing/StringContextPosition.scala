package inox
package parsing

import scala.util.parsing.input._

trait StringContextPosition extends Position {
  val context: StringContext

  import StringContextPosition._

  override def <(that: Position): Boolean = {
    assert(that.isInstanceOf[StringContextPosition])
    val other = that.asInstanceOf[StringContextPosition]

    (this, other) match {
      case (InArgumentPosition(arg1, _), InArgumentPosition(arg2, _)) =>
        arg1 < arg2
      case (InPartPosition(part, _, _, _), InArgumentPosition(arg, _)) =>
        part <= arg
      case (InArgumentPosition(arg, _), InPartPosition(part, _, _, _)) =>
        arg < part
      case (InPartPosition(part1, _, line1, column1), InPartPosition(part2, _, line2, column2)) =>
        part1 < part2 || (part1 == part2 && (line1 < line2 || (line1 == line2 && column1 < column2))) 
    }
  }

  private def lineOfArg(arg: Int): Int = {
    context.parts.take(arg).map(_.count(_ == '\n')).sum
  }

  private def lineOfPart(part: Int): Int = {
    context.parts.take(part - 1).map(_.count(_ == '\n')).sum
  }

  override lazy val line = this match {
    case InArgumentPosition(arg, _) =>
      lineOfArg(arg) + 1
    case InPartPosition(part, _, partLine, _) =>
      lineOfPart(part) + partLine
  }

  private def columnOfArg(arg: Int): Int = {
    val str = context.parts.take(arg).mkString
    val i = str.lastIndexOf('\n')
    
    if (i < 0) {
      str.length + (1 to (arg - 1)).map(sizeOfArg(_)).sum + 1
    }
    else {
      str.length - (i + 1) + 
      ((arg - 1) to 1 by (-1))
        .takeWhile((j: Int) => !context.parts(j + 1).contains('\n'))
        .map(sizeOfArg(_)).sum + 1
    }
  }

  private def columnOfPart(part: Int): Int = {
    if (part == 1) {
      1
    }
    else {
      val arg = part - 1
      columnOfArg(arg) + sizeOfArg(arg) 
    }
  }

  override lazy val column = this match {

    case InArgumentPosition(arg, _) => {
      columnOfArg(arg)
    }
    case InPartPosition(part, _, partLine, partColumn) => {
      if (partLine == 1) {
        columnOfPart(part) + partColumn - 1
      }
      else {
        partColumn
      }
    }

  }

  override def longString = {
    lineContents + "\n" + 
    " " * (column - 1) + "^"
  }

  override def lineContents = {
    val it = scToString(context).lines.drop(line - 1)
    if (it.hasNext) it.next else ""
  }
}

case class InArgumentPosition(arg: Int, context: StringContext) extends StringContextPosition
case class InPartPosition(part: Int, context: StringContext, partLine: Int, partColumn: Int) extends StringContextPosition

object StringContextPosition {
  def scToString(sc: StringContext): String = {
    sc.parts.head + sc.parts.tail.zipWithIndex.map({
      case (part, i) => "$" + (i + 1) + part
    }).mkString
  }

  def sizeOfArg(arg: Int): Int = {
    arg.toString.length + 1
  }
}