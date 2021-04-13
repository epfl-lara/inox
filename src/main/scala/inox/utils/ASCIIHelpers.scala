/* Copyright 2009-2018 EPFL, Lausanne */

package inox.utils

object ASCIIHelpers {
  case class Table(title: String, rows: Seq[TableRow] = Nil) {
    def +(r: TableRow): Table = this ++ Seq(r)
    def ++(rs: Iterable[TableRow]): Table = copy(rows = rows ++ rs)


    private def computeColumnSizes = {
      // First check constraints
      var constraints = Map[(Int, Int), Int]()

      var cellsPerRow = 0
      for((r, j) <- rows.zipWithIndex) r match {
        case r @ Row(cells) =>
          if (cellsPerRow > 0) {
            assert(r.cellsSize == cellsPerRow, s"Row $j has incompatible number of virtual cells (${r.cellsSize} v.s. $cellsPerRow")
          } else {
            cellsPerRow = r.cellsSize
            constraints += (0, cellsPerRow-1) -> 80
          }

          var i = 0
          for (c <- cells) {
            val k = i -> (i+c.spanning-1)

            val cols = constraints.getOrElse(k, 1)

            val size = c.printableWidth

            constraints += k -> (cols max size)

            i += c.spanning
          }
        case _ =>
      }

      // discharge constraints that are spanning
      val toRemove = constraints.keySet.filter { case (from, to) => from != to }.toSeq.sortBy{ s => s._2 - s._1 }

      for (k @ (from, to) <- toRemove) {
        val min = constraints(k)

        val parts = (from to to).map(i => constraints.getOrElse((i, i), 1))

        var sum = parts.sum

        if (sum < min) {
          var remaining = min - sum

          for ((s, i) <- parts.zipWithIndex.sortBy(- _._1)) {
            val inc = Math.round(s*remaining*1d/sum).toInt
            constraints += (from+i, from+i) -> (s + inc)
            remaining -= inc
            sum -= s
          }
        }

        constraints -= k
      }

      (0 until cellsPerRow).map(i => constraints.getOrElse((i, i), 1))
    }

    def render(asciiOnly: Boolean): String = {
      val colSizes = computeColumnSizes
      val titleWidth = trimNonPrintable(title).length
      val fullWidth = Math.max(colSizes.sum + colSizes.size * 2, titleWidth + 7)
      val padWidth = fullWidth - titleWidth - 5

      val sb = new StringBuffer

      val barH = if (asciiOnly) "#" else "─"
      val topLeft = if (asciiOnly) "#" else "┌"
      val topRight = if (asciiOnly) "#" else "┐"
      val bottomLeft = if (asciiOnly) "#" else "└"
      val bottomRight = if (asciiOnly) "#" else "┘"
      val dots = if (asciiOnly) "." else "┄"
      val doubleBarH = if (asciiOnly) "#" else "═"
      val doubleBarV = if (asciiOnly) "#" else "║"
      val doubleTopLeft = if (asciiOnly) "#" else "╔"
      val doubleTopRight = if (asciiOnly) "#" else "╗"
      val doubleBottomLeft = if (asciiOnly) "#" else "╚"
      val doubleBottomRight = if (asciiOnly) "#" else "╝"

      val leftConnect = if (asciiOnly) "#" else "╡"
      val rightConnect = if (asciiOnly) "#" else "╞"
      val doubleRightConnect = if (asciiOnly) "#" else "╟"
      val doubleLeftConnect = if (asciiOnly) "#" else "╢"

      sb append s"  $topLeft$barH" + (barH * titleWidth) + s"$barH$topRight\n"
      sb append s"$doubleTopLeft$doubleBarH$leftConnect " + title + s" $rightConnect" + (doubleBarH * padWidth) + s"$doubleTopRight\n"
      sb append s"$doubleBarV $bottomLeft$barH" + (barH * titleWidth) + s"$barH$bottomRight"  + (" " * padWidth) + s"$doubleBarV\n"

      for (r <- rows) r match {
        case Separator =>
          sb append doubleRightConnect + (dots * fullWidth) + s"$doubleLeftConnect\n"

        case Row(cells) =>
          sb append s"$doubleBarV "
          var i = 0
          for (c <- cells) {
            if (i > 0) {
              sb append "  "
            }

            val size = (i until i + c.spanning).map(colSizes).sum + (c.spanning-1) * 2

            if (size >= 0) {
              if (c.align == Left) {
                sb append ("%-"+(size+c.invisibleWidth)+"s").format(c.vString)
              } else {
                sb append ("%"+(size+c.invisibleWidth)+"s").format(c.vString)
              }
            } else {
              sb append c.vString
            }

            i += c.spanning
          }
          sb append s" $doubleBarV\n"
      }

      sb append doubleBottomLeft + (doubleBarH * fullWidth) + doubleBottomRight

      sb.toString
    }
  }

  abstract class TableRow
  case object Separator extends TableRow
  case class Row(cells: Seq[Cell]) extends TableRow {
    def cellsSize = {
      cells.map(_.spanning).sum
    }
  }
  sealed abstract class Alignment
  case object Left extends Alignment
  case object Right extends Alignment

  case class Cell(v: Any, spanning: Int = 1, align: Alignment = Left) {
    require(spanning >= 1)

    lazy val vString = v.toString

    lazy val printableWidth = trimNonPrintable(vString).length
    lazy val fullWidth      = vString.length
    lazy val invisibleWidth = fullWidth-printableWidth
  }

  def trimNonPrintable(str: String): String = {
    str.replaceAll("\u001b\\[[0-9;]*m", "")
  }
}
