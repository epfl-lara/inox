/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package utils

import org.scalatest.funsuite.AnyFunSuite

import ASCIIHelpers._

class ASCIIHelpersSuite extends AnyFunSuite {

  // Display width, ignoring ANSI color codes
  private def width(line: String): Int = trimNonPrintable(line).length

  private val table = Table("Results") +
    Row(Seq(Cell("name"), Cell("time", align = Right))) +
    Separator +
    Row(Seq(Cell("short"), Cell(1, align = Right))) +
    Row(Seq(Cell("a much longer name"), Cell(12345, align = Right)))

  test("ASCII rendering lays out the title, rows and separators") {
    val lines = table.render(asciiOnly = true).split("\n").toSeq
    // title box (3 lines), header, separator and 2 rows (the bottom line is empty in ASCII)
    assert(lines.size == 7)
    assert(lines(1).contains(" Results "))
    assert(lines(3).startsWith("name "))
    assert(lines(4).forall(_ == '.'))
    assert(lines.forall(_.forall(_ < 128)), "asciiOnly output contains non-ASCII characters")
  }

  test("Tables fill at least 80 columns and keep columns aligned") {
    val rows = table.render(asciiOnly = true).split("\n").toSeq.slice(3, 7).filterNot(_.startsWith("."))
    assert(rows.map(_.length).distinct.size == 1, rows)
    // the 80 columns are shared between the columns in proportion to their content
    assert(rows.head.length == 80 + 2 + 1)
    assert(rows.head.indexOf("time") > "a much longer name".length * 3)
    // right-aligned values end at the same column
    assert(rows.map(_.trim.last) == Seq('e', '1', '5'))
  }

  test("Columns are as wide as their widest cell once past 80 columns") {
    val wide = "x" * 90
    val rows = (Table("Wide") + Row(Seq(Cell("a"), Cell("b"))) + Row(Seq(Cell(wide), Cell("ccc"))))
      .render(asciiOnly = true).split("\n").toSeq.drop(3) // the bottom line is empty in ASCII
    assert(rows.map(_.length) == Seq(90 + 2 + 3 + 1, 90 + 2 + 3 + 1))
    assert(rows.head == "a" + " " * 89 + "  b   ")
  }

  test("Unicode rendering draws a box of uniform width") {
    val lines = table.render(asciiOnly = false).split("\n").toSeq
    assert(lines.head.trim.startsWith("┌"))
    assert(lines(1).startsWith("╔"))
    assert(lines.last.startsWith("╚") && lines.last.endsWith("╝"))
    assert(lines.exists(_.startsWith("╟")), "separator row missing")
    val widths = lines.drop(1).map(width).distinct
    assert(widths.size == 1, s"lines have different widths: $widths")
  }

  test("Color codes don't count towards the column width") {
    val colored = Table("T") +
      Row(Seq(Cell(Console.RED + "red" + Console.RESET), Cell("x"))) +
      Row(Seq(Cell("plain"), Cell("y")))
    val lines = colored.render(asciiOnly = false).split("\n").toSeq
    val widths = lines.drop(1).map(width).distinct
    assert(widths.size == 1, s"lines have different widths: $widths")
    assert(trimNonPrintable(Console.RED + "red" + Console.RESET) == "red")
  }

  test("A cell can span several columns") {
    val spanned = Table("Spans") +
      Row(Seq(Cell("a"), Cell("b"), Cell("c"))) +
      Row(Seq(Cell("a cell spanning two columns", spanning = 2), Cell("c")))
    val lines = spanned.render(asciiOnly = true).split("\n").toSeq
    assert(lines(3).length == lines(4).length)
    assert(lines(4).startsWith("a cell spanning two columns"))
    assert(Row(Seq(Cell("x", spanning = 2), Cell("y"))).cellsSize == 3)
  }

  test("A title wider than the columns sets the table width") {
    val wide = Table("A rather long table title") + Row(Seq(Cell("x")))
    val lines = wide.render(asciiOnly = false).split("\n").toSeq
    assert(lines.drop(1).map(width).distinct.size == 1)
    assert(width(lines.last) >= "A rather long table title".length)
  }

  test("Rows with different numbers of columns are rejected") {
    val bad = Table("Bad") + Row(Seq(Cell("a"), Cell("b"))) + Row(Seq(Cell("c")))
    assertThrows[AssertionError](bad.render(asciiOnly = true))
  }

  test("Cells reject non-positive spans") {
    assertThrows[IllegalArgumentException](Cell("x", spanning = 0))
  }

  test("Tables are extended with + and ++") {
    val t = Table("T") ++ Seq(Row(Seq(Cell("a"))), Separator)
    assert(t.rows.size == 2)
    assert((t + Row(Seq(Cell("b")))).rows.size == 3)
  }
}
