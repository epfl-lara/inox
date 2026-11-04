/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package utils

import org.scalatest.funsuite.AnyFunSuite

import Graphs._
import GraphPrinters._

class GraphPrintersSuite extends AnyFunSuite {

  type G = DiGraph[String, SimpleEdge[String]]
  type LG = DiGraph[String, LabeledEdge[String, String]]

  private val graph: G = DiGraph[String, SimpleEdge[String]]() +
    SimpleEdge("a", "b") + SimpleEdge("b", "c") + SimpleEdge("a", "c") + "d"

  // The lines declaring nodes and edges, without the digraph header and footer
  private def body(dot: String): Seq[String] = {
    val lines = dot.split("\n").toSeq
    assert(lines.head == "digraph D {")
    assert(lines.last == "}")
    lines.drop(1).dropRight(1)
  }

  private def nodeName(dot: String, label: String): String =
    body(dot).collectFirst {
      case l if l.contains(s"""label="$label"""") => l.takeWhile(_ != ' ')
    }.getOrElse(fail(s"No node labeled $label in:\n$dot"))

  test("Every node and edge is printed once") {
    val dot = new DotPrinter[String, SimpleEdge[String], G].asString(graph)
    val lines = body(dot)
    assert(lines.count(_.contains("label=")) == 4)
    assert(lines.count(_.contains("->")) == 3)

    val names = Seq("a", "b", "c", "d").map(n => n -> nodeName(dot, n)).toMap
    assert(names.values.toSet.size == 4, "node names must be unique")
    for ((from, to) <- Seq("a" -> "b", "b" -> "c", "a" -> "c"))
      assert(lines.contains(s"  ${names(from)} -> ${names(to)} [];"))
  }

  test("Node labels can be customized and are escaped") {
    val printer = new DotPrinter[String, SimpleEdge[String], G]
    printer.setNodeLabel(n => s"""node "$n"""")
    val dot = printer.asString(graph)
    assert(body(dot).exists(_.contains("""label="node \"a\""""")))
  }

  test("Highlighted and colorized nodes get a color option") {
    val printer = new DotPrinter[String, SimpleEdge[String], G]
    printer.highlight(_ == "a")
    printer.colorize(_ == "b", "blue")
    val dot = printer.asString(graph)
    val lines = body(dot)
    assert(lines.filter(_.contains("color=")).size == 2)
    assert(lines.exists(l => l.contains("""label="a"""") && l.contains("color=red")))
    assert(lines.exists(l => l.contains("""label="b"""") && l.contains("color=blue")))
  }

  test("Labeled edges go through a box holding the label") {
    val lg: LG = DiGraph[String, LabeledEdge[String, String]]() + LabeledEdge("a", "b", "calls")
    val dot = new DotPrinter[String, LabeledEdge[String, String], LG].asString(lg)
    val lines = body(dot)
    val box = lines.find(_.contains("""label="calls"""")).getOrElse(fail(dot))
    assert(box.contains("shape=box"))
    val boxName = box.takeWhile(_ != ' ')
    assert(lines.contains(s"  ${nodeName(dot, "a")} -> $boxName [];"))
    assert(lines.contains(s"  $boxName -> ${nodeName(dot, "b")} [];"))
  }

  test("Graphs can be written to a file") {
    val file = java.io.File.createTempFile("graph", ".dot")
    try {
      val printer = new DotPrinter[String, SimpleEdge[String], G]
      printer.asFile(graph, file.getPath)
      val source = scala.io.Source.fromFile(file)
      try assert(source.mkString == printer.asString(graph))
      finally source.close()
    } finally file.delete()
  }

  test("DotHelpers escape labels") {
    val dot = new DotHelpers
    assert(dot.escape("""say "hi"""") == """say \"hi\"""")
    assert(dot.escape("a\\b") == "a\\\\b")
    assert(dot.escape("line1\nline2") == "line1\\nline2")
    assert(dot.escape("a~b|c") == "a?b?c")
    assert(dot.escapeStrict("List.size-1") == "List_size_1")
  }

  test("DotHelpers build nodes and arrows") {
    val dot = new DotHelpers
    assert(dot.arrow("x", "y") == "  x -> y [];\n")
    assert(dot.labeledArrow("x", "l", "y") == "  x -> y [label=\"l\"];\n")
    assert(dot.labeledDashedArrow("x", "l", "y") == "  x -> y [label=\"l\" style=dashed];\n")
    assert(dot.node("n", "name") == "n [label=\"name\"];\n")
    assert(dot.box("n", "name") == "n [label=\"name\", shape=box, color=lightblue, style=filled];\n")
    assert(dot.invisNode("n", "name") == "n [label=\"name\", shape=none];\n")
    assert(dot.dashedNode("n", "name") == "n [label=\"name\", style=dashed];\n")
  }

  test("DotHelpers give each object a stable unique name") {
    val dot = new DotHelpers
    val a = dot.uniqueName("n", "a")
    val b = dot.uniqueName("n", "b")
    assert(a != b)
    assert(dot.uniqueName("n", "a") == a)
    assert(a.startsWith("n") && b.startsWith("n"))
  }

  test("DotHelpers cycle through colors") {
    val dot = new DotHelpers
    val bg = Seq.fill(dot.bgColors.size)(dot.nextColor)
    assert(bg.distinct.size == bg.size)
    val colors = Seq.fill(dot.colors.size)(dot.randomColor)
    assert(colors.toSet == dot.colors.toSet)
  }
}
