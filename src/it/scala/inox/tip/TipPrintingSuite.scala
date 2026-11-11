/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package tip

import org.scalatest.funsuite.AnyFunSuite

import java.io.{StringReader, StringWriter}

class TipPrintingSuite extends AnyFunSuite with ResourceUtils {
  import inox.trees._

  val ctx = TestContext.empty

  val filesWithCat = resourceFiles("regression/tip/", filter = _ `endsWith` ".tip", recursive = true) map { f =>
    f.getParentFile.getName -> f
  }

  private def checkScript(program: InoxProgram, expr: Expr): Unit = {
    import program.symbols.{given, _}
    symbols.ensureWellFormed

    assert(expr.isTyped)
  }

  for ((cat, file) <- filesWithCat) {
    test(s"Parsing file $cat/${file.getName}") {
      for ((program, expr) <- Parser(file).parseScript) {
        checkScript(program, expr)
      }
    }

    test(s"Re-printing file $cat/${file.getName}") {
      for ((program, expr) <- Parser(file).parseScript) {
        val file = java.io.File.createTempFile("test-output", ".tip")
        file.deleteOnExit()
        val fw = new java.io.FileWriter(file, false)
        val printer = new Printer(program, ctx, fw)
        printer.printScript(expr)
        printer.emit(smtlib.trees.Commands.CheckSat())
        printer.free()

        val Seq((newProgram, newExpr)) = Parser(file).parseScript
        checkScript(newProgram, newExpr)
      }
    }
  }

  /** Prints expressions that the regression files don't contain, and parses them back. */
  private def print(program: InoxProgram, expr: Expr): String = {
    val out = new StringWriter
    val printer = new Printer(program, ctx, out)
    printer.printScript(expr)
    printer.emit(smtlib.trees.Commands.CheckSat())
    printer.free()
    out.toString
  }

  private def roundTrip(program: InoxProgram, expr: Expr): (String, Expr) = {
    val script = print(program, expr)
    val Seq((newProgram, newExpr)) = new Parser(new StringReader(script), None).parseScript
    checkScript(newProgram, newExpr)
    assert(newExpr.getType(using newProgram.symbols) == BooleanType(), s"for\n$script")
    (script, newExpr)
  }

  val empty = InoxProgram(NoSymbols)
  val x = Variable.fresh("x", IntegerType())
  val b = Variable.fresh("b", BooleanType())

  test("Re-printing tuples") {
    val t = Variable.fresh("t", TupleType(Seq(IntegerType(), BooleanType())))
    val t3 = Variable.fresh("t3", TupleType(Seq(IntegerType(), BooleanType(), IntegerType())))
    val (script, _) = roundTrip(empty, And(Seq(
      Equals(t, Tuple(Seq(x, b))),
      Equals(TupleSelect(t, 1), IntegerLiteral(1)),
      Equals(TupleSelect(t3, 3), x),
    )))
    assert(script.contains("declare-datatype"))
  }

  test("Re-printing sets, bags and maps") {
    val s1 = Variable.fresh("s1", SetType(IntegerType()))
    val s2 = Variable.fresh("s2", SetType(IntegerType()))
    val b1 = Variable.fresh("b1", BagType(IntegerType()))
    val b2 = Variable.fresh("b2", BagType(IntegerType()))
    val m1 = Variable.fresh("m1", MapType(IntegerType(), IntegerType()))
    val m2 = Variable.fresh("m2", MapType(IntegerType(), IntegerType()))
    val (script, _) = roundTrip(empty, And(Seq(
      Equals(SetIntersection(s1, s2), SetDifference(s1, s2)),
      SubsetOf(s1, SetUnion(s1, s2)),
      Equals(BagIntersection(b1, b2), BagDifference(b1, b2)),
      Equals(MapApply(MapMerge(s1, m1, m2), x), IntegerLiteral(1)),
      ElementOfSet(x, FiniteSet(Seq(IntegerLiteral(1)), IntegerType())),
    )))
    assert(script.contains("intersection") && script.contains("setminus"))
  }

  test("Re-printing negated quantifiers and generic functions") {
    val tp = TypeParameter.fresh("T")
    val p = ValDef.fresh("p", tp)
    val idFd = new FunDef(FreshIdentifier("id"), Seq(TypeParameterDef(tp)), Seq(p), tp, p.toVariable, Seq())
    val program = InoxProgram(NoSymbols.withFunctions(Seq(idFd)))
    val y = ValDef.fresh("y", IntegerType())
    val (script, _) = roundTrip(program, And(Seq(
      Not(Forall(Seq(y), GreaterThan(y.toVariable, x))),
      Not(Forall(Seq(y), Not(Equals(FunctionInvocation(idFd.id, Seq(IntegerType()), Seq(y.toVariable)), x)))),
    )))
    assert(script.contains("exists") && script.contains("par"))
  }
}
