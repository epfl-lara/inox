/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package tip

import utils._
import solvers._

case object DebugSectionTip extends DebugSection("tip")

trait TipDebugger extends Solver {
  import program._
  import program.trees._
  import SolverResponses._

  protected val encoder: transformers.ProgramTransformer {
    val sourceProgram: program.type
    val targetProgram: Program { val trees: inox.trees.type }
  }

  abstract override def free(): Unit = {
    super.free()
    debugOut.foreach(_.free())
  }

  protected class DebugPrinter(program: InoxProgram, context: Context, writer: java.io.Writer)
    extends tip.Printer(program, context, writer) {

    import inox.trees._

    protected object checker extends ConcreteSelfTreeTraverser {
      override def traverse(tpe: Type): Unit = tpe match {
        case (_: PiType | _: SigmaType | _: RefinementType) =>
          unsupported(tpe, "Dependent types cannot be expressed in TIP")
        case _ => super.traverse(tpe)
      }
    }

    private[this] var reported: Boolean = false
    private[this] def tryCheck[T <: Tree](performCheck: => Unit): Boolean = try {
      performCheck
      true
    } catch {
      case u: Unsupported =>
        if (!reported) {
          context.reporter.warning(u.getMessage)
          reported = false
        }
        false
    }

    private val validSymbols = tryCheck {
      program.symbols.functions.values.foreach(checker.traverse)
      program.symbols.sorts.values.foreach(checker.traverse)
    }

    override def printScript(expr: Expr): Unit = {
      if (validSymbols && tryCheck(checker.traverse(expr))) {
        super.printScript(expr)
      }
    }
  }

  protected lazy val debugOut: Option[tip.Printer] = {
    given DebugSection = DebugSectionTip

    if (context.reporter.isDebugEnabled) {
      val files = context.options.findOptionOrDefault(Main.optFiles)
      if (files.nonEmpty && files.forall(_.getName.endsWith(".tip"))) {
        // don't output TIP when running on a TIP benchmark
        None
      } else {
        val file = files.headOption.map(_.getName).getOrElse("NA")
        val n = DebugFileNumbers.next(file)
        val fileName = s"tip-sessions/$file-$n.tip"

        val javaFile = new java.io.File(fileName)
        javaFile.getParentFile.mkdirs()

        context.reporter.debug(s"Outputting tip session into $fileName")
        val fw = new java.io.FileWriter(javaFile, false)
        Some(new DebugPrinter(encoder.targetProgram, context, fw))
      }
    } else {
      None
    }
  }

  abstract override def assertCnstr(expr: Expr): Unit = {
    debugOut.foreach(o => o.printScript(encoder.encode(expr)))
    super.assertCnstr(expr)
  }

  abstract override def check(config: CheckConfiguration): config.Response[Model, Assumptions] = {
    debugOut.foreach(o => o.emit(_root_.smtlib.trees.Commands.CheckSat()))
    super.check(config)
  }

  abstract override def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[Model, Assumptions] = {
    debugOut.foreach(o => o.emit("; check-assumptions required here, but not part of tip standard"))
    super.checkAssumptions(config)(assumptions)
  }
}

// Unique numbers
private[tip] object DebugFileNumbers extends UniqueCounter[String]
