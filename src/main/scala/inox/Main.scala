/* Copyright 2009-2018 EPFL, Lausanne */

package inox

import solvers._

import java.io.File

trait MainHelpers {

  protected def getDebugSections: Set[DebugSection] = Set(
    utils.DebugSectionTimers,
    solvers.DebugSectionSolver,
    solvers.smtlib.DebugSectionSMT,
    tip.DebugSectionTip
  )

  protected final val debugSections = getDebugSections

  object optDebug extends OptionDef[Set[DebugSection]] {
    import OptionParsers._
    val name = "debug"
    val default = Set[DebugSection]()
    val usageRhs = "d1,d2,..."

    private val debugParser: OptionParser[Set[DebugSection]] = s => {
      if (s == "all") Some(debugSections)
      else debugSections.find(_.name == s).map(Set(_))
    }

    val parser: String => Option[Set[DebugSection]] = {
      setParser[Set[DebugSection]](debugParser)(_).map(_.flatten)
    }
  }

  object optHelp extends MarkerOptionDef("help")
  object optPrintProgram extends FlagOptionDef("print-program", false)

  abstract class Format
  case object Tip extends Format
  case class Binary(methodName: Option[String]) extends Format

  object optFormat extends OptionDef[Format] {
    val name: String = "format"
    val usageRhs: String = "tip|binary[:<method-name>]"
    val default: Format = Tip

    private val BinaryRegex = """binary:?(.+)?""".r

    override def parser: OptionParsers.OptionParser[Format] = s => s.toLowerCase match {
      case "tip" => Some(Tip)
      // Option.apply takes care of potential null in regex match
      case BinaryRegex(methodName) => Some(Binary(Option(methodName)))
      case _ => None
    }
  }

  abstract class Category
  case object General extends Category
  case object Solvers extends Category
  case object Evaluators extends Category
  case object Printing extends Category

  protected case class Description(category: Category, description: String)

  protected def getOptions: Map[OptionDef[_], Description] = Map(
    optHelp -> Description(General, "Show help message"),
    optNoColors -> Description(General, "Disable colored output and non-ascii characters (enable this option for better support in IDEs)"),
    optTimeout -> Description(General, "Set a timeout for the solver (in sec.)"),
    optSelectedSolvers -> Description(General, {
      "Use solvers s1,s2,...\nAvailable: " +
      solvers.SolverFactory.solverNames.toSeq.sortBy(_._1).map {
        case (name, desc) =>
          // f interpolator does not process escape sequence, we workaround that with the following trick.
          // See https://github.com/lampepfl/dotty/issues/11750
          val nl = '\n'
          f"$nl  $name%-14s : $desc"
      }.mkString("") +
      "\nYou can prefix the solvers unrollz3, smt-z3, smt-z3:<exec> and smt-cvc4, with 'no-inc:' to use them in non-incremental mode"
    }),
    optDebug -> Description(General, {
      val sects = debugSections.toSeq.map(_.name).sorted
      val (first, second) = sects.splitAt(sects.length/2 + 1)
      "Enable detailed messages per component.\nAvailable:\n" +
        "  " + first.mkString(", ") + ",\n" +
        "  " + second.mkString(", ")
    }),
    optFormat -> Description(General, "Choose input format (if 'binary' also choose method to use as expression)"),
    optPrintProgram -> Description(Printing, "Print the entire program"),
    optPrintChooses -> Description(Printing, "Display partial models for chooses when printing models"),
    ast.optPrintPositions -> Description(Printing, "Attach positions to trees when printing"),
    ast.optPrintUniqueIds -> Description(Printing, "Always print unique ids"),
    ast.optPrintTypes -> Description(Printing, "Attach types to trees when printing"),
    ast.optPrintUnicode -> Description(Printing, "Print unicode characters for mathematical symbols instead of their ASCII variant"),
    solvers.optAssumeChecked -> Description(Solvers, "Assume that all impure expression have been checked"),
    solvers.optNoSimplifications -> Description(Solvers, "Disable selector/quantifier simplifications in solvers"),
    solvers.optCheckModels -> Description(Solvers, "Double-check counter-examples with evaluator"),
    solvers.optSilentErrors -> Description(Solvers, "Fail silently into UNKNOWN when encountering an error"),
    solvers.unrolling.optUnrollBound -> Description(Solvers, "Maximum number of unroll steps to perform"),
    solvers.unrolling.optUnrollFactor -> Description(Solvers, "Number of unrollings to perform between each interaction with the SMT solver"),
    solvers.unrolling.optFeelingLucky -> Description(Solvers, "Use evaluator to find counter-examples early"),
    solvers.unrolling.optUnrollAssumptions -> Description(Solvers, "Use unsat-assumptions to drive unfolding while remaining fair"),
    solvers.unrolling.optModelFinding -> Description(Solvers, "Enhance model-finding capabilities of solvers by given aggressivity"),
    solvers.smtlib.optCVC4Options -> Description(Solvers, "Pass extra options to CVC4"),
    evaluators.optMaxCalls -> Description(Evaluators, "Maximum function invocations allowed during evaluation"),
    evaluators.optIgnoreContracts -> Description(Evaluators, "Don't fail on invalid contracts during evaluation")
  )

  final val options = getOptions

  protected def getCategories: Seq[Category] = {
    General +: (options.map(_._2.category).toSet - General).toSeq.sortBy(_.toString)
  }

  protected def displayVersion(reporter: Reporter) = {
    reporter.title("Inox solver (https://github.com/epfl-lara/inox)")
    reporter.info(s"Version: ${Build.version}")
  }

  protected def getName: String = "inox"

  protected def displayUsage(reporter: Reporter) = {
    reporter.info("Usage: " +
      Console.BOLD + getName + Console.RESET +
      " [" + Console.UNDERLINED + "OPTION" + Console.RESET + "]... " +
      Console.UNDERLINED + "FILE" + Console.RESET + "..."
    )
  }

  protected def displayHelp(reporter: Reporter, error: Boolean) = {
    val categories = getCategories
    val margin = options.map(_._1.usageDesc.size).max + 2
    var first = true

    for {
      category <- categories
      opts = options.filter(_._2.category == category)
      if opts.nonEmpty
    } {
      if (!first) reporter.info("")
      first = false

      reporter.title(category)
      for ((opt, Description(_, description)) <- opts.toSeq.sortBy(_._1.name)) {
        val default = if (opt.formatDefault.isEmpty) "" else s" (default: ${opt.formatDefault})"
        val desc = if (description.contains('\n')) {
          val first :: rest = description.split('\n').toList: @unchecked
          ((first ++ default) :: rest).mkString("\n")
        } else description ++ default
        val paddedDesc = desc.replaceAll("\n", "\n" + " " * margin)
        reporter.info(s"%-${margin}s".format(opt.usageDesc) ++ paddedDesc)
      }
    }

    exit(error)
  }

  /** The current files on which Inox is running.
    *
    * This option cannot be filled through option parsing and must always be
    * instantiated manually (see [[parseArguments]]). We therefore MUST NOT add
    * it to the [[options]] map!
    */
  object optFiles extends OptionDef[Seq[File]] {
    val name = "files"
    val default = Seq[File]()
    val usageRhs = "No possible usage"
    val parser = { (_: String) => throw FatalError("Unparsable option \"files\"") }
  }

  protected def newReporter(debugSections: Set[DebugSection]): inox.Reporter =
    new DefaultReporter(debugSections)

  protected def parseArguments(args: Seq[String])(using initReporter: Reporter): Context = {
    val opts = args.filter(_.startsWith("--"))

    val files = args.filterNot(_.startsWith("-")).map(new File(_))

    val inoxOptions: Seq[OptionValue[_]] = opts.map { opt =>
      val (name, value) = OptionsHelpers.nameValue(opt) getOrElse initReporter.fatalError(
        s"Malformed option $opt. Options should have the form --name or --name=value"
      )

      // find respective OptionDef, or report an error
      val df = options.keys.find(_.name == name) getOrElse initReporter.fatalError(
        s"Unknown option: $name\nTry the --help option for more information."
      )

      df.parse(value)
    }

    processOptions(files, inoxOptions)
  }

  protected def processOptions(files: Seq[File], inoxOptions: Seq[OptionValue[_]])
                              (using initReporter: Reporter): Context = {

    for ((optDef, values) <- inoxOptions.groupBy(_.optionDef) if values.size > 1)
      initReporter.fatalError(s"Duplicate option: ${optDef.name}")

    val reporter = newReporter(
      inoxOptions.collectFirst {
        case OptionValue(`optDebug`, sections) => sections.asInstanceOf[Set[DebugSection]]
      }.getOrElse(Set[DebugSection]())
    )

    reporter.whenDebug(DebugSectionOptions) { debug =>
      debug("Options considered:")
      for (io <- inoxOptions) debug(io.toString)
    }

    Context(
      reporter = reporter,
      options = Options(inoxOptions :+ optFiles(files)),
      interruptManager = new utils.InterruptManager(reporter)
    )
  }

  def exit(error: Boolean) = sys.exit(if (error) 1 else 0)

  def getFilesOrExit(ctx: Context): Seq[File] = {
    val files = ctx.options.findOptionOrDefault(optFiles)
    if (files.isEmpty) {
      ctx.reporter.error(s"Input file was not specified.\nTry the --help option for more information.")
      exit(error = true)
    }
    files
  }

  def setup(args: Array[String]): Context = {
    val initReporter = newReporter(Set())

    val ctx = try {
      parseArguments(args.toList)(using initReporter)
    } catch {
      case FatalError(msg) =>
        exit(error = true)
    }

    if (ctx.options.findOptionOrDefault(optHelp)) {
      displayVersion(ctx.reporter)
      ctx.reporter.info("")
      displayUsage(ctx.reporter)
      ctx.reporter.info("")
      displayHelp(ctx.reporter, error = false)
    } else {
      ctx.interruptManager.registerSignalHandler()
      ctx
    }
  }
}

object Main extends MainHelpers {
  import inox.trees._

  def main(args: Array[String]): Unit = {
    val ctx = setup(args)
    var error: Boolean = false

    for {
      file <- getFilesOrExit(ctx)
      (program, exprOpt) <- parse(ctx, file)
    } {
      import ctx.{given, _}
      import program._

      if (ctx.options.findOptionOrDefault(optPrintProgram)) {
        ctx.reporter.info(s"Program in $file:\n\n")
        ctx.reporter.info(program.asString)
      }

      exprOpt.foreach { expr =>
        val sf = ctx.options.findOption(optTimeout) match {
          case Some(to) => program.getSolver.withTimeout(to)
          case None => program.getSolver
        }

        import SolverResponses._
        SimpleSolverAPI(sf).solveSAT(expr) match {
          case SatWithModel(model) =>
            reporter.info(s"$file => SAT")
            reporter.info("  " + model.asString.replaceAll("\n", "\n  "))
          case Unsat =>
            reporter.info(s"$file => UNSAT")
          case Unknown =>
            reporter.info(s"$file => UNKNOWN")
            error = true
        }
      }
    }

    val asciiOnly = ctx.options.findOptionOrDefault(optNoColors)
    ctx.reporter.whenDebug(utils.DebugSectionTimers) { debug =>
      ctx.timers.outputTable(debug, asciiOnly)
    }

    exit(error)
  }

  protected def parse(ctx: Context, file: File): Seq[(InoxProgram, Option[Expr])] =
    ctx.options.findOptionOrDefault(optFormat) match {
      case Tip =>
        tip.Parser(file).parseScript.map{ case (p, e) => (p, Some(e)) }

      case Binary(None) =>
        Seq((InoxProgram(deserializeSymbols(ctx, file)), None))

      case Binary(Some(methodName)) =>
        val symbols = deserializeSymbols(ctx, file)
        Seq(
          (
            InoxProgram(symbols),
            symbols.functions.find(_._1.name == methodName).map(_._2.fullBody)
          )
        )

    }

  private def deserializeSymbols(ctx: Context, file: File): Symbols = {
    import java.io._
    try {
      val serializer = utils.Serializer(inox.trees)
      val in = new FileInputStream(file)
      serializer.deserialize[Symbols](in)
    } catch {
      case _: FileNotFoundException =>
        ctx.reporter.error(s"Input file was not found:\n  $file")
        exit(error = true)
      case _: IOException =>
        ctx.reporter.error(s"Error reading from file:\n  $file")
        exit(error = true)
    }
  }
}
