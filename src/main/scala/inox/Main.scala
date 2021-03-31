/* Copyright 2009-2018 EPFL, Lausanne */

package inox

import solvers._

import java.io.File

trait MainHelpers {

  protected def getDebugSections: Set[DebugSection] = Set(
    utils.DebugSectionTimers,
    solvers.DebugSectionSolver,
    tip.DebugSectionTip
  )

  protected final val debugSections = getDebugSections

  final object optDebug extends OptionDef[Set[DebugSection]] {
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

  final object optHelp extends MarkerOptionDef("help")

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
        case (name, desc) => f"\n  $name%-14s : $desc"
      }.mkString("")
    }),
    optDebug -> Description(General, {
      val sects = debugSections.toSeq.map(_.name).sorted
      val (first, second) = sects.splitAt(sects.length/2 + 1)
      "Enable detailed messages per component.\nAvailable:\n" +
        "  " + first.mkString(", ") + ",\n" +
        "  " + second.mkString(", ")
    }),
    optPrintChooses -> Description(Printing, "Display partial models for chooses when printing models"),
    ast.optPrintPositions -> Description(Printing, "Attach positions to trees when printing"),
    ast.optPrintUniqueIds -> Description(Printing, "Always print unique ids"),
    ast.optPrintTypes -> Description(Printing, "Attach types to trees when printing"),
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
          val first :: rest = description.split('\n').toList
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
  final object optFiles extends OptionDef[Seq[File]] {
    val name = "files"
    val default = Seq[File]()
    val usageRhs = "No possible usage"
    val parser = { (_: String) => throw FatalError("Unparsable option \"files\"") }
  }

  protected def newReporter(debugSections: Set[DebugSection]): inox.Reporter =
    new DefaultReporter(debugSections)

  protected def parseArguments(args: Seq[String])(implicit initReporter: Reporter): Context = {
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
                              (implicit initReporter: Reporter): Context = {

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

  def setup(args: Array[String]): Context = {
    val initReporter = newReporter(Set())

    val ctx = try {
      parseArguments(args.toList)(initReporter)
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

  def main(args: Array[String]): Unit = {
    val ctx = setup(args)

    val files = ctx.options.findOptionOrDefault(optFiles)
    if (files.isEmpty) {
      ctx.reporter.error(s"Input file was not specified.\nTry the --help option for more information.")
      exit(error = true)
    } else {
      var error: Boolean = false
      for (file <- files; (program, expr) <- tip.Parser(file).parseScript) {
        import ctx._
        import program._

        val sf = ctx.options.findOption(optTimeout) match {
          case Some(to) => program.getSolver.withTimeout(to)
          case None => program.getSolver
        }

        import SolverResponses._
        SimpleSolverAPI(sf).solveSAT(expr) match {
          case SatWithModel(model) =>
            reporter.info(file + " => SAT")
            reporter.info("  " + model.asString.replaceAll("\n", "\n  "))
          case Unsat =>
            reporter.info(file + " => UNSAT")
          case Unknown =>
            reporter.info(file + " => UNKNOWN")
            error = true
        }
      }

      val asciiOnly = ctx.options.findOptionOrDefault(optNoColors)
      ctx.reporter.whenDebug(utils.DebugSectionTimers) { debug =>
        ctx.timers.outputTable(debug, asciiOnly)
      }

      exit(error = error)
    }
  }
}
