/* Copyright 2009-2016 EPFL, Lausanne */

package inox

import solvers._

trait MainHelpers {

  protected def getDebugSections: Set[DebugSection] = Set(
    ast.DebugSectionTrees,
    solvers.DebugSectionSolver
  )

  protected final lazy val debugSections = getDebugSections

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

  final object optHelp extends FlagOptionDef("help", false)

  abstract class Category
  case object General extends Category
  case object Solvers extends Category
  case object Evaluators extends Category
  case object Printing extends Category

  protected case class Description(category: Category, description: String)

  protected def getOptions: Map[OptionDef[_], Description] = Map(
    optHelp -> Description(General, "Show help message"),
    optTimeout -> Description(General, "Set a timeout for each proof attempt (in sec.)"),
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
    ast.optPrintPositions -> Description(Printing, "Attach positions to trees when printing"),
    ast.optPrintUniqueIds -> Description(Printing, "Always print unique ids"),
    ast.optPrintTypes -> Description(Printing, "Attach types to trees when printing"),
    solvers.optCheckModels -> Description(Solvers, "Double-check counter-examples with evaluator"),
    solvers.optSilentErrors -> Description(Solvers, "Fail silently into UNKNOWN when encountering an error"),
    solvers.unrolling.optUnrollFactor -> Description(Solvers, "Number of unrollings to perform in each unfold step"),
    solvers.unrolling.optFeelingLucky -> Description(Solvers, "Use evaluator to find counter-examples early"),
    solvers.unrolling.optUnrollAssumptions -> Description(Solvers, "Use unsat-assumptions to drive unfolding while remaining fair"),
    solvers.unrolling.optNoSimplifications -> Description(Solvers, "Disable selector/quantifier simplifications in solvers"),
    solvers.unrolling.optModelFinding -> Description(Solvers, "Enhance model-finding capabilities of solvers by given aggresivity"),
    solvers.smtlib.optCVC4Options -> Description(Solvers, "Pass extra options to CVC4"),
    evaluators.optMaxCalls -> Description(Evaluators, "Maximum function invocations allowed during evaluation (-1 for unbounded)"),
    evaluators.optIgnoreContracts -> Description(Evaluators, "Don't fail on invalid contracts during evaluation")
  )

  protected final lazy val options = getOptions

  protected def getCategories: Seq[Category] = {
    General +: (options.map(_._2.category).toSet - General).toSeq.sortBy(_.toString)
  }

  protected def displayHelp(reporter: Reporter, error: Boolean) = {
    val categories = getCategories

    for {
      category <- categories
      opts = options.filter(_._2.category == category)
      if opts.nonEmpty
    } {
      reporter.info("")
      reporter.title(category)
      for ((opt, Description(_, desc)) <- opts) {
        reporter.info(f"${opt.usageDesc}%-28s" + desc.replaceAll("\n", "\n" + " " * 28))
      }
    }

    exit(error)
  }

  protected def displayVersion(reporter: Reporter) = {
    reporter.title("Inox solver (https://github.com/epfl-lara/inox)")
    // XXX @nv: Just ignore this... no clean way to do it :(
    // reporter.info(s"Version: $version")
  }

  /** The current files on which Inox is running.
    *
    * This option cannot be filled through option parsing and must always be
    * instantiated manually (see [[processOptions]]). We therefore MUST NOT add
    * it to the [[options]] map!
    */
  final object optFiles extends OptionDef[Seq[java.io.File]] {
    val name = "files"
    val default = Seq[java.io.File]()
    val usageRhs = "No possible usage"
    val parser = { (_: String) => throw FatalError("Unparsable option \"files\"") }
  }

  protected def processOptions(args: Seq[String]): Context = {
    val initReporter = new DefaultReporter(Set())

    val opts = args.filter(_.startsWith("--"))

    val files = args.filterNot(_.startsWith("-")).map(new java.io.File(_))

    val inoxOptions: Seq[OptionValue[_]] = opts.map { opt =>
      val (name, value) = OptionsHelpers.nameValue(opt) getOrElse initReporter.fatalError(
        s"Malformed option $opt. Options should have the form --name or --name=value"
      )

      // find respective OptionDef, or report an error
      val df = options.keys.find(_.name == name) getOrElse initReporter.fatalError(
        s"Unknown option: $name\nTry the --help option for more information."
      )

      df.parse(value)(initReporter)
    }

    val reporter = new DefaultReporter(
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
    val ctx = try {
      processOptions(args.toList)
    } catch {
      case FatalError(msg) =>
        exit(error = true)
    }

    if (ctx.options.findOptionOrDefault(optHelp)) {
      displayVersion(ctx.reporter)
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
      ctx.reporter.fatalError(s"Input file was not specified.\nTry the --help option for more information.")
    } else {
      var error: Boolean = false
      for (file <- files;
           (syms, expr) <- new tip.Parser(file).parseScript) {
        val program = InoxProgram(ctx, syms)
        import program._
        import program.ctx._

        val sf = program.ctx.options.findOption(optTimeout) match {
          case Some(to) => SolverFactory.default(program).withTimeout(to)
          case None => SolverFactory.default(program)
        }

        import SolverResponses._
        SimpleSolverAPI(sf).solveSAT(expr) match {
          case SatWithModel(model) =>
            reporter.info(" => SAT")
            if (model.isEmpty) {
              reporter.info("  (Empty model)")
            } else {
              val max = model.keys.map(_.asString.length).max
              for ((vd, res) <- model) {
                reporter.info("  %-" + max + "s -> %s".format(vd.asString, res.asString))
              }
            }
          case Unsat =>
            reporter.info(" => UNSAT")
          case Unknown =>
            reporter.info(" => UNKNOWN")
            error = true
        }
      }

      ctx.reporter.whenDebug(utils.DebugSectionTimers) { debug =>
        ctx.timers.outputTable(debug)
      }

      exit(error = error)
    }
  }
}
