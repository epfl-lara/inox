package inox.solvers.smtlib

import _root_.smtlib.trees.Terms.*
import _root_.smtlib.printer.Printer
import _root_.smtlib.parser.Parser
import _root_.smtlib.Interpreter
import _root_.smtlib.theories.*
import java.io.BufferedReader
import _root_.smtlib.trees.CommandsResponses.*
import _root_.smtlib.trees.Commands.*
import java.io.StringReader
import java.util.concurrent.Future

/**
  * 
  *
  * @param printer
  * @param parser
  */
class EldaricaInterpreter(val printer: Printer, val parserCtor: BufferedReader => Parser) extends Interpreter {

  import collection.mutable.{Stack => MStack, Seq => MSeq}

  private val commands = MStack(MSeq.empty[SExpr])

  private var lastModelResponse: Option[GetModelResponse] = None

  val parser = parserCtor(new BufferedReader(new StringReader(""))) // dummy parser

  private class InterruptibleExecutor[T]:
    private var task: Option[Future[T]] = None

    private val executor = scala.concurrent.ExecutionContext.fromExecutorService(null)

    private def asCallable[A](block: => A): java.util.concurrent.Callable[A] = 
        new java.util.concurrent.Callable[A] { def call(): A = block }

    def execute(block: => T): Option[T] = 
        this.synchronized: // run only one task at a time
          task = Some(executor.submit(asCallable(block)))
  
          val res = 
            try
              Some(task.get.get()) // block for result or interrupt
            catch
              case e: java.util.concurrent.CancellationException => None // externally interrupted
              case e: Exception => throw e
  
          task = None
          res

    def interrupt(): Unit = 
        task.foreach(_.cancel(true))

  private val executor = new InterruptibleExecutor[SExpr]

  /**
    * args to run Eldarica calls under
    */
  private val eldArgs = Array(
    "-in",      // read input from (simulated) stdin 
    "-hsmt",    // use SMT-LIB2 input format
    "-disj"     // use disjunctive interpolation
  )

  def eval(cmd: SExpr): SExpr =
    cmd match
      case CheckSat() =>
        checkSat
      case CheckSatAssuming(assumptions) =>
        def toAssertion(lit: PropLiteral): SExpr = 
            val PropLiteral(sym, polarity) = lit
            val id = QualifiedIdentifier(SimpleIdentifier(sym), Some(Core.BoolSort()))
            val term = if polarity then id else Core.Not(id)
            Assert(term)

        commands.push(assumptions.map(toAssertion).to(MSeq))
        val res = checkSat
        commands.pop()
        res
      case Echo(value) =>
        EchoResponseSuccess(value.toString)
      case Exit() =>
        // equivalent to reset
        commands.clear()
        trySuccess
      case GetInfo(flag) =>
        flag match
          case VersionInfoFlag() =>
            GetInfoResponseSuccess(VersionInfoResponse("0.1"), Seq.empty)
          case _ => Unsupported
      case GetModel() =>
        getModel
      case Pop(n) =>
        (1 to n).foreach(_ => commands.pop())
        trySuccess
      case Push(n) =>
        (1 to n).foreach(_ => commands.push(MSeq()))
        trySuccess
      case Reset() =>
        commands.clear()
        trySuccess
      case SetOption(option) =>
        // slightly haphazard
        // but we always expect that PrintSuccess(true) has been passed as the first command
        trySuccess
      case _ =>
        commands.push(commands.pop() :+ cmd)
        trySuccess

  //A free method is kind of justified by the need for the IO streams to be closed, and
  //there seems to be a decent case in general to have such a method for things like solvers
  //note that free can be used even if the solver is currently solving, and act as a sort of interrupt
  def free(): Unit =
    commands.clear()

  def interrupt(): Unit = 
    executor.interrupt()

  private def trySuccess: SExpr = Success

  private def collapsedCommands = commands.toSeq.flatten

  private def checkSat: SExpr = 
    this.synchronized { 
        // reset last model
        setLastModelResponse(None)
        executor
          .execute(seqCheckSat)
          .getOrElse(CheckSatStatus(UnknownStatus))
    }

  private def seqCheckSat: SExpr =
    val commands = collapsedCommands :+ CheckSat()
    val script = commands.map(printer.toString).mkString("\n")

    val inputStream = new java.io.StringReader(script)

    val buffer = new java.io.ByteArrayOutputStream
    val printStream = new java.io.PrintStream(buffer)

    // actually check sat, requesting a model if possible
    Console.withIn(inputStream):
      Console.withOut(printStream):
        lazabs.Main.doMain(eldArgs, false)

    val eldRes = new java.io.BufferedReader(new java.io.StringReader(buffer.toString))

    val parser = parserCtor(eldRes)

    val result = parser.parseCheckSatResponse

    result match
        case CheckSatStatus(SatStatus) =>
        // FIXME: @sg: disabled due to non-SMTLIB compliant model printing from eldarica
        // there will be a parser exception if we attemp this
        //   // if Sat, parse and store model
        //   val model = parser.parseGetModelResponse
        //   // could be a model or an error, in either case, this is the response for (get-model)
        //   setLastModelResponse(Some(model))
            setLastModelResponse(Some(GetModelResponseSuccess(Nil))) // empty model
            result
        case _ =>
            // if unsat or unknown, reset the model
            setLastModelResponse(None)
            result

  private def setLastModelResponse(model: Option[GetModelResponse]): Unit =
    lastModelResponse = model

  private def getModel: SExpr = 
    lastModelResponse match
        case Some(modelResponse) =>
            modelResponse
        case None =>
            Error("No model available")
}
