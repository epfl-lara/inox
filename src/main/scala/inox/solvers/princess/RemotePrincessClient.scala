/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package princess

import java.io.{BufferedInputStream, BufferedOutputStream, DataInputStream, DataOutputStream}
import java.net.{ServerSocket, Socket}

import utils._
import SolverResponses._
import RemoteProtocol._

/** Parent-side proxy that plays the role `AbstractPrincessSolver` normally
  * plays inside `PrincessSolver` -- i.e. it is the `underlying: AbstractSolver`
  * slot of a `RemotePrincessSolver` -- except every operation is a blocking
  * RPC to a child JVM (spawned by [[RemotePrincessClient.spawn]]) that hosts
  * the real, unmodified `AbstractPrincessSolver`.
  *
  * `Trees`/`Model` are opaque `Long` handles minted by the child: the
  * underlying Princess `IExpression`/`ap.api.PartialModel` values never
  * leave that process.
  */
class RemotePrincessClient private[princess] (
  override val program: Program { val trees: inox.trees.type },
  override val context: Context,
  private[princess] val process: Process,
  controlSocket: Socket,
  interruptSocket: Socket
) extends AbstractSolver {
  import program.trees._

  val name = "Princess-proc"

  type Trees = Long
  type Model = Long

  private val serializer = RemoteProtocol.inoxTreesSerializer()
  import serializer.{given, _}

  private val out = new DataOutputStream(new BufferedOutputStream(controlSocket.getOutputStream))
  private val in = new DataInputStream(new BufferedInputStream(controlSocket.getInputStream))
  private val interruptOut = new DataOutputStream(new BufferedOutputStream(interruptSocket.getOutputStream))

  private val lock = new Object

  private def rawResponseFor(r: WireCheckResult): SolverResponse[Long, Set[Long]] = r match {
    case WSat => Sat
    case WUnsat => Unsat
    case WUnknown => Unknown
    case WSatWithModel(h) => SatWithModel(h)
    case WUnsatWithAssumptions => UnsatWithAssumptions(Set.empty)
  }

  def declareVariable(v: Variable): Trees = lock.synchronized {
    out.writeByte(ReqDeclareVariable)
    serializer.serialize(v, out)
    out.flush()
    val h = in.readLong()
    readEnd(in)
    h
  }

  def freshSymbol(v: Variable): Trees = lock.synchronized {
    out.writeByte(ReqFreshSymbol)
    serializer.serialize(v, out)
    out.flush()
    val h = in.readLong()
    readEnd(in)
    h
  }

  def encode(e: Expr, bindings: Map[Variable, Trees]): Trees = lock.synchronized {
    out.writeByte(ReqEncode)
    serializer.serialize(e, out)
    serializer.serialize(bindings, out)
    out.flush()
    val h = in.readLong()
    readEnd(in)
    h
  }

  def assertCnstr(formula: Trees): Unit = lock.synchronized {
    out.writeByte(ReqAssertCnstr)
    out.writeLong(formula)
    out.flush()
    readEnd(in)
  }

  def check(config: CheckConfiguration): config.Response[Model, Assumptions] = lock.synchronized {
    out.writeByte(ReqCheck)
    writeConfig(config, out)
    out.flush()
    val res = readCheckResult(in)
    readEnd(in)
    config.cast(rawResponseFor(res))
  }

  def checkAssumptions(config: Configuration)(assumptions: Set[Trees]): config.Response[Model, Assumptions] = lock.synchronized {
    out.writeByte(ReqCheckAssumptions)
    writeConfig(config, out)
    serializer.serialize(assumptions.toSeq, out)
    out.flush()
    val res = readCheckResult(in)
    readEnd(in)
    config.cast(rawResponseFor(res))
  }

  def push(): Unit = lock.synchronized {
    out.writeByte(ReqPush)
    out.flush()
    readEnd(in)
  }

  def pop(): Unit = lock.synchronized {
    out.writeByte(ReqPop)
    out.flush()
    readEnd(in)
  }

  def reset(): Unit = lock.synchronized {
    out.writeByte(ReqReset)
    out.flush()
    readEnd(in)
  }

  def free(): Unit = lock.synchronized {
    try {
      out.writeByte(ReqFree)
      out.flush()
      readEnd(in)
    } catch {
      case _: java.io.IOException => // child already gone -- nothing more to do
    } finally {
      try { controlSocket.close() } catch { case _: java.io.IOException => () }
      try { interruptSocket.close() } catch { case _: java.io.IOException => () }
      if (!process.waitFor(2, java.util.concurrent.TimeUnit.SECONDS)) {
        process.destroyForcibly()
      }
    }
  }

  // Non-blocking, safe to call from another thread while `check`/
  // `checkAssumptions` is in flight on the control socket -- delivered on
  // the dedicated interrupt socket so it can't be stuck behind a blocked
  // request/response exchange.
  def interrupt(): Unit = interruptOut.synchronized {
    try {
      interruptOut.writeByte(1)
      interruptOut.flush()
    } catch {
      case _: java.io.IOException => // child already gone -- nothing to interrupt
    }
  }

  // Pure, local-in-the-embedded-solver IExpression combinators, relocated
  // here as RPCs since `Trees = Long` is opaque -- only the child holds the
  // real `IExpression` values these operate on.

  def mkNot(e: Trees): Trees = lock.synchronized {
    out.writeByte(ReqMkNot)
    out.writeLong(e)
    out.flush()
    val h = in.readLong()
    readEnd(in)
    h
  }

  def mkAnd(es: Seq[Trees]): Trees = lock.synchronized {
    out.writeByte(ReqMkAnd)
    serializer.serialize(es, out)
    out.flush()
    val h = in.readLong()
    readEnd(in)
    h
  }

  def mkOr(es: Seq[Trees]): Trees = lock.synchronized {
    out.writeByte(ReqMkOr)
    serializer.serialize(es, out)
    out.flush()
    val h = in.readLong()
    readEnd(in)
    h
  }

  def mkImplies(e1: Trees, e2: Trees): Trees = lock.synchronized {
    out.writeByte(ReqMkImplies)
    out.writeLong(e1)
    out.writeLong(e2)
    out.flush()
    val h = in.readLong()
    readEnd(in)
    h
  }

  def mkEquals(e1: Trees, e2: Trees): Trees = lock.synchronized {
    out.writeByte(ReqMkEquals)
    out.writeLong(e1)
    out.writeLong(e2)
    out.flush()
    val h = in.readLong()
    readEnd(in)
    h
  }

  def extractNot(e: Trees): Option[Trees] = lock.synchronized {
    out.writeByte(ReqExtractNot)
    out.writeLong(e)
    out.flush()
    val has = in.readBoolean()
    val res = if (has) Some(in.readLong()) else None
    readEnd(in)
    res
  }

  def mkSubstituter(substMap: Map[Trees, Trees]): Trees = lock.synchronized {
    out.writeByte(ReqMkSubstituter)
    serializer.serialize(substMap, out)
    out.flush()
    val h = in.readLong()
    readEnd(in)
    h
  }

  def applySubstituter(substHandle: Trees, e: Trees): Trees = lock.synchronized {
    out.writeByte(ReqApplySubstituter)
    out.writeLong(substHandle)
    out.writeLong(e)
    out.flush()
    val h = in.readLong()
    readEnd(in)
    h
  }

  def asString(e: Trees): String = lock.synchronized {
    out.writeByte(ReqAsString)
    out.writeLong(e)
    out.flush()
    val s = serializer.deserialize[String](in)
    readEnd(in)
    s
  }

  def decodeGround(h: Trees, tpe: Type): Option[Expr] = lock.synchronized {
    out.writeByte(ReqDecodeGround)
    out.writeLong(h)
    serializer.serialize(tpe, out)
    out.flush()
    val res = serializer.deserialize[Option[Expr]](in)
    readEnd(in)
    res
  }

  def modelEval(model: Model, h: Trees, tpe: Type): (Option[Expr], Map[Choose, Lambda]) = lock.synchronized {
    out.writeByte(ReqModelEval)
    out.writeLong(model)
    out.writeLong(h)
    serializer.serialize(tpe, out)
    out.flush()
    val res = serializer.deserialize[(Option[Expr], Map[Choose, Lambda])](in)
    readEnd(in)
    res
  }

  def extractConstructor(model: Model, h: Trees, tpe: ADTType): Option[Identifier] = lock.synchronized {
    out.writeByte(ReqExtractConstructor)
    out.writeLong(model)
    out.writeLong(h)
    serializer.serialize(tpe, out)
    out.flush()
    val res = serializer.deserialize[Option[Identifier]](in)
    readEnd(in)
    res
  }
}

object RemotePrincessClient {

  /** `java.class.path` is only reliable when this JVM was itself started
    * via a plain `java -cp ...` invocation -- true for the real `stainless`/
    * `inox` CLI (and for sbt's `run`, which is forked for exactly this
    * reason: `run / Keys.fork := true`) and, since `ItTest / fork := true`
    * was added for this backend, for the integration test suite too.
    *
    * (An earlier version of this also walked the classloader chain for
    * `URLClassLoader` entries to paper over non-forked JVMs -- that instead
    * pulled in an unrelated, binary-incompatible `scala-library` from the
    * host tool's own classloader and made things worse. Forking the JVM
    * that needs this, rather than trying to reconstruct its classpath
    * after the fact, is the correct fix.)
    */
  private def computeClasspath(): String = System.getProperty("java.class.path")

  /** Spawns a child JVM running [[PrincessWorkerMain]] (same jar, same
    * classpath as the running process -- no separate princess-jar
    * discovery needed), hands it `targetProgram`'s symbols, and returns a
    * ready-to-use client proxying to it.
    */
  def spawn(targetProgram: Program { val trees: inox.trees.type }, context: Context):
    RemotePrincessClient { val program: targetProgram.type } = {

    val controlServer = new ServerSocket(0)
    val interruptServer = new ServerSocket(0)

    try {
      val javaBin = System.getProperty("java.home") + java.io.File.separator + "bin" + java.io.File.separator + "java"
      val classpath = computeClasspath()

      val pb = new ProcessBuilder(
        javaBin, "-cp", classpath,
        "inox.solvers.princess.PrincessWorkerMain",
        controlServer.getLocalPort.toString,
        interruptServer.getLocalPort.toString
      )
      pb.redirectOutput(ProcessBuilder.Redirect.INHERIT)
      pb.redirectError(ProcessBuilder.Redirect.INHERIT)
      val process = pb.start()

      // `java.class.path` alone can be incomplete when the parent itself
      // isn't running from a plain `java -cp ...` invocation (e.g. under
      // sbt's non-forked test JVM, which loads dependencies through its own
      // classloaders) -- if the child can't find its classes it dies
      // immediately without ever connecting, so bound the wait instead of
      // blocking forever with no diagnostic.
      controlServer.setSoTimeout(30000)
      interruptServer.setSoTimeout(30000)
      val controlSocket =
        try controlServer.accept()
        catch {
          case _: java.net.SocketTimeoutException =>
            val alive = process.isAlive
            if (alive) process.destroyForcibly()
            throw FatalError(
              "princess-proc: child JVM did not connect within 30s " +
              s"(process ${if (alive) "still running -- destroyed" else s"exited with code ${process.exitValue()}"}). " +
              "This usually means `java.class.path` didn't include everything needed to load " +
              "inox.solvers.princess.PrincessWorkerMain in the parent's runtime environment " +
              "(known to happen under sbt's non-forked test JVMs)."
            )
        }
      val interruptSocket = interruptServer.accept()
      controlSocket.setSoTimeout(0)
      interruptSocket.setSoTimeout(0)

      val out = new DataOutputStream(new BufferedOutputStream(controlSocket.getOutputStream))
      val serializer = RemoteProtocol.inoxTreesSerializer()
      import serializer.{given, _}

      // Handshake: send the target program's symbols so the child can
      // build the same `targetProgram` locally, mirroring the
      // `symbolsProcedure` mapping already used for VC-cache serialization
      // (inox.utils.Serialization: Symbols <-> (Seq[FunDef], Seq[ADTSort])).
      val syms = targetProgram.symbols
      serializer.serialize(syms.functions.values.toSeq, out)
      serializer.serialize(syms.sorts.values.toSeq, out)
      out.flush()

      class Impl(override val program: targetProgram.type)
        extends RemotePrincessClient(program, context, process, controlSocket, interruptSocket)
      new Impl(targetProgram)
    } finally {
      controlServer.close()
      interruptServer.close()
    }
  }
}
