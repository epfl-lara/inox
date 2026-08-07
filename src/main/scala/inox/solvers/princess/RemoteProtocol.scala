/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package princess

import java.io.{DataInputStream, DataOutputStream}

import utils.InoxSerializer

/** Wire protocol shared between [[RemotePrincessClient]] (parent JVM) and
  * [[PrincessWorkerMain]] (child JVM). Every AST-typed payload (`Expr`,
  * `Type`, `Identifier`, ...) is carried using the existing
  * `inox.utils.InoxSerializer` for `inox.trees` (the fixed target trees of
  * every solver backend, see `SolverFactory.getFromName`'s `enc` parameter
  * type). Handles to Princess-native objects that cannot leave the child
  * JVM (`IExpression` terms, `ap.api.PartialModel` instances) are
  * represented as opaque `Long`s minted by the child.
  */
private[princess] object RemoteProtocol {

  /** `new InoxSerializer(inox.trees)` alone widens `trees` to the abstract
    * `ast.Trees`, which then defeats given-instance resolution for
    * `Expr`/`Type`/... (the compiler can no longer see that `serializer.trees`
    * is `inox.trees`). Mirrors the same fix already used by the existing
    * `stainless.utils.Serializer.apply` factory (an explicit cast -- true by
    * construction, since the value handed in literally becomes that field).
    */
  def inoxTreesSerializer(): InoxSerializer { val trees: inox.trees.type } =
    new InoxSerializer(inox.trees).asInstanceOf[InoxSerializer { val trees: inox.trees.type }]

  // Requests, sent parent -> child on the control socket.
  final val ReqDeclareVariable: Byte = 1
  final val ReqFreshSymbol: Byte = 2
  final val ReqEncode: Byte = 3
  final val ReqAssertCnstr: Byte = 4
  final val ReqCheck: Byte = 5
  final val ReqCheckAssumptions: Byte = 6
  final val ReqPush: Byte = 7
  final val ReqPop: Byte = 8
  final val ReqReset: Byte = 9
  final val ReqFree: Byte = 10
  final val ReqDecodeGround: Byte = 11
  final val ReqModelEval: Byte = 12
  final val ReqExtractConstructor: Byte = 13

  // Local, pure IExpression combinators that `Templates` requires (used by
  // the unrolling engine to build blocking clauses etc.) -- these don't
  // touch the live `SimpleAPI` session at all in the embedded solver, but
  // since `Encoded` is an opaque handle here, only the child can perform
  // them (it alone holds the real `IExpression` values behind the handles).
  final val ReqMkNot: Byte = 14
  final val ReqMkAnd: Byte = 15
  final val ReqMkOr: Byte = 16
  final val ReqMkImplies: Byte = 17
  final val ReqMkEquals: Byte = 18
  final val ReqExtractNot: Byte = 19
  final val ReqMkSubstituter: Byte = 20
  final val ReqApplySubstituter: Byte = 21
  final val ReqAsString: Byte = 22

  // `SolverResponses.Configuration`, hand-encoded (not registered in the
  // shared `InoxSerializer` class table, to avoid touching that shared,
  // versioned id registry for a 4-way closed enum).
  final val ConfigSimple: Byte = 0
  final val ConfigModel: Byte = 1
  final val ConfigUnsatAssumptions: Byte = 2
  final val ConfigAll: Byte = 3

  def writeConfig(config: SolverResponses.Configuration, out: DataOutputStream): Unit = {
    import SolverResponses._
    out.writeByte(config match {
      case Simple => ConfigSimple
      case Model => ConfigModel
      case UnsatAssumptions => ConfigUnsatAssumptions
      case All => ConfigAll
    })
  }

  def readConfig(in: DataInputStream): SolverResponses.Configuration = {
    import SolverResponses._
    in.readByte() match {
      case ConfigSimple => Simple
      case ConfigModel => Model
      case ConfigUnsatAssumptions => UnsatAssumptions
      case ConfigAll => All
      case other => throw FatalError(s"Unknown wire configuration tag: $other")
    }
  }

  // Result of a Check/CheckAssumptions RPC, independent of the specific
  // `Configuration`'s dependent response type -- the caller (parent side)
  // reconstructs the proper `SolverResponse` via `config.cast(...)`.
  sealed trait WireCheckResult
  case object WSat extends WireCheckResult
  case object WUnsat extends WireCheckResult
  case object WUnknown extends WireCheckResult
  case class WSatWithModel(modelHandle: Long) extends WireCheckResult
  // Princess's own `checkAssumptions` always returns an empty unsat core
  // (see AbstractPrincessSolver.scala's `UnsatWithAssumptions(Set.empty)`),
  // so there is no assumption-handle payload to carry back.
  case object WUnsatWithAssumptions extends WireCheckResult

  final val RespSat: Byte = 0
  final val RespUnsat: Byte = 1
  final val RespUnknown: Byte = 2
  final val RespSatWithModel: Byte = 3
  final val RespUnsatWithAssumptions: Byte = 4

  def writeCheckResult(r: WireCheckResult, out: DataOutputStream): Unit = r match {
    case WSat => out.writeByte(RespSat)
    case WUnsat => out.writeByte(RespUnsat)
    case WUnknown => out.writeByte(RespUnknown)
    case WSatWithModel(h) => out.writeByte(RespSatWithModel); out.writeLong(h)
    case WUnsatWithAssumptions => out.writeByte(RespUnsatWithAssumptions)
  }

  def readCheckResult(in: DataInputStream): WireCheckResult = in.readByte() match {
    case RespSat => WSat
    case RespUnsat => WUnsat
    case RespUnknown => WUnknown
    case RespSatWithModel => WSatWithModel(in.readLong())
    case RespUnsatWithAssumptions => WUnsatWithAssumptions
    case other => throw FatalError(s"Unknown wire check-result tag: $other")
  }

  // A single byte written after every request's response payload is fully
  // written, used only to fail fast/clearly if the two ends' framing ever
  // desyncs (rather than silently misinterpreting bytes as an unrelated
  // message). Not a general framing mechanism -- see the note in
  // `RemotePrincessClient`/`PrincessWorkerMain` on why none is needed.
  final val EndOfMessage: Byte = 0x7e

  def writeEnd(out: DataOutputStream): Unit = out.writeByte(EndOfMessage)

  def readEnd(in: DataInputStream): Unit = {
    val b = in.readByte()
    if (b != EndOfMessage)
      throw FatalError(s"princess-proc protocol desync: expected end-of-message marker, got $b")
  }
}
