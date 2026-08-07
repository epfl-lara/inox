/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package princess

import java.io.{BufferedInputStream, BufferedOutputStream, DataInputStream, DataOutputStream}
import java.net.Socket

import ap.parser.{Context => _, _}
import ap.parser.IExpression.{given, _}

import utils._
import SolverResponses._
import RemoteProtocol._

/** Child-process entry point for the `princess-proc` solver backend.
  *
  * Connects back to the parent on the two ports given as arguments,
  * rebuilds `targetProgram` from the parent's `Symbols`, and hosts a real,
  * completely unmodified [[AbstractPrincessSolver]] instance, dispatching
  * every RPC from [[RemotePrincessClient]] directly onto it. Princess
  * `IExpression` terms and `ap.api.PartialModel` instances never leave this
  * process -- callers on the other end of the wire only ever see opaque
  * `Long` handles.
  */
object PrincessWorkerMain {

  private class RealPrincessSolver(override val program: InoxProgram, override val context: Context)
                                   (using theSemantics: program.Semantics)
    extends AbstractPrincessSolver(program, context)

  def main(args: Array[String]): Unit = {
    val controlPort = args(0).toInt
    val interruptPort = args(1).toInt

    val controlSocket = new Socket("localhost", controlPort)
    val interruptSocket = new Socket("localhost", interruptPort)

    val out = new DataOutputStream(new BufferedOutputStream(controlSocket.getOutputStream))
    val in = new DataInputStream(new BufferedInputStream(controlSocket.getInputStream))

    val serializer = RemoteProtocol.inoxTreesSerializer()
    import serializer.{given, _}
    import inox.trees._

    // Handshake: rebuild `targetProgram` from the parent's Symbols, mirroring
    // the `symbolsProcedure` mapping already used for VC-cache serialization.
    val functions = serializer.deserialize[Seq[FunDef]](in)
    val sorts = serializer.deserialize[Seq[ADTSort]](in)
    val targetProgram: InoxProgram = InoxProgram(functions, sorts)

    val context = Context.empty
    val theSemantics: targetProgram.Semantics = targetProgram.getSemantics(using inoxSemantics)
    val realSolver = new RealPrincessSolver(targetProgram, context)(using theSemantics)

    val exprHandles = scala.collection.mutable.HashMap.empty[Long, IExpression]
    // Reverse index so that re-deriving a *structurally identical* Princess
    // term (e.g. re-encoding the same sub-expression, or combining the same
    // already-encoded sub-formulas via mkAnd/mkOr/...) reuses the same
    // handle instead of minting a fresh one. This matters because
    // `Templates.scala`'s unrolling engine tracks fixpoint/dedup state in
    // `Map[Encoded, ...]`/`Set[Encoded]` structures, relying on `Encoded`
    // (here, our handles) behaving like the value type it wraps -- in the
    // embedded solver `Encoded = IExpression`, whose case-class equality is
    // already structural, so this reverse index restores that property for
    // opaque `Long` handles instead of one being minted per call.
    val exprHandlesRev = scala.collection.mutable.HashMap.empty[IExpression, Long]
    val modelHandles = scala.collection.mutable.HashMap.empty[Long, ap.api.PartialModel]
    // Substituters (from `mkSubstituter`/`ApplySubstituter`) are their own
    // kind of handle -- they don't refer to an `IExpression`, so they're
    // kept in a separate table rather than smuggled into `exprHandles`.
    val substHandles = scala.collection.mutable.HashMap.empty[Long, Map[IExpression, IExpression]]
    var exprCounter = 0L
    var modelCounter = 0L
    var substCounter = 0L

    def newExprHandle(e: IExpression): Long = exprHandlesRev.getOrElseUpdate(e, {
      val h = exprCounter
      exprCounter += 1
      exprHandles(h) = e
      h
    })

    def newModelHandle(m: ap.api.PartialModel): Long = {
      val h = modelCounter
      modelCounter += 1
      modelHandles(h) = m
      h
    }

    def newSubstHandle(m: Map[IExpression, IExpression]): Long = {
      val h = substCounter
      substCounter += 1
      substHandles(h) = m
      h
    }

    // Mirrors PrincessSolver.ModelWrapperImpl.extractConstructor verbatim --
    // relocated here since it needs the live `constructors`/`selectors`
    // bijections, which only make sense next to the real Princess objects.
    def extractConstructor(v: IExpression, model: ap.api.PartialModel): Option[Identifier] = {
      val optFun = realSolver.princessToInox.simplify(v)(model) match {
        case IFunApp(fun, _) if realSolver.constructors `containsB` fun => Some(fun)
        case it: ITerm => model.evalToTerm(it) match {
          case Some(IFunApp(fun, _)) => Some(fun)
          case _ => None
        }
        case _ => None
      }
      optFun.map(fun => realSolver.constructors.toA(fun).asInstanceOf[realSolver.ADTCons].id)
    }

    // Delivers `interrupt()` from a separate thread while the main loop may
    // be blocked inside `realSolver.check`/`checkAssumptions`'s poll loop --
    // `AbstractPrincessSolver.interrupt()` is a plain flag flip, safe to
    // call concurrently, exactly as it already is for in-process callers
    // (TimeoutSolver's Countdown thread, PortfolioSolver's loser-cancellation).
    val interruptListener = new Thread(() => {
      val iin = new DataInputStream(new BufferedInputStream(interruptSocket.getInputStream))
      try {
        while (true) {
          iin.readByte()
          realSolver.interrupt()
        }
      } catch {
        case _: java.io.IOException => // socket closed: nothing more to listen for
      }
    })
    interruptListener.setDaemon(true)
    interruptListener.start()

    def writeCheckResponse(resp: SolverResponse[ap.api.PartialModel, Set[IExpression]]): Unit = {
      val wire = resp match {
        case Sat => WSat
        case Unsat => WUnsat
        case Unknown => WUnknown
        case SatWithModel(m) => WSatWithModel(newModelHandle(m))
        case UnsatWithAssumptions(_) => WUnsatWithAssumptions
      }
      writeCheckResult(wire, out)
      writeEnd(out)
      out.flush()
    }

    var running = true
    while (running) {
      (in.readByte(): Byte) match {
        case ReqDeclareVariable =>
          val v = serializer.deserialize[Variable](in)
          val h = newExprHandle(realSolver.declareVariable(v))
          out.writeLong(h); writeEnd(out); out.flush()

        case ReqFreshSymbol =>
          val v = serializer.deserialize[Variable](in)
          val h = newExprHandle(realSolver.freshSymbol(v))
          out.writeLong(h); writeEnd(out); out.flush()

        case ReqEncode =>
          val e = serializer.deserialize[Expr](in)
          val bindingsRaw = serializer.deserialize[Map[Variable, Long]](in)
          val bindings = bindingsRaw.map { case (v, h) => v -> exprHandles(h) }
          val h = newExprHandle(realSolver.inoxToPrincess(e)(using bindings))
          out.writeLong(h); writeEnd(out); out.flush()

        case ReqAssertCnstr =>
          val h = in.readLong()
          realSolver.assertCnstr(exprHandles(h))
          writeEnd(out); out.flush()

        case ReqCheck =>
          val config = readConfig(in).asInstanceOf[SolverResponses.CheckConfiguration]
          writeCheckResponse(realSolver.check(config))

        case ReqCheckAssumptions =>
          val config = readConfig(in)
          val handles = serializer.deserialize[Seq[Long]](in)
          val assumptions = handles.map(exprHandles(_)).toSet
          writeCheckResponse(realSolver.checkAssumptions(config)(assumptions))

        case ReqPush =>
          realSolver.push(); writeEnd(out); out.flush()

        case ReqPop =>
          realSolver.pop(); writeEnd(out); out.flush()

        case ReqReset =>
          realSolver.reset(); writeEnd(out); out.flush()

        case ReqFree =>
          realSolver.free()
          writeEnd(out); out.flush()
          running = false

        case ReqMkNot =>
          val h = in.readLong()
          val res = newExprHandle(!(exprHandles(h).asInstanceOf[IFormula]))
          out.writeLong(res); writeEnd(out); out.flush()

        case ReqMkAnd =>
          val hs = serializer.deserialize[Seq[Long]](in)
          val es = hs.map(h => exprHandles(h).asInstanceOf[IFormula])
          val res = newExprHandle(es.tail.foldLeft(es.head)((p, q) => p & q))
          out.writeLong(res); writeEnd(out); out.flush()

        case ReqMkOr =>
          val hs = serializer.deserialize[Seq[Long]](in)
          val es = hs.map(h => exprHandles(h).asInstanceOf[IFormula])
          val res = newExprHandle(es.tail.foldLeft(es.head)((p, q) => p | q))
          out.writeLong(res); writeEnd(out); out.flush()

        case ReqMkImplies =>
          val h1 = in.readLong()
          val h2 = in.readLong()
          val e1 = exprHandles(h1).asInstanceOf[IFormula]
          val e2 = exprHandles(h2).asInstanceOf[IFormula]
          val res = newExprHandle(e1 ==> e2)
          out.writeLong(res); writeEnd(out); out.flush()

        case ReqMkEquals =>
          val h1 = in.readLong()
          val h2 = in.readLong()
          val res = newExprHandle((exprHandles(h1), exprHandles(h2)) match {
            case (f1: IFormula, f2: IFormula) => f1 <=> f2
            case (t1: ITerm, t2: ITerm) => t1 === t2
            case (e1, e2) => throw FatalError(s"Unhandled equality between $e1 and $e2")
          })
          out.writeLong(res); writeEnd(out); out.flush()

        case ReqExtractNot =>
          val h = in.readLong()
          exprHandles(h) match {
            case INot(e2) =>
              out.writeBoolean(true)
              out.writeLong(newExprHandle(e2))
            case _ =>
              out.writeBoolean(false)
          }
          writeEnd(out); out.flush()

        case ReqMkSubstituter =>
          val substMap = serializer.deserialize[Map[Long, Long]](in)
          val resolved = substMap.map { case (k, v) => exprHandles(k) -> exprHandles(v) }
          val sh = newSubstHandle(resolved)
          out.writeLong(sh); writeEnd(out); out.flush()

        case ReqApplySubstituter =>
          val sh = in.readLong()
          val h = in.readLong()
          val substMap = substHandles(sh)
          val visitor = new CollectingVisitor[Unit, IExpression] {
            override def preVisit(t: IExpression, unit: Unit): PreVisitResult = substMap.get(t) match {
              case Some(nt) => ShortCutResult(nt)
              case _ => KeepArg
            }
            def postVisit(t: IExpression, unit: Unit, subs: Seq[IExpression]): IExpression = t update subs
          }
          val res = newExprHandle(visitor.visit(exprHandles(h), ()))
          out.writeLong(res); writeEnd(out); out.flush()

        case ReqAsString =>
          val h = in.readLong()
          serializer.serialize(exprHandles(h).toString, out); writeEnd(out); out.flush()

        case ReqDecodeGround =>
          val h = in.readLong()
          val tpe = serializer.deserialize[Type](in)
          val res = realSolver.princessToInox.asGround(exprHandles(h), tpe)
          serializer.serialize(res, out); writeEnd(out); out.flush()

        case ReqModelEval =>
          val mh = in.readLong()
          val h = in.readLong()
          val tpe = serializer.deserialize[Type](in)
          val model = modelHandles(mh)
          val (decoded, chooseMap) = realSolver.princessToInox(exprHandles(h), tpe)(using model)
          serializer.serialize((decoded, chooseMap.toMap), out); writeEnd(out); out.flush()

        case ReqExtractConstructor =>
          val mh = in.readLong()
          val h = in.readLong()
          val _ = serializer.deserialize[ADTType](in) // tpe unused by extractConstructor, kept for wire symmetry
          val model = modelHandles(mh)
          val res = extractConstructor(exprHandles(h), model)
          serializer.serialize(res, out); writeEnd(out); out.flush()

        case other =>
          throw FatalError(s"princess-proc worker: unknown request tag $other")
      }
    }

    controlSocket.close()
    interruptSocket.close()
    System.exit(0)
  }
}
