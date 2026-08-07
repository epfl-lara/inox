/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package princess

import unrolling._

import scala.collection.mutable.{Map => MutableMap}

/** Process-isolated counterpart to [[PrincessSolver]]: identical shape
  * (same `AbstractUnrollingSolver` subclassing, same `theories.Princess`
  * theory encoding, same `TemplatesImpl`/`ModelWrapperImpl` bodies), but its
  * `underlying` slot is a [[RemotePrincessClient]] instead of a live
  * `AbstractPrincessSolver` -- every operation that would touch the native
  * Princess API directly is instead a blocking RPC to a child JVM (see
  * [[PrincessWorkerMain]]), which hosts the real, unmodified
  * `AbstractPrincessSolver`. `Encoded` is an opaque `Long` handle rather
  * than `IExpression`, since Princess terms can't leave that child JVM.
  */
class RemotePrincessSolver(override val program: Program)
                          (override val prog: program.type,
                           override val context: Context,
                           override val enc: transformers.ProgramTransformer {
                             val sourceProgram: program.type
                             val targetProgram: Program { val trees: inox.trees.type }
                           },
                           override val chooses: ChooseEncoder {val program: prog.type; val sourceEncoder: enc.type})
                          (using semantics: prog.Semantics,
                           semanticsProvider: SemanticsProvider {val trees: enc.targetProgram.trees.type})
  extends AbstractUnrollingSolver(program, context, enc, chooses)
    (fullEncoder => solvers.theories.Princess(fullEncoder)(semantics.getEvaluator(using context))) { self =>

  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  override val name = "Princess-proc"

  protected val underlying: RemotePrincessClient { val program: targetProgram.type } =
    RemotePrincessClient.spawn(targetProgram, context)

  type Encoded = Long

  val templates = new TemplatesImpl(targetProgram, context)

  protected def declareVariable(v: t.Variable): Long = underlying.declareVariable(v)

  protected def wrapModel(model: underlying.Model): ModelWrapper = ModelWrapperImpl(model)

  private case class ModelWrapperImpl(model: Long) extends ModelWrapper {
    private val chooses: MutableMap[Identifier, t.Expr] = MutableMap.empty

    def extractConstructor(v: Long, tpe: t.ADTType): Option[Identifier] =
      underlying.extractConstructor(model, v, tpe)

    def extractSet(v: Long, tpe: t.SetType) = scala.sys.error("Should never happen")
    def extractBag(v: Long, tpe: t.BagType) = scala.sys.error("Should never happen")
    def extractMap(v: Long, tpe: t.MapType) = scala.sys.error("Should never happen")

    def modelEval(elem: Long, tpe: t.Type): Option[t.Expr] = timers.solvers.princess.eval.run {
      val (res, cs) = underlying.modelEval(model, elem, tpe)
      chooses ++= cs.map(p => p._1.res.id -> p._2)
      res
    }

    def getChoose(id: Identifier): Option[t.Expr] = chooses.get(id)

    override def toString = model.toString
  }

  private class TemplatesImpl(override val program: targetProgram.type,
                              override val context: Context)
                             (using override val semantics: targetProgram.Semantics) extends Templates {
    import program.trees._

    type Encoded = self.Encoded

    def asString(ast: Long): String = underlying.asString(ast)
    def abort: Boolean = self.abort
    def pause: Boolean = self.pause

    def encodeSymbol(v: Variable): Long = underlying.freshSymbol(v)

    def mkEncoder(bindings: Map[Variable, Long])(e: Expr): Long =
      underlying.encode(e, bindings)

    def mkSubstituter(substMap: Map[Long, Long]): Long => Long = {
      val substHandle = underlying.mkSubstituter(substMap)
      (e: Long) => underlying.applySubstituter(substHandle, e)
    }

    def mkNot(e: Long): Long = underlying.mkNot(e)
    def mkAnd(es: Long*): Long = underlying.mkAnd(es.toSeq)
    def mkOr(es: Long*): Long = underlying.mkOr(es.toSeq)
    def mkImplies(e1: Long, e2: Long): Long = underlying.mkImplies(e1, e2)
    def mkEquals(e1: Long, e2: Long): Long = underlying.mkEquals(e1, e2)

    def extractNot(e: Long): Option[Long] = underlying.extractNot(e)

    def decodePartial(e: Encoded, tpe: Type): Option[Expr] = underlying.decodeGround(e, tpe)
  }

  override def push(): Unit = {
    super.push()
    underlying.push()
  }

  override def pop(): Unit = {
    super.pop()
    underlying.pop()
  }

  override def reset(): Unit = {
    super.reset()
    underlying.reset()
  }

  override def interrupt(): Unit = {
    underlying.interrupt()
    super.interrupt()
  }

  override def free(): Unit = {
    super.free()
    underlying.free()
  }
}
