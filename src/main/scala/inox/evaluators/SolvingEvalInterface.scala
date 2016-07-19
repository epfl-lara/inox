
package inox
package evaluators

import scala.collection.mutable.{Map => MutableMap}

trait SolvingEvalInterface {
  val program: Program
  import program._
  import program.trees._
  import program.symbols._

  val evaluator: DeterministicEvaluator with SolvingEvaluator { val program: SolvingEvalInterface.this.program.type }
  val bodies: Map[Identifier, (Seq[ValDef], Expr)]

  private val inputCache: MutableMap[(Identifier, Seq[Expr]), Expr] = MutableMap.empty
  private val forallCache: MutableMap[Forall, Expr] = MutableMap.empty

  def onInputInvocation(id: Identifier, args: Seq[Expr]): Expr = inputCache.getOrElseUpdate((id, args), {
    val (vds, body) = bodies.getOrElse(id, throw new RuntimeException("Body for " + id + " not found"))
    val tpSubst = canBeSupertypeOf(tupleTypeWrap(vds.map(_.tpe)), tupleTypeWrap(args.map(_.getType))).getOrElse {
      throw new RuntimeException("Cannot construct typing substitution from " + vds.map(_.asString).mkString(",") + " to " + args.map(_.asString))
    }

    val model = (vds.map(vd => vd.copy(tpe = instantiateType(vd.tpe, tpSubst))) zip args).toMap
    val instBody = instantiateType(body, tpSubst)
    evaluator.eval(instBody, model).result.getOrElse {
      throw new RuntimeException("Couldn't evaluate " + instBody.asString + " with model " +
        model.map(p => p._1.asString -> p._2.asString).mkString("{", ", ", "}"))
    }
  })

  def onForallInvocation(forall: Forall): Expr = forallCache.getOrElseUpdate(forall, {
    

  })
}
