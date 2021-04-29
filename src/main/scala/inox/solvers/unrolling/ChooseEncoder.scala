/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

trait ChooseEncoder extends transformers.ProgramTransformer {
  val program: Program
  val sourceEncoder: transformers.ProgramTransformer { val sourceProgram: program.type }

  lazy val sourceProgram: sourceEncoder.targetProgram.type = sourceEncoder.targetProgram
  import sourceProgram.trees._

  private lazy val chooses = {
    import program._
    import program.trees._
    program.symbols.functions.values.flatMap { fd =>
      exprOps.collect { case c: Choose => Set(c) case _ => Set.empty[Choose] } (fd.fullBody)
        .map(c => c.res.id -> c)
    }.toMap
  }

  private lazy val (newFunctions: Seq[FunDef], scopes: Map[Identifier, Seq[ValDef]]) = {
    var fdChooses: Set[(Identifier, FunDef, Seq[ValDef])] = Set.empty

    val newFds = sourceProgram.symbols.functions.values.toList.map { fd =>
      def rec(e: Expr, params: Seq[ValDef]): Expr = e match {
        case l: Let =>
          val free = exprOps.variablesOf(l)
          l.copy(body = rec(l.body, params.filter(vd => free(vd.toVariable)) :+ l.vd)).copiedFrom(l)

        case l: Lambda =>
          val free = exprOps.variablesOf(l)
          l.copy(body = rec(l.body, params.filter(vd => free(vd.toVariable)) ++ l.params)).copiedFrom(l)

        case c: Choose =>
          val (substMap, freshParams) = params.foldLeft((Map[ValDef, Expr](), Seq[ValDef]())) {
            case ((substMap, vds), vd) =>
              val ntpe = typeOps.replaceFromSymbols(substMap, vd.tpe)
              val nvd = ValDef(vd.id.freshen, ntpe, vd.flags).copiedFrom(vd)
              (substMap + (vd -> nvd.toVariable), vds :+ nvd)
          }

          val newPred = exprOps.replaceFromSymbols(substMap, rec(c.pred, params))
          val returnType = typeOps.replaceFromSymbols(substMap, c.res.tpe)

          val newFd = new FunDef(
            FreshIdentifier("choose", true), fd.tparams, freshParams,
            returnType, Choose(c.res.copy(tpe = returnType), newPred).copiedFrom(c), Seq.empty)
          fdChooses += ((c.res.id, newFd, params))

          FunctionInvocation(newFd.id, newFd.tparams.map(_.tp), params.map(_.toVariable)).copiedFrom(c)

        case Operator(es, recons) => recons(es.map(rec(_, params))).copiedFrom(e)
      }

      fd.copy(fullBody = fd.fullBody match {
        case c: Choose => c.copy(pred = rec(c.pred, fd.params)).copiedFrom(c)
        case body => rec(body, fd.params)
      })
    }

    val allFunctions = newFds ++ fdChooses.map(_._2)
    val allScopes = fdChooses.map(p => p._1 -> p._3).toMap ++ newFds.flatMap(fd => fd.fullBody match {
      case c: Choose => Some(c.res.id -> fd.params)
      case _ => None
    })

    (allFunctions, allScopes)
  }

  lazy val targetProgram: Program { val trees: sourceEncoder.targetProgram.trees.type } =
    Program(sourceEncoder.targetProgram.trees)(sourceProgram.symbols withFunctions newFunctions)

  protected object encoder extends transformers.TreeTransformer {
    val s: sourceProgram.trees.type = sourceProgram.trees
    val t: targetProgram.trees.type = targetProgram.trees
  }

  protected object decoder extends transformers.TreeTransformer {
    val s: targetProgram.trees.type = targetProgram.trees
    val t: sourceProgram.trees.type = sourceProgram.trees
  }

  def getChoose(fd: targetProgram.trees.FunDef): Option[(Identifier, program.trees.Choose, Seq[program.trees.ValDef])] = fd.fullBody match {
    case targetProgram.trees.Choose(res, _) =>
      scopes.get(res.id).flatMap { vds =>
        chooses.get(res.id).map(c => (res.id, c, vds.map(sourceEncoder.decode(_))))
      }
    case _ => None
  }
}

object ChooseEncoder {
  def apply(p: Program)(enc: transformers.ProgramTransformer { val sourceProgram: p.type }): ChooseEncoder {
    val program: p.type
    val sourceEncoder: enc.type
  } = new ChooseEncoder {
    val program: p.type = p
    val sourceEncoder: enc.type = enc
  }
}
