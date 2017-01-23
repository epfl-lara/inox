/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

trait ChooseEncoder extends ast.ProgramTransformer {
  val program: Program
  val sourceEncoder: ast.ProgramTransformer { val sourceProgram: program.type }

  lazy val sourceProgram: sourceEncoder.targetProgram.type = sourceEncoder.targetProgram
  import sourceProgram.trees._

  private lazy val chooses = {
    import program._
    import program.trees._
    program.symbols.functions.values.flatMap { fd =>
      exprOps.collect { case c: Choose => Set(c) case _ => Set.empty[Choose] } (fd.fullBody).map(c => c.res -> c)
    }.toMap
  }

  private lazy val (newFunctions: Seq[FunDef], scopes: Map[ValDef, Seq[ValDef]]) = {
    var fdChooses: Set[(ValDef, FunDef, Seq[ValDef])] = Set.empty

    val newFds = sourceProgram.symbols.functions.values.toList.map { fd =>
      def rec(e: Expr, args: Seq[ValDef]): Expr = e match {
        case l: Lambda =>
          val free = exprOps.variablesOf(l)
          l.copy(body = rec(l.body, args.filter(vd => free(vd.toVariable)) ++ l.args)).copiedFrom(l)

        case c: Choose =>
          val newPred = rec(c.pred, args)
          val freshArgs = args.map(_.freshen)

          val substPred = exprOps.replaceFromSymbols(
            (args zip freshArgs.map(_.toVariable)).toMap,
            newPred)

          val newFd = new FunDef(
            FreshIdentifier("choose", true), fd.tparams, freshArgs,
            c.res.tpe, Choose(c.res, substPred).copiedFrom(c), Set.empty)
          fdChooses += ((c.res, newFd, args))

          FunctionInvocation(newFd.id, newFd.tparams.map(_.tp), args.map(_.toVariable)).copiedFrom(c)

        case Operator(es, recons) => recons(es.map(rec(_, args))).copiedFrom(e)
      }

      fd.copy(fullBody = fd.fullBody match {
        case c: Choose => c.copy(pred = rec(c.pred, fd.params)).copiedFrom(c)
        case body => rec(body, fd.params)
      })
    }

    val allFunctions = newFds ++ fdChooses.map(_._2)
    val allScopes = fdChooses.map(p => p._1 -> p._3).toMap ++ newFds.flatMap(fd => fd.fullBody match {
      case c: Choose => Some(c.res -> fd.params)
      case _ => None
    })

    (allFunctions, allScopes)
  }

  lazy val targetProgram: Program { val trees: sourceEncoder.targetProgram.trees.type } = new Program {
    val trees: sourceEncoder.targetProgram.trees.type = sourceEncoder.targetProgram.trees
    val symbols = sourceProgram.symbols.withFunctions(newFunctions)
    val ctx = sourceProgram.ctx
  }

  protected object encoder extends ast.TreeTransformer {
    val s: sourceProgram.trees.type = sourceProgram.trees
    val t: targetProgram.trees.type = targetProgram.trees
  }

  protected object decoder extends ast.TreeTransformer {
    val s: targetProgram.trees.type = targetProgram.trees
    val t: sourceProgram.trees.type = sourceProgram.trees
  }

  def getChoose(fd: targetProgram.trees.FunDef): Option[(Identifier, program.trees.Choose, Seq[program.trees.ValDef])] = fd.fullBody match {
    case targetProgram.trees.Choose(res, _) =>
      scopes.get(res).flatMap { vds =>
        val dres = sourceEncoder.decode(decoder.transform(res))
        chooses.get(dres).map(c => (res.id, c, vds.map(sourceEncoder.decode(_))))
      }
    case _ => None
  }
}

object ChooseEncoder {
  def apply(p: Program)(enc: ast.ProgramTransformer { val sourceProgram: p.type }): ChooseEncoder {
    val program: p.type
    val sourceEncoder: enc.type
  } = new ChooseEncoder {
    val program: p.type = p
    val sourceEncoder: enc.type = enc
  }
}
