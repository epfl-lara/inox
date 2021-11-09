/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

class ChooseEncoder private
  (val program: Program)
  (val sourceEncoder: transformers.ProgramTransformer { val sourceProgram: program.type })
  (override val sourceProgram: sourceEncoder.targetProgram.type,
   override val targetProgram: Program { val trees: sourceEncoder.targetProgram.trees.type })
  (private val scopes: Map[Identifier, Seq[sourceProgram.trees.ValDef]])
  extends transformers.ProgramTransformer {

  import sourceProgram.trees._

  private def this(program: Program,
                   sourceEncoder: transformers.ProgramTransformer {val sourceProgram: program.type},
                   args: (Program {val trees: sourceEncoder.targetProgram.trees.type},
                     Map[Identifier, Seq[sourceEncoder.targetProgram.trees.ValDef]]))
  = this(program)(sourceEncoder)(sourceEncoder.targetProgram, args._1)(args._2)

  def this(program: Program,
           sourceEncoder: transformers.ProgramTransformer {val sourceProgram: program.type})
  = this(program, sourceEncoder, ChooseEncoder.ctorHelper(program, sourceEncoder))

  private lazy val chooses = {
    import program._
    import program.trees._
    program.symbols.functions.values.flatMap { fd =>
      exprOps.collect { case c: Choose => Set(c) case _ => Set.empty[Choose] } (fd.fullBody)
        .map(c => c.res.id -> c)
    }.toMap
  }

  protected val encoder: transformers.TreeTransformer {val s: sourceProgram.trees.type; val t: targetProgram.trees.type} = {
    class EncoderImpl(override val s: sourceProgram.trees.type, override val t: targetProgram.trees.type)
      extends transformers.ConcreteTreeTransformer(s, t)
    new EncoderImpl(sourceProgram.trees, targetProgram.trees)
  }

  protected val decoder: transformers.TreeTransformer {val s: targetProgram.trees.type; val t: sourceProgram.trees.type} = {
    class DecoderImpl(override val s: targetProgram.trees.type, override val t: sourceProgram.trees.type)
      extends transformers.ConcreteTreeTransformer(s, t)
    new DecoderImpl(targetProgram.trees, sourceProgram.trees)
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
  } = {
    class Impl(override val program: p.type, override val sourceEncoder: enc.type)
      extends ChooseEncoder(program, sourceEncoder)
    new Impl(p, enc)
  }

  private def ctorHelper(program: Program,
                         sourceEncoder: transformers.ProgramTransformer {val sourceProgram: program.type}):
  (Program {val trees: sourceEncoder.targetProgram.trees.type},
    Map[Identifier, Seq[sourceEncoder.targetProgram.trees.ValDef]]) = {
    val sourceProgram: sourceEncoder.targetProgram.type = sourceEncoder.targetProgram
    val (newFunctions, scopes) = ChooseEncoder.computeFunctionsAndScopes(sourceProgram)
    val targetProgram = Program(sourceProgram.trees)(sourceProgram.symbols withFunctions newFunctions)
    (targetProgram, scopes)
  }

  private def computeFunctionsAndScopes(sourceProgram: Program): (Seq[sourceProgram.trees.FunDef], Map[Identifier, Seq[sourceProgram.trees.ValDef]]) = {
    import sourceProgram.trees._
    var fdChooses: Set[(Identifier, FunDef, Seq[ValDef])] = Set.empty

    val newFds = sourceProgram.symbols.functions.values.toList.map { fd =>
      def rec(e: Expr, params: Seq[ValDef]): Expr = e match {
        case l: Let => l.copy(body = rec(l.body, params :+ l.vd)).copiedFrom(l)

        case l: Lambda => l.copy(body = rec(l.body, params ++ l.params)).copiedFrom(l)

        case c: Choose =>
          val (substMap, freshParams) = params.foldLeft((Map[ValDef, Expr](), Seq[ValDef]())) {
            case ((substMap, vds), vd) =>
              val ntpe = typeOps.replaceFromSymbols(substMap, vd.tpe)
              val nvd = ValDef(vd.id.freshen, ntpe, vd.flags).copiedFrom(vd)
              (substMap + (vd -> nvd.toVariable), vds :+ nvd)
          }

          val newPred = exprOps.replaceFromSymbols(substMap, rec(c.pred, params :+ c.res))
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
}
