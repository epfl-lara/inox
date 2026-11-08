/* Copyright 2009-2018 EPFL, Lausanne */

package inox

object optPrintChooses extends FlagOptionDef("print-chooses", false)

object Model {
  def empty(p: Program): p.Model = {
    class EmptyImpl(override val program: p.type,
                    override val vars: Map[p.trees.ValDef, p.trees.Expr],
                    override val chooses: Map[(Identifier, Seq[p.trees.Type]), p.trees.Expr])
      extends Model(program)(vars, chooses)
    new EmptyImpl(p, Map.empty, Map.empty)
  }

  def apply(p: Program)(
    vs: Map[p.trees.ValDef, p.trees.Expr],
    cs: Map[(Identifier, Seq[p.trees.Type]), p.trees.Expr]
  ): p.Model = {
    class Impl(override val program: p.type,
               override val vars: Map[p.trees.ValDef, p.trees.Expr],
               override val chooses: Map[(Identifier, Seq[p.trees.Type]), p.trees.Expr])
      extends Model(program)(vars, chooses)
    new Impl(p, vs, cs)
  }
}

class Model(val program: Program)
           (val vars: Map[program.trees.ValDef, program.trees.Expr],
            val chooses: Map[(Identifier, Seq[program.trees.Type]), program.trees.Expr]) { self =>
  import program.{Model => _, _}
  import program.trees._

  def isEmpty: Boolean = vars.isEmpty && chooses.isEmpty

  def encode(t: transformers.ProgramTransformer {
    val sourceProgram: program.type
  }): t.targetProgram.Model = {
    class EncodedImpl(override val program: t.targetProgram.type,
                      override val vars: Map[t.targetProgram.trees.ValDef, t.targetProgram.trees.Expr],
                      override val chooses: Map[(Identifier, Seq[t.targetProgram.trees.Type]), t.targetProgram.trees.Expr])
      extends Model(program)(vars, chooses)

    new EncodedImpl(
      t.targetProgram,
      self.vars.map { case (vd, e) => t.encode(vd) -> t.encode(e) },
      self.chooses.map { case ((id, tps), e) => (id, tps.map(t.encode(_))) -> t.encode(e) }
    )
  }

  def asString(using opts: PrinterOptions): String = {
    val modelString: String = if (vars.isEmpty) "" else {
      val max = vars.keys.map(_.asString.length).max
      (for ((vd, e) <- vars) yield {
        ("%-" + max + "s -> %s").format(vd.asString, e.asString)
      }).mkString("\n")
    }

    val chooseFds = symbols.functions.values.flatMap(fd => fd.fullBody match {
      case Choose(res, _) =>
        val cs = chooses.filter { case ((id, _), _) => res.id == id }
        if (cs.isEmpty) None else Some(fd -> cs)
      case _ => None
    }).toSeq

    val functionString = (for {
      (fd, cs) <- chooseFds
      ((id, tps), e) <- cs
    } yield {
      fd.id.asString +
      (if (tps.nonEmpty) "[" + tps.map(_.asString).mkString(",") + "]" else "") +
      (if (fd.params.nonEmpty) "(" + fd.params.map(_.asString).mkString(", ") + ")" else "") +
      " -> " + e.asString
    }).mkString("\n")

    lazy val chooseString = if (!opts.printChooses) "" else {
      val fdChooses = symbols.functions.values.flatMap(fd => fd.fullBody match {
        case Choose(res, _) => Some(res.id)
        case _ => None
      }).toSet

      chooses.collect { case ((id, tps), e) if !fdChooses(id) =>
        id.asString +
        (if (tps.nonEmpty) " (typed [" + tps.mkString(",") + "])" else "") +
        " -> " + e.asString
      }.mkString("\n")
    }

    if (modelString.isEmpty && functionString.isEmpty && (chooses.isEmpty || !opts.printChooses)) {
      if (chooses.isEmpty) {
        "(Empty model)"
      } else {
        "(Model with chooses)"
      }
    } else {
      modelString +
      (if (modelString.nonEmpty && functionString.nonEmpty) "\n\n" else "") +
      functionString +
      (if ((modelString.nonEmpty || functionString.nonEmpty) && chooseString.nonEmpty) "\n\n" else "") +
      chooseString
    }
  }

  override def toString: String = asString(using PrinterOptions(symbols = Some(symbols)))
}
