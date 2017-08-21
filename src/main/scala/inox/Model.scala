/* Copyright 2009-2016 EPFL, Lausanne */

package inox

object optPrintChooses extends FlagOptionDef("printchooses", false)

object Model {
  def empty(p: Program, ctx: Context): p.Model = new Model {
    val program: p.type = p
    val context = ctx
    val vars: Map[p.trees.ValDef, p.trees.Expr] = Map.empty
    val chooses: Map[(Identifier, Seq[p.trees.Type]), p.trees.Expr] = Map.empty
  }

  def apply(p: Program, ctx: Context)(
    vs: Map[p.trees.ValDef, p.trees.Expr],
    cs: Map[(Identifier, Seq[p.trees.Type]), p.trees.Expr]
  ): p.Model = new Model {
    val program: p.type = p
    val context = ctx
    val vars = vs
    val chooses = cs
  }
}

trait Model { self =>
  protected val program: Program
  protected val context: Context

  import context._
  import program._
  import program.trees._

  val vars: Map[ValDef, Expr]
  val chooses: Map[(Identifier, Seq[Type]), Expr]

  def isEmpty: Boolean = vars.isEmpty && chooses.isEmpty

  def encode(t: ast.ProgramTransformer {
    val sourceProgram: program.type
  }): t.targetProgram.Model = new inox.Model {
    val program: t.targetProgram.type = t.targetProgram
    val context = self.context
    val vars = self.vars.map { case (vd, e) => t.encode(vd) -> t.encode(e) }
    val chooses = self.chooses.map { case ((id, tps), e) => (id, tps.map(t.encode(_))) -> t.encode(e) }
  }

  def asString: String = {
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

    val printChooses = options.findOptionOrDefault(optPrintChooses)
    lazy val chooseString = if (!printChooses) "" else {
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

    if (modelString.isEmpty && functionString.isEmpty && (chooses.isEmpty || !printChooses)) {
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

  override def toString: String = asString
}
