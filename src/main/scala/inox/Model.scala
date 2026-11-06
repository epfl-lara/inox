/* Copyright 2009-2018 EPFL, Lausanne */

package inox

object optPrintChooses extends FlagOptionDef("print-chooses", false)

object Model {
  def empty(p: Program): p.Model = apply(p)(Map.empty, Map.empty)

  def apply(p: Program)(
    vs: Map[p.trees.ValDef, p.trees.Expr],
    cs: Map[(Identifier, Seq[p.trees.Type]), p.trees.Expr],
    fs: Seq[p.trees.FunDef] = Seq.empty
  ): p.Model = {
    class Impl(override val program: p.type,
               override val vars: Map[p.trees.ValDef, p.trees.Expr],
               override val chooses: Map[(Identifier, Seq[p.trees.Type]), p.trees.Expr],
               override val functions: Seq[p.trees.FunDef])
      extends Model(program)(vars, chooses, functions)
    new Impl(p, vs, cs, fs)
  }
}

/** A model of a formula: values for its free variables and its `choose`s.
  *
  * The values may call functions that the program doesn't define. Their definitions are in `functions`,
  * and [[symbols]] is the program extended with them: model values are typed, printed and evaluated
  * with these symbols, as in the input extraction of Voirol's thesis (§2.2).
  */
class Model(val program: Program)
           (val vars: Map[program.trees.ValDef, program.trees.Expr],
            val chooses: Map[(Identifier, Seq[program.trees.Type]), program.trees.Expr],
            val functions: Seq[program.trees.FunDef] = Seq.empty) { self =>
  import program.{Model => _, symbols => _, _}
  import program.trees._

  /** The program's symbols extended with the model's definitions. */
  lazy val symbols: Symbols =
    if (functions.isEmpty) program.symbols else program.symbols.withFunctions(functions)

  def isEmpty: Boolean = vars.isEmpty && chooses.isEmpty && functions.isEmpty

  def encode(t: transformers.ProgramTransformer {
    val sourceProgram: Program { val trees: program.trees.type }
  }): t.targetProgram.Model = {
    Model(t.targetProgram)(
      self.vars.map { case (vd, e) => t.encode(vd) -> t.encode(e) },
      self.chooses.map { case ((id, tps), e) => (id, tps.map(t.encode(_))) -> t.encode(e) },
      self.functions.map(t.encode(_))
    )
  }

  def asString(using opts: PrinterOptions): String = {
    val modelString: String = if (vars.isEmpty) "" else {
      val max = vars.keys.map(_.asString.length).max
      (for ((vd, e) <- vars) yield {
        ("%-" + max + "s -> %s").format(vd.asString, e.asString)
      }).mkString("\n")
    }

    val chooseFds = program.symbols.functions.values.flatMap(fd => fd.fullBody match {
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
      val fdChooses = program.symbols.functions.values.flatMap(fd => fd.fullBody match {
        case Choose(res, _) => Some(res.id)
        case _ => None
      }).toSet

      chooses.collect { case ((id, tps), e) if !fdChooses(id) =>
        id.asString +
        (if (tps.nonEmpty) " (typed [" + tps.mkString(",") + "])" else "") +
        " -> " + e.asString
      }.mkString("\n")
    }

    val defString = functions.map(_.asString).mkString("\n\n")

    if (defString.isEmpty && modelString.isEmpty && functionString.isEmpty && (chooses.isEmpty || !opts.printChooses)) {
      if (chooses.isEmpty) {
        "(Empty model)"
      } else {
        "(Model with chooses)"
      }
    } else {
      defString +
      (if (defString.nonEmpty && (modelString.nonEmpty || functionString.nonEmpty)) "\n\n" else "") +
      modelString +
      (if (modelString.nonEmpty && functionString.nonEmpty) "\n\n" else "") +
      functionString +
      (if ((defString.nonEmpty || modelString.nonEmpty || functionString.nonEmpty) && chooseString.nonEmpty) "\n\n" else "") +
      chooseString
    }
  }

  override def toString: String = asString(using PrinterOptions(symbols = Some(symbols)))
}
