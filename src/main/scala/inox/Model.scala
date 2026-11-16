/* Copyright 2009-2018 EPFL, Lausanne */

package inox

object optPrintInterpretations extends FlagOptionDef("print-interpretations", false)

object Model {
  def empty(p: Program): p.Model = {
    class EmptyImpl(override val program: p.type,
                    override val vars: Map[p.trees.ValDef, p.trees.Expr],
                    override val interpretations: Map[(Identifier, Seq[p.trees.Type]), p.trees.Expr])
      extends Model(program)(vars, interpretations)
    new EmptyImpl(p, Map.empty, Map.empty)
  }

  def apply(p: Program)(
    vs: Map[p.trees.ValDef, p.trees.Expr],
    cs: Map[(Identifier, Seq[p.trees.Type]), p.trees.Expr],
    tps: Map[p.trees.TypeParameter, p.trees.Type] = Map.empty[p.trees.TypeParameter, p.trees.Type]
  ): p.Model = {
    class Impl(override val program: p.type,
               override val vars: Map[p.trees.ValDef, p.trees.Expr],
               override val interpretations: Map[(Identifier, Seq[p.trees.Type]), p.trees.Expr],
               override val types: Map[p.trees.TypeParameter, p.trees.Type])
      extends Model(program)(vars, interpretations, types)
    new Impl(p, vs, cs, tps)
  }
}

/** A model of a formula: the values of its free variables `vars`, the interpretations of its
  * uninterpreted functions, and the `types` that its type parameters stand for,
  * e.g. an empty type when the formula only has models in which some type parameter is empty.
  * The values of the model have these types. The type parameters that `types` leaves out may
  * stand for any (inhabited) type. */
class Model(val program: Program)
           (val vars: Map[program.trees.ValDef, program.trees.Expr],
            val interpretations: Map[(Identifier, Seq[program.trees.Type]), program.trees.Expr],
            val types: Map[program.trees.TypeParameter, program.trees.Type] =
              Map.empty[program.trees.TypeParameter, program.trees.Type]) { self =>
  import program.{Model => _, _}
  import program.trees._

  def isEmpty: Boolean = vars.isEmpty && interpretations.isEmpty && types.isEmpty

  def encode(t: transformers.ProgramTransformer {
    val sourceProgram: program.type
  }): t.targetProgram.Model = {
    class EncodedImpl(override val program: t.targetProgram.type,
                      override val vars: Map[t.targetProgram.trees.ValDef, t.targetProgram.trees.Expr],
                      override val interpretations: Map[(Identifier, Seq[t.targetProgram.trees.Type]), t.targetProgram.trees.Expr],
                      override val types: Map[t.targetProgram.trees.TypeParameter, t.targetProgram.trees.Type])
      extends Model(program)(vars, interpretations, types)

    new EncodedImpl(
      t.targetProgram,
      self.vars.map { case (vd, e) => t.encode(vd) -> t.encode(e) },
      self.interpretations.map { case ((id, tps), e) => (id, tps.map(t.encode(_))) -> t.encode(e) },
      self.types.flatMap { case (tp, tpe) => t.encode(tp) match {
        case etp: t.targetProgram.trees.TypeParameter => Some(etp -> t.encode(tpe))
        case _ => None
      }}
    )
  }

  def asString(using opts: PrinterOptions): String = {
    val typeString: String = types.toSeq.map { case (tp, tpe) =>
      "type " + tp.asString + " -> " + tpe.asString
    }.mkString("\n")

    val varString: String = if (vars.isEmpty) "" else {
      val max = vars.keys.map(_.asString.length).max
      (for ((vd, e) <- vars) yield {
        ("%-" + max + "s -> %s").format(vd.asString, e.asString)
      }).mkString("\n")
    }

    val modelString = Seq(typeString, varString).filter(_.nonEmpty).mkString("\n")

    // The functions without definitions call uninterpreted functions (see `exprOps.uninterpretedBody`)
    val uninterpretedFds = symbols.functions.values.flatMap(fd => fd.fullBody match {
      case UninterpretedCall(ucId, _, _, _) =>
        val cs = interpretations.filter { case ((id, _), _) => ucId == id }
        if (cs.isEmpty) None else Some(fd -> cs)
      case _ => None
    }).toSeq

    val functionString = (for {
      (fd, cs) <- uninterpretedFds
      ((id, tps), e) <- cs
    } yield {
      fd.id.asString +
      (if (tps.nonEmpty) "[" + tps.map(_.asString).mkString(",") + "]" else "") +
      (if (fd.params.nonEmpty) "(" + fd.params.map(_.asString).mkString(", ") + ")" else "") +
      " -> " + e.asString
    }).mkString("\n")

    lazy val interpretationString = if (!opts.printInterpretations) "" else {
      val fdUninterpreted = symbols.functions.values.flatMap(fd => fd.fullBody match {
        case UninterpretedCall(ucId, _, _, _) => Some(ucId)
        case _ => None
      }).toSet

      interpretations.collect { case ((id, tps), e) if !fdUninterpreted(id) =>
        id.asString +
        (if (tps.nonEmpty) " (typed [" + tps.mkString(",") + "])" else "") +
        " -> " + e.asString
      }.mkString("\n")
    }

    if (modelString.isEmpty && functionString.isEmpty && (interpretations.isEmpty || !opts.printInterpretations)) {
      if (interpretations.isEmpty) {
        "(Empty model)"
      } else {
        "(Model with interpretations)"
      }
    } else {
      modelString +
      (if (modelString.nonEmpty && functionString.nonEmpty) "\n\n" else "") +
      functionString +
      (if ((modelString.nonEmpty || functionString.nonEmpty) && interpretationString.nonEmpty) "\n\n" else "") +
      interpretationString
    }
  }

  override def toString: String = asString(using PrinterOptions(symbols = Some(symbols)))
}
