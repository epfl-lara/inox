/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package tip

/** Prints model values as SMT-LIB terms, for tools that drive Inox
  * through its command line (see `--model-format=smtlib`).
  *
  * Free variables and constructors are printed with the names they had in
  * the input, so a TIP producer can map a model back to its own terms.
  * Variables bound inside values (lambda parameters) get unique names.
  */
object ValuePrinter {
  import inox.trees._

  def sort(tpe: Type): String = tpe match {
    case IntegerType() => "Int"
    case BooleanType() => "Bool"
    case RealType() => "Real"
    case BVType(_, size) => s"(_ BitVec $size)"
    case ADTType(id, Seq()) => id.name
    case ADTType(id, tps) => tps.map(sort).mkString(s"(${id.name} ", " ", ")")
    case TypeParameter(id, _) => id.name
    case FunctionType(from, to) => (from :+ to).map(sort).mkString("(=> ", " ", ")")
    case _ => throw UnsupportedValue(tpe.toString)
  }

  case class UnsupportedValue(desc: String) extends Exception(s"cannot print $desc as SMT-LIB")

  def value(e: Expr): String = e match {
    case IntegerLiteral(v) => if (v < 0) s"(- ${-v})" else v.toString
    case BooleanLiteral(b) => b.toString
    case FractionLiteral(n, d) =>
      val num = if (n < 0) s"(- ${-n})" else n.toString
      s"(/ $num $d)"
    case UMinus(a) => s"(- ${value(a)})"
    case ADT(id, _, Seq()) => id.name
    case ADT(id, _, args) => args.map(value).mkString(s"(${id.name} ", " ", ")")
    case v: Variable => v.id.uniqueName
    case Lambda(params, body) =>
      val ps = params.map(vd => s"(${vd.id.uniqueName} ${sort(vd.getType(using NoSymbols))})")
      ps.mkString("(lambda (", " ", s") ${value(body)})")
    case IfExpr(c, t, f) => s"(ite ${value(c)} ${value(t)} ${value(f)})"
    case Equals(a, b) => s"(= ${value(a)} ${value(b)})"
    case And(es) => es.map(value).mkString("(and ", " ", ")")
    case Or(es) => es.map(value).mkString("(or ", " ", ")")
    case Not(a) => s"(not ${value(a)})"
    case Let(vd, v, b) => s"(let ((${vd.id.uniqueName} ${value(v)})) ${value(b)})"
    case _ => throw UnsupportedValue(e.toString)
  }

  /** The model in `get-value` response form: `((x v) (y w) ...)`. */
  def model(vars: Map[ValDef, Expr]): String =
    vars.toSeq.sortBy(_._1.id.name).map { case (vd, v) => s"(${vd.id.name} ${value(v)})" }
      .mkString("(", " ", ")")
}
