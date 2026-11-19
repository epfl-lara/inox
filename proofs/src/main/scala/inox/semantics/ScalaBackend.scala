/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package semantics

/** Writes a [[Spec]] as Scala: one object with a case class per constructor and a method per
  * function, which runs the semantics on its own trees. */
object ScalaBackend {
  import Spec._

  private val keywords = Set(
    "abstract", "case", "catch", "class", "def", "do", "else", "enum", "export", "extends", "false",
    "final", "finally", "for", "given", "if", "implicit", "import", "lazy", "match", "new", "null",
    "object", "override", "package", "private", "protected", "return", "sealed", "super", "then",
    "throw", "trait", "true", "try", "type", "val", "var", "while", "with", "yield")

  /** A variable or function name as a Scala identifier that a pattern binds. */
  private def name(n: String): String = {
    val s = n.replace('-', '_')
    if (keywords(s) || s.head.isUpper) s"v_$s" else s
  }

  private def tpe(t: Type): String = t match {
    case Type.Named("Int", Seq()) => "BigInt"
    case Type.Named("Bool", Seq()) => "Boolean"
    case Type.Named("Id", Seq()) => "Id"
    case Type.Named(n, Seq()) => n
    case Type.Named(n, args) => args.map(tpe).mkString(s"$n[", ", ", "]")
    case Type.Param(p) => p
  }

  private def params(t: Type): Set[String] = t match {
    case Type.Named(_, args) => args.flatMap(params).toSet
    case Type.Param(p) => Set(p)
  }

  private def datatype(dt: Datatype): String = {
    val tps = if (dt.tparams.isEmpty) "" else dt.tparams.map("+" + _).mkString("[", ", ", "]")
    val b = new StringBuilder
    dt.ctors match {
      // a record: one constructor named after its type
      case Seq(c) if c.name == dt.name =>
        val fields = c.fields.map { case (f, t) => s"${name(f)}: ${tpe(t)}" }.mkString(", ")
        return s"  final case class ${dt.name}$tps($fields)\n"
      case cs if cs.exists(_.name == dt.name) =>
        throw SpecError(s"only a datatype with one constructor can name it ${dt.name}")
      case _ =>
    }
    b ++= s"  sealed abstract class ${dt.name}$tps\n"
    for (c <- dt.ctors) {
      val used = c.fields.flatMap(f => params(f._2)).toSet
      val ctps = dt.tparams.filter(used)
      val ctpsS = if (ctps.isEmpty) "" else ctps.map("+" + _).mkString("[", ", ", "]")
      val parent = if (dt.tparams.isEmpty) dt.name
        else dt.tparams.map(t => if (used(t)) t else "Nothing").mkString(s"${dt.name}[", ", ", "]")
      val fields = c.fields.map { case (f, t) => s"${name(f)}: ${tpe(t)}" }.mkString(", ")
      b ++= s"  final case class ${c.name}$ctpsS($fields) extends $parent\n"
    }
    b.result()
  }

  private def pattern(p: Pattern): String = p match {
    case Pattern.Wildcard => "_"
    case Pattern.Bind(x) => name(x)
    case Pattern.BoolLit(v) => v.toString
    case Pattern.Ctor(c, args) => args.map(pattern).mkString(s"$c(", ", ", ")")
  }

  private def ind(n: Int) = "  " * n

  private def term(t: Term, d: Int): String = t match {
    case Term.Var(x) => name(x)
    case Term.IntLit(v) => if (v.isValidInt) s"BigInt($v)" else s"""BigInt("$v")"""
    case Term.BoolLit(v) => v.toString
    case Term.Ctor(c, args) => args.map(term(_, d)).mkString(s"$c(", ", ", ")")
    case Term.Call(f, args) => args.map(term(_, d)).mkString(s"${name(f)}(", ", ", ")")
    case Term.Builtin(op, Seq(a)) =>
      assert(op == "not")
      s"!(${term(a, d)})"
    case Term.Builtin(op, Seq(a, b)) =>
      val (x, y) = (term(a, d), term(b, d))
      op match {
        case "div" => s"ediv($x, $y)"
        case "mod" => s"emod($x, $y)"
        case "and" => s"($x && $y)"
        case "or" => s"($x || $y)"
        case "=" => s"($x == $y)"
        case _ => s"($x $op $y)"
      }
    case Term.Builtin(op, _) => throw SpecError(s"arity of $op")
    case Term.Let(bs, body) =>
      val vals = bs.map { case (x, v) => s"${ind(d + 1)}val ${name(x)} = ${term(v, d + 1)}\n" }.mkString
      s"{\n$vals${ind(d + 1)}${term(body, d + 1)}\n${ind(d)}}"
    case Term.LetBang(bs, body) if bs.isEmpty => term(body, d)
    case Term.LetBang(bs, body) =>
      val ((x, v), rest) = (bs.head, bs.tail)
      s"${term(v, d)} match {\n" +
      s"${ind(d + 1)}case Ok(${name(x)}) => ${term(Term.LetBang(rest, body), d + 1)}\n" +
      s"${ind(d + 1)}case Stuck() => Stuck()\n" +
      s"${ind(d + 1)}case OutOfFuel() => OutOfFuel()\n" +
      s"${ind(d)}}"
    case Term.If(c, a, b) =>
      s"if (${term(c, d)}) {\n${ind(d + 1)}${term(a, d + 1)}\n${ind(d)}} else {\n${ind(d + 1)}${term(b, d + 1)}\n${ind(d)}}"
    case Term.Match(s, cases) =>
      val cs = cases.map { case (p, b) => s"${ind(d + 1)}case ${pattern(p)} => ${term(b, d + 2)}\n" }.mkString
      s"(${term(s, d)}) match {\n$cs${ind(d)}}"
  }

  private def function(f: Function): String = {
    val ps = f.params.map { case (x, t) => s"${name(x)}: ${tpe(t)}" }.mkString(", ")
    val head = s"  def ${name(f.name)}($ps): ${tpe(f.result)} ="
    f.body match {
      case Body.Term(t) => s"$head\n${ind(2)}${term(t, 2)}\n"
      case Body.Cases(x, cases) =>
        val cs = cases.map { case (p, b) => s"${ind(2)}case ${pattern(p)} =>\n${ind(3)}${term(b, 3)}\n" }.mkString
        s"$head ${name(x)} match {\n$cs  }\n"
    }
  }

  def apply(spec: Spec, source: String, pkg: String): String = {
    val b = new StringBuilder
    b ++= "/* Copyright 2009-2026 EPFL, Lausanne */\n\n"
    b ++= s"// Generated from $source by inox.semantics.Codegen. Do not edit: change $source\n"
    b ++= "// and regenerate (see proofs/README.md).\n\n"
    b ++= s"package $pkg\n\n"
    b ++= "import scala.language.unsafeNulls\n\n"
    b ++= "object Semantics {\n"
    b ++= "  type Id = inox.Identifier\n\n"
    b ++= "  /** The euclidean quotient and remainder, as `div` and `mod` in the semantics; 0 and `a` for a\n"
    b ++= "    * zero `b`, where the semantics leaves them unused. */\n"
    b ++= "  def ediv(a: BigInt, b: BigInt): BigInt = if (b == 0) BigInt(0) else (a - emod(a, b)) / b\n"
    b ++= "  def emod(a: BigInt, b: BigInt): BigInt = if (b == 0) a else a.mod(b.abs)\n\n"
    for (dt <- spec.datatypes) b ++= datatype(dt) + "\n"
    b ++= spec.functions.map(function).mkString("\n")
    b ++= "}\n"
    b.result()
  }
}
