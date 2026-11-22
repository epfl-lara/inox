/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package certificates

/** An s-expression of a proof. A symbol of the solver's session is a [[Sym]], with the Inox
  * variable, function, sort or constructor that it stands for. Other atoms keep the text that the
  * solver printed (numerals, keywords, strings, the solver's own symbols), since proof formats such
  * as CPC have literals that SMT-LIB doesn't, as `-1` or `1/2`. */
sealed trait SExpr {
  /** The s-expression where each atom that `table` maps (without its quotes `|...|`) is a symbol. */
  def resolve(table: String => Option[Ref]): SExpr = this match {
    case a @ Atom(text) =>
      val name = if (text.length >= 2 && text.head == '|' && text.last == '|') text.substring(1, text.length - 1) else text
      table(name).fold(a)(Sym(text, _))
    case SList(items) => SList(items.map(_.resolve(table)))
    case sym: Sym => sym
  }

  /** The symbols of the s-expression, by their text. */
  def symbols: Seq[Sym] = this match {
    case _: Atom => Seq()
    case SList(items) => items.flatMap(_.symbols)
    case sym: Sym => Seq(sym)
  }

  override def toString: String = {
    val sb = new StringBuilder
    def rec(e: SExpr): Unit = e match {
      case Atom(text) => sb ++= text
      case Sym(text, _) => sb ++= text
      case SList(items) =>
        sb += '('
        for ((item, i) <- items.zipWithIndex) {
          if (i > 0) sb += ' '
          rec(item)
        }
        sb += ')'
    }
    rec(this)
    sb.toString
  }
}

final case class Atom(text: String) extends SExpr
final case class SList(items: Seq[SExpr]) extends SExpr
/** A symbol of the solver's session, as the solver printed it, and what it stands for. */
final case class Sym(text: String, ref: Ref) extends SExpr

/** What a symbol of a solver's session stands for, in the Inox trees of the solver's program
  * (certificates are for programs of Inox trees). */
sealed trait Ref {
  /** What the symbol stands for, as a certificate prints it: its kind, then the identifier (with
    * its unique id), types and index that it has, as strings. */
  def describe: Seq[String] = {
    import inox.trees.PrinterOptions
    val opts = PrinterOptions(printUniqueIds = true)
    def tp(t: inox.trees.Type) = t.asString(using opts)
    this match {
      case Ref.Variable(v) => Seq("variable", v.id.uniqueName, tp(v.tpe))
      case Ref.Function(id, tps) => Seq("function", id.uniqueName) ++ tps.map(tp)
      case Ref.FirstOrder(id) => Seq("first-order", id.uniqueName)
      case Ref.Lambda(tpe) => Seq("application", tp(tpe))
      case Ref.Sort(tpe) => Seq("sort", tp(tpe))
      case Ref.Constructor(id, tpe) => Seq("constructor") ++ id.map(_.uniqueName) ++ Seq(tp(tpe))
      case Ref.Selector(id, tpe, index) => Seq("selector") ++ id.map(_.uniqueName) ++ Seq(tp(tpe), index.toString)
      case Ref.Tester(id, tpe) => Seq("tester") ++ id.map(_.uniqueName) ++ Seq(tp(tpe))
    }
  }
}
object Ref {
  import inox.trees as t

  final case class Variable(v: t.Variable) extends Ref
  /** A function, under its type arguments. */
  final case class Function(id: Identifier, tps: Seq[t.Type]) extends Ref
  /** An uninterpreted first-order function (see [[unrolling.Templates]]). */
  final case class FirstOrder(id: Identifier) extends Ref
  /** The application of functions of type `tpe`. */
  final case class Lambda(tpe: t.FunctionType) extends Ref
  final case class Sort(tpe: t.Type) extends Ref
  /** The constructor of type `tpe`, which is `id` for an ADT constructor (and the constructor of a
    * tuple, of a type parameter or of unit otherwise), and its selectors and tester. */
  final case class Constructor(id: Option[Identifier], tpe: t.Type) extends Ref
  final case class Selector(id: Option[Identifier], tpe: t.Type, index: Int) extends Ref
  final case class Tester(id: Option[Identifier], tpe: t.Type) extends Ref
}

object SExpr {
  /** The s-expressions of `text`, without its comments, or why it has none. */
  def parse(text: String): Either[String, Seq[SExpr]] = {
    var stack = List(scala.collection.mutable.ArrayBuffer[SExpr]())
    var i = 0
    val n = text.length
    def until(end: Char): Int = {
      val j = text.indexOf(end, i + 1)
      if (j < 0) throw new IllegalArgumentException(s"unterminated $end at $i") else j + 1
    }
    try {
      while (i < n) text(i) match {
        case c if c.isWhitespace => i += 1
        case ';' => i = { val j = text.indexOf('\n', i); if (j < 0) n else j + 1 }
        case '(' =>
          stack = scala.collection.mutable.ArrayBuffer[SExpr]() :: stack
          i += 1
        case ')' =>
          if (stack.tail.isEmpty) throw new IllegalArgumentException(s"unbalanced ) at $i")
          val items = stack.head.toSeq
          stack = stack.tail
          stack.head += SList(items)
          i += 1
        case '|' =>
          val start = i
          val j = until('|')
          stack.head += Atom(text.substring(start, j))
          i = j
        case '"' =>
          val start = i
          // a quote in a string is doubled
          var j = until('"')
          while (j < n && text(j) == '"') { i = j; j = until('"') }
          stack.head += Atom(text.substring(start, j))
          i = j
        case _ =>
          var j = i
          while (j < n && !text(j).isWhitespace && "();|\"".indexOf(text(j)) < 0) j += 1
          stack.head += Atom(text.substring(i, j))
          i = j
      }
      if (stack.tail.nonEmpty) Left("unbalanced (") else Right(stack.head.toSeq)
    } catch {
      case e: IllegalArgumentException => Left(e.getMessage)
    }
  }
}

/** The proof of an unsat answer (see [[SolverResponses.UnsatWithProof]]), which `toString` prints. */
sealed trait Proof

/** A solver's proof that `script` has no model: the commands that declare its symbols and assert
  * its clauses, and the solver's CPC proof, whose assumptions are the asserts of `script`:
  * {{{
  * (script
  * <the commands>
  * (check-sat)
  * )
  * (cpc
  * <the proof>
  * )
  * }}}
  */
final case class ScriptProof(script: Seq[SExpr], cpc: Seq[SExpr]) extends Proof {
  /** The asserted terms of the script, in order. */
  def asserts: Seq[SExpr] = script.collect { case SList(Seq(Atom("assert"), t)) => t }

  override def toString: String = Proof.block("script", script :+ SList(Seq(Atom("check-sat")))) + "\n" + Proof.block("cpc", cpc)
}

/** A template of a [[Certificate]]: the terms of its start blocker and arguments, and the indices
  * of the asserts of its clauses in the certificate's template script. */
final case class Template(params: Seq[SExpr], asserts: Seq[Int])

/** A rule of a [[Certificate]] (see [[unrolling.RuleKernel]]): its kind, the arguments that its
  * clauses are built from, the indices of the asserts of its clauses in the certificate's script,
  * and when it instantiates a template, the template's index and the values of the template's
  * symbols. */
final case class Rule(kind: String, arguments: Seq[Argument[SExpr]], instance: Option[Instance[SExpr]], asserts: Seq[Int])

/** An argument of a rule, by its name in the rule (see [[unrolling.RuleKernel.Rule.arguments]]). */
final case class Argument[T](name: String, terms: Seq[T])

/** An instance of the template of index `template`, with the values of its symbols. */
final case class Instance[T](template: Int, values: Seq[Value[T]])

/** The value of a template's symbol in an instance. */
final case class Value[T](symbol: T, value: T)

/** The assumptions of the check that a [[Certificate]] is for, as the indices of their asserts in
  * the certificate's script: those of the `query`, and those that state that an open conjunction
  * or disjunction is `complete` (see [[unrolling.OpenJunctions]]). */
final case class Assumptions(query: Seq[Int], complete: Seq[Int])

/** The certificate that the unrolling solver's query has no model: the underlying solver's
  * `proof`, whose asserts are the clauses that the solver asserted and then the assumptions of
  * its check, the rules that gave the clauses, and the templates that rules instantiate, whose
  * clauses `templateScript` declares and asserts (see [[Certificates.certificate]]). */
final case class Certificate(proof: ScriptProof, templateScript: Seq[SExpr], templates: Seq[Template],
                             rules: Seq[Rule], assumptions: Assumptions) extends Proof {
  /** What the symbols of the solver's session stand for, by their text and in its order. */
  def symbols: Seq[(String, Ref)] =
    (proof.script ++ templateScript ++ proof.cpc).flatMap(_.symbols).map(s => s.text -> s.ref).distinct.sortBy(_._1)

  override def toString: String = {
    def ints(is: Seq[Int]) = is.map(" " + _).mkString
    def string(s: String) = "\"" + s.replace("\"", "\"\"") + "\""
    val templateLines = templates.zipWithIndex.map { case (t, i) =>
      s"($i (params ${t.params.mkString(" ")})${ints(t.asserts)})"
    }
    val ruleLines = rules.map { case Rule(kind, arguments, instance, asserts) =>
      val args = arguments.map(a => s"(${a.name}${a.terms.map(" " + _).mkString})").mkString(" ")
      val inst = instance.map { case Instance(i, values) =>
        s" (instance $i (${values.map(v => s"(${v.symbol} ${v.value})").mkString(" ")}))"
      }.getOrElse("")
      s"($kind (args${if (args.isEmpty) "" else " " + args})$inst${ints(asserts)})"
    }
    val symbolLines = symbols.map { case (text, ref) =>
      val kind +: rest = ref.describe: @unchecked
      s"($text $kind${rest.map(" " + string(_)).mkString})"
    }
    s"(inox-certificate ${Certificate.version}\n" + Proof.block("script", proof.script :+ SList(Seq(Atom("check-sat")))) + "\n" +
      "(templates\n" + Proof.block("script", templateScript) + "\n" + templateLines.map(_ + "\n").mkString + ")\n" +
      "(rules\n" + ruleLines.map(_ + "\n").mkString + ")\n" +
      s"(assumptions (query${ints(assumptions.query)}) (complete${ints(assumptions.complete)}))\n" +
      "(symbols\n" + symbolLines.map(_ + "\n").mkString + ")\n" +
      Proof.block("cpc", proof.cpc) + ")"
  }
}

object Certificate {
  /** The version of the format that certificates print in, which changes with it. */
  val version = 1
}

object Proof {
  private[certificates] def block(name: String, es: Seq[Any]): String = s"($name\n${es.map(_.toString + "\n").mkString})"
}
