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
      case Ref.Uninterpreted(id, _) => Seq("uninterpreted", id.uniqueName)
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
  /** An uninterpreted function of the underlying solver (see [[unrolling.Templates]]), and for
    * one of the sources, the type arguments that it is the function of: each instantiation of
    * an uninterpreted function is a function of its own. */
  final case class Uninterpreted(id: Identifier, tps: Seq[t.Type] = Seq()) extends Ref
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
final case class Template(params: Seq[SExpr], asserts: Seq[Int], source: Source[SExpr])

/** What a template is of, in the terms `E` (see [[unrolling.Templates.templateSource]]), with the
  * meanings `where` of the symbols and markers that it names. It prints as a certificate has it. */
sealed abstract class Source[+E] {
  import Source._
  val where: Seq[(E, E)]

  /** The source whose terms are `f` of those of this one, which it is applied to in the order
    * of [[terms]]. */
  def map[F](f: E => F): Source[F] = {
    def pairs(ps: Seq[(E, E)]) = ps.map((l, r) => f(l) -> f(r))
    this match {
      case Expression(e, w, o) => { val expr = f(e); val where = pairs(w); Expression(expr, where, o.map(_.map(f))) }
      case Function(c, b, w) => { val call = f(c); Function(call, f(b), pairs(w)) }
      case Definition(c, ns, w) => { val call = f(c); Definition(call, pairs(ns), pairs(w)) }
    }
  }

  def terms: Seq[E] = {
    val terms = scala.collection.mutable.ListBuffer[E]()
    map(terms += _)
    terms.toSeq
  }

  override def toString: String = {
    def pairs(name: String, ps: Seq[(E, E)]) =
      if (ps.isEmpty) "" else ps.map((l, r) => s"($l $r)").mkString(s" ($name ", " ", ")")
    this match {
      case Expression(e, w, _) => s"(expression $e${pairs("where", w)})"
      case Function(c, b, w) => s"(function $c $b${pairs("where", w)})"
      case Definition(c, ns, w) => s"(definition $c${pairs("names", ns)}${pairs("where", w)})"
    }
  }
}

object Source {
  /** An expression that holds, whose clauses the template's are, and when the solver simplified
    * it, the expression before it did (see [[Original]]). The original doesn't print with the
    * source: the certificate's simplifications have it (see [[Certificates.certificate]]). */
  final case class Expression[+E](expr: E, where: Seq[(E, E)] = Seq(), original: Option[Original[E]] = None) extends Source[E]

  /** The expression `term` that the solver simplified into the expression of a source, where the
    * expression of the source names subterms of the simplified expression: each subterm that is
    * the right of a pair of `names` is the left of that pair in the source (as in a
    * [[Definition]]). */
  final case class Original[+E](term: E, names: Seq[(E, E)] = Seq(),
                                steps: Seq[(String, E)] = Seq()) {
    def map[F](f: E => F): Original[F] = {
      val t = f(term)
      val ns = names.map((l, r) => { val fl = f(l); fl -> f(r) })
      Original(t, ns, steps.map((rule, term) => rule -> f(term)))
    }
  }

  /** A function, a lambda or an evaluated call: the `call`, and the `body` that is its value. */
  final case class Function[+E](call: E, body: E, where: Seq[(E, E)] = Seq()) extends Source[E]

  /** A defined function: the `call`, whose value is the body that the certificate defines the
    * function with, at the type arguments and arguments of the call, where each subterm that is
    * the right of a pair of `names` is the left of that pair. */
  final case class Definition[+E](call: E, names: Seq[(E, E)] = Seq(), where: Seq[(E, E)] = Seq()) extends Source[E]
}

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

/** A constraint of the input of a solver, and what the encoders make of it, as sources. */
final case class Constraint(input: SExpr, encoded: SExpr)

/** The input of the solver of a [[Certificate]]: the names of the encoders that give the program
  * of the session from the program of the input, in their order (see
  * [[transformers.ProgramTransformer.encoders]]), the declarations of the datatypes and the
  * definitions of the functions of the input, as its printer made them, the constraints that
  * were asserted, and the sorts of the variables and uninterpreted functions of the input. */
final case class Input(encoders: Seq[String], definitions: Seq[SExpr], constraints: Seq[Constraint],
                       sorts: Map[Ref, SExpr] = Map()) {
  /** What the symbols of the input stand for, by their text and in its order: those of the
    * printer that printed it, and the variables of the session. */
  def symbols: Seq[(String, Ref)] =
    (definitions ++ constraints.map(_.input) ++ sorts.values).flatMap(_.symbols).map(s => s.text -> s.ref).distinct.sortBy(_._1)
}

/** The certificate that the unrolling solver's query has no model: the underlying solver's
  * `proof`, whose asserts are the clauses that the solver asserted and then the assumptions of
  * its check, the rules that gave the clauses, and the templates that rules instantiate, whose
  * clauses `templateScript` declares and asserts (see [[Certificates.certificate]]). */
final case class Certificate(proof: ScriptProof, templateScript: Seq[SExpr], templates: Seq[Template],
                             rules: Seq[Rule], assumptions: Assumptions, sourceDefinitions: Seq[SExpr] = Seq(),
                             solverSorts: Map[Ref, SExpr] = Map(), sourceSorts: Map[Ref, SExpr] = Map(),
                             simplifications: Seq[SExpr] = Seq(), input: Option[Input] = None) extends Proof {
  /** What the symbols of the solver's session stand for, by their text and in its order. */
  def solverSymbols: Seq[(String, Ref)] =
    (proof.script ++ templateScript ++ proof.cpc).flatMap(_.symbols).map(s => s.text -> s.ref).distinct.sortBy(_._1)

  /** What the symbols of the sources of the templates stand for, by their text and in its order:
    * those of the printer that printed them, and the variables of the session. */
  def sourceSymbols: Seq[(String, Ref)] =
    (templates.flatMap(_.source.terms) ++
      sourceDefinitions ++ sourceSorts.values ++ simplifications).flatMap(_.symbols).map(s => s.text -> s.ref).distinct.sortBy(_._1)

  override def toString: String = {
    def ints(is: Seq[Int]) = is.map(" " + _).mkString
    def string(s: String) = "\"" + s.replace("\"", "\"\"") + "\""
    val templateLines = templates.zipWithIndex.map { case (t, i) =>
      s"($i (params ${t.params.mkString(" ")}) ${t.source}${ints(t.asserts)})"
    }
    val ruleLines = rules.map { case Rule(kind, arguments, instance, asserts) =>
      val args = arguments.map(a => s"(${a.name}${a.terms.map(" " + _).mkString})").mkString(" ")
      val inst = instance.map { case Instance(i, values) =>
        s" (instance $i (${values.map(v => s"(${v.symbol} ${v.value})").mkString(" ")}))"
      }.getOrElse("")
      s"($kind (args${if (args.isEmpty) "" else " " + args})$inst${ints(asserts)})"
    }
    def symbolLines(symbols: Seq[(String, Ref)], sorts: Map[Ref, SExpr]) = symbols.map { case (text, ref) =>
      val kind +: rest = ref.describe: @unchecked
      s"($text $kind${rest.map(" " + string(_)).mkString}${sorts.get(ref).map(" " + _).getOrElse("")})"
    }
    s"(inox-certificate ${Certificate.version}\n" + Proof.block("script", proof.script :+ SList(Seq(Atom("check-sat")))) + "\n" +
      "(templates\n" + Proof.block("script", templateScript) + "\n" + templateLines.map(_ + "\n").mkString + ")\n" +
      "(rules\n" + ruleLines.map(_ + "\n").mkString + ")\n" +
      s"(assumptions (query${ints(assumptions.query)}) (complete${ints(assumptions.complete)}))\n" +
      "(solver-symbols\n" + symbolLines(solverSymbols, solverSorts).map(_ + "\n").mkString + ")\n" +
      Proof.block("source-definitions", sourceDefinitions) + "\n" +
      "(source-symbols\n" + symbolLines(sourceSymbols, sourceSorts).map(_ + "\n").mkString + ")\n" +
      Proof.block("simplifications", simplifications) + "\n" +
      input.map { in =>
        "(input\n(encoders" + in.encoders.map(" " + string(_)).mkString + ")\n" + Proof.block("definitions", in.definitions) + "\n" +
          in.constraints.map(c => s"(constraint ${c.input} (encoded ${c.encoded}))\n").mkString +
          "(symbols\n" + symbolLines(in.symbols, in.sorts).map(_ + "\n").mkString + "))\n"
      }.getOrElse("(input)\n") +
      Proof.block("cpc", proof.cpc) + ")"
  }
}

object Certificate {
  /** The version of the format that certificates print in, which changes with it. */
  val version = 5
}

object Proof {
  private[certificates] def block(name: String, es: Seq[Any]): String = s"($name\n${es.map(_.toString + "\n").mkString})"
}
