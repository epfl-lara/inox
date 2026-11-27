/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package certificates

import scala.annotation.unchecked.uncheckedVariance

/** Has the solvers that can produce proofs do so: the unrolling solver logs the rules that it
  * applies, and cvc5 runs with proofs. Proof production slows the solver down from its first
  * assertion, so that it is set only where proofs will be asked for: Inox sets it for an input
  * that asks for a proof (see [[Main]]). */
object optProduceProofs extends FlagOptionDef("produce-proofs", false)

object Certificates {
  /** What the unrolling solver checked in a refutation, in its terms `E`: the clauses that it
    * asserted and the assumptions of the check that answered unsat, in the order of the asserts
    * of the solver's session, the rules that gave the clauses, and the templates that they
    * instantiate, which a rule names by their index. */
  final case class Refutation[E](clauses: Seq[E], assumptions: Seq[Assumed[E]], templates: Seq[TemplateClauses[E]], rules: Seq[AppliedRule[E]],
                                 input: Option[Encoding[E]] = None)

  /** What relates the sources of a refutation to the input of the solver: the constraints that
    * were asserted, as terms of the program before the encoders `encoders`, which `printer`
    * prints, each with the term that the encoders make of it and the steps of the solver's
    * simplification of that term, the rule of each and the term after it, which lead to the
    * source of the template of the constraint, and as well, for each function that the sources
    * define, the call of the function on its parameters, its body after the encoders, and the
    * steps of the solver's simplification of that body, which lead to the body of its source
    * definition: those of the functions defined so far, which printing sources defines more of. */
  final case class Encoding[E](encoders: Seq[String], printer: Printer[E], constraints: Seq[(E, E, Seq[(String, E)])],
                               definitions: () => Seq[(E, E, Seq[(String, E)])] = () => Seq(),
                               functionEquality: String = "none")

  /** An assumption of the check, and whether it states that an open conjunction or disjunction
    * is complete, which refutations may assume (see [[unrolling.OpenJunctions]]), or is one of
    * the query. */
  final case class Assumed[E](assumption: E, complete: Boolean)

  /** A template: its start blocker and arguments, its clauses, and its source. */
  final case class TemplateClauses[E](params: Seq[E], clauses: Seq[E], source: Source[E])

  /** A rule that the solver applied (see [[unrolling.RuleKernel]]): its kind, its arguments, its
    * clauses, and when they are an instance of the clauses of a template, the instance. */
  final case class AppliedRule[E](kind: String, arguments: Seq[Argument[E]], instance: Option[Instance[E]], clauses: Seq[E])

  /** A solver whose session prints its terms, as the certificates of an unrolling solver over it
    * need for the terms that its session doesn't have. */
  trait CertificatePrinter { self: AbstractSolver =>
    /** The printer of the terms and sources of the session's certificates. */
    def certificatePrinter: Printer[Trees]
  }

  /** The printer of a certificate: of terms in the solver's session, and of the sources of
    * templates in Inox's SMT-LIB 3 syntax with the symbols of the session for their variables,
    * with the declarations that the sources make and the sorts of the symbols. The sources of a
    * session are those of one printer. */
  trait Printer[-E] {
    /** `es` as terms of the session, and the declarations of their symbols that printing them made. */
    def printTerms(es: Seq[E]): Printed

    /** `es` as sources, and the declarations of the session's symbols that printing them made. */
    def printSources(es: Seq[E]): Printed

    /** Has the printer define a function with the body that `body` gives, over the function's
      * parameters and type parameters, for the definitions that it hasn't printed yet: the body
      * that the solver unfolds (see [[Source.Definition]]). */
    def define(body: Identifier => E): Unit = ()

    /** The declarations and definitions that printing the sources and sorts made, in the
      * printer's syntax. */
    def declarations: Seq[SExpr]

    /** Gives the printer the steps of the simplification of the body of each function into the
      * body that it is defined with (see [[define]]): the rule of each step and the body after
      * it. */
    def defineSteps(steps: Identifier => Seq[(String, E)]): Unit = ()

    /** The body of each function that the printer defined, before the solver simplified it (the
      * body of the function in the solver's program), by the symbol of the function, and the
      * steps of its simplification (see [[defineSteps]]): terms over the parameters of the
      * definition, as the definition prints them. Printing them may define more functions, whose
      * original bodies are printed too. */
    def originals: Seq[(SExpr, SExpr, Seq[(String, SExpr)])] = Seq()
    /** The printer of the input of the session: of the terms of `program`, the program before
      * the encoders that give the session's, as sources, where the symbols of the identifiers
      * that the session's program keeps are those of this printer, and a variable `v` is the
      * variable `encode(v)` of the session. Its declarations are those of the input. None when
      * the printer prints no input, or not that of this program. */
    def input(program: Program, encode: (E @uncheckedVariance) => (E @uncheckedVariance)): Option[Printer[E]] = None

    /** The sort, as the printer of the sources prints it, of the type that a symbol stands for
      * when the symbol of the session that stands for an expression depends on its type: the
      * function type of an application, the type of a constructor, selector or tester, or of a
      * variable, and the sorts of the type arguments of a function, as a list. None for the
      * other symbols.
      *
      * Distinct types have distinct sorts: it fails when two types that it was asked for
      * print as the same sort (see [[DistinctSorts]]). */
    def sort(ref: Ref): Option[SExpr]
  }

  /** The types that sorts were printed for, by the text of their sort, which fails when two
    * distinct types print as the same sort: a checker picks the symbol of the session that a
    * symbol of the sources stands for by its sort. */
  final class DistinctSorts[T](show: T => String) {
    private val types = scala.collection.mutable.Map[String, T]()

    /** `text`, the sort of `tpe`. */
    def apply(text: String, tpe: T): String = {
      for (other <- types.get(text) if other != tpe)
        throw new IllegalStateException(s"the types ${show(other)} and ${show(tpe)} have the same sort $text")
      types(text) = tpe
      text
    }
  }

  /** Terms as the solver's session prints them, and the declarations that printing them made. */
  final case class Printed(terms: Seq[SExpr], declarations: Seq[SExpr])

  /** The certificate that a solver's session has no model, which the unrolling solver checked and
    * the solver proved with `proof`, where the asserts of the session are the clauses and then
    * the assumptions of `refutation`, or why there is none. There is none when a clause is the
    * clause of no rule, such as one of a template that was instantiated outside of a rule. It prints as:
    * {{{
    * (inox-certificate <version>
    * (script
    * <the SMT-LIB script that asserts the clauses, then the assumptions>
    * )
    * (templates
    * (script
    * <the SMT-LIB script that asserts the clauses of the templates, after the declarations of the script>
    * )
    * (<index> (params <its start blocker and arguments>) <its source> <the indices of the asserts of its clauses>)
    * ...)
    * (rules
    * (<kind> (args (<name> <term> ...) ...) <the indices of the asserts of its clauses>)
    * (<kind> (args ...) (instance <template index> ((<template symbol> <value>) ...)) <the indices>)
    * ...)
    * (assumptions (query <the indices of their asserts>) (complete <the indices of their asserts>))
    * (solver-symbols
    * (<symbol of the session> <kind> "<identifier, type or index>" ... [<sort>])
    * ...)
    * (source-definitions
    * <the declarations of the datatypes, with their invariants, and the definitions of the functions of the sources>
    * )
    * (source-symbols
    * (<symbol of the sources> <kind> "<identifier, type or index>" ... [<sort>])
    * ...)
    * (simplifications
    * <the original bodies and expressions that the solver simplified, and the steps that rewrite them>
    * )
    * (input
    * (encoders "<name>" ...)
    * (function-equality "<none, intensional or extensional>")
    * (definitions
    * <the declarations of the datatypes and the definitions of the functions of the input>
    * )
    * (constraint <a constraint of the input> (encoded <what the encoders make of it>))
    * ...
    * (symbols
    * (<symbol of the input> <kind> "<identifier, type or index>" ... [<sort>])
    * ...))
    * (cpc
    * <the solver's CPC proof that the script has no model>
    * ))
    * }}}
    * The source of a template is `(function <call> <body>)` for the template of a function, where
    * the body is the value of the call, or `(definition <call> [(names (<name> <subterm>) ...)])`
    * when that body is the one that the source definitions define the function with, at the
    * arguments of the call, where each named subterm is its name (see [[Source.Definition]]). It is
    * `(expression <term>)` for one of an expression that holds, such as the query. A source is
    * followed by `(where (<lhs> <rhs>) ...)` when the source names
    * markers or symbols of the template whose meanings it gives (see [[unrolling.TemplateGenerator.markers]]).
    * Every template has a source. Sources are terms of Inox's SMT-LIB 3 syntax (see
    * [[inox.smtlib3.Printer]]), with the `(assume <condition> <body>)` and `(error <sort> "<message>")` of Inox's expressions,
    * whose symbols are those of the printer and, for their variables, those of the session: the
    * source symbols say what they stand for. A marker of the sources is applied to its arguments
    * and qualified by the sort of the type that it is about, such as
    * `((as typing!0 <sort>) "<mode>" <value> <closures>)`. The source definitions are the commands
    * that printing the sources made: the declarations of the datatypes and uninterpreted
    * functions, and the definitions of the functions, with the bodies that the solver unfolds
    * (see [[Printer.define]]). The symbols of the session that depend on a type (see [[Printer.sort]]) and
    * the variables of the sources end with the SMT-LIB 3 sort of that type, as the printer of the
    * sources prints it, and a source prints each symbol whose symbol of the session depends on a
    * type under that sort, `(as <symbol> <sort>)`, so that a checker reads the symbol of the
    * session that it stands for from the tables.
    * The arguments of a rule are those that its clauses are built from, by name (see
    * [[unrolling.RuleKernel.Rule.arguments]]). The values of an instance's symbols are those of
    * the template's start blocker and arguments, then of the fresh symbols that replace its other
    * symbols. The symbols are those of the solver's session, with the Inox definition that each
    * one stands for (see [[Ref.describe]]). `printer` prints the terms in the solver's session, and
    * the sources with their declarations and sorts.
    *
    * The proof's assumptions are the script's asserts. Given the templates, a checker checks that
    * each rule is an instance of its kind, that its clauses are the asserts it names, that every
    * assert is named, and the proof (see `proofs/certificates`). */
  def certificate[E](proof: ScriptProof, refutation: Refutation[E], printer: Printer[E],
                     functionEquality: String = "none"): Either[String, Certificate] = {
    val Refutation(clauses, assumptions, templates, rules, encoding) = refutation
    val asserts = proof.asserts.size
    val ruled = rules.flatMap(_.clauses).toSet
    if (asserts != clauses.size + assumptions.size) {
      Left(s"the solver's session has $asserts asserts, for ${clauses.size} clauses and ${assumptions.size} assumptions")
    } else if (!clauses.forall(ruled)) {
      Left(s"clause ${clauses.indexWhere(c => !ruled(c))} of the solver's session is the clause of no rule")
    } else try {
      // a clause may be asserted several times
      val index = clauses.zipWithIndex.foldLeft(Map[E, Seq[Int]]()) {
        case (m, (e, i)) => m + (e -> (m.getOrElse(e, Seq()) :+ i))
      }
      def names(es: Seq[E]): Seq[Int] = es.flatMap(index).distinct

      // all terms are printed at once, along with the declarations that they need
      val values = rules.flatMap(_.instance.toSeq.flatMap(_.values))
      val Printed(terms, declarations) = printer.printTerms(templates.flatMap(t => t.params ++ t.clauses) ++
        values.flatMap(v => Seq(v.symbol, v.value)) ++ rules.flatMap(_.arguments.flatMap(_.terms)))
      val it = terms.iterator

      // a source is printed on its own, as it has expressions that the clauses don't
      val sessionDeclarations = scala.collection.mutable.ListBuffer[SExpr]()
      val sourceSeq = templates.map { t =>
        val Printed(terms, declarations) = printer.printSources(t.source.terms)
        sessionDeclarations ++= declarations
        val printed = terms.iterator
        t.source.map(_ => printed.next())
      }

      val templateAsserts = scala.collection.mutable.ListBuffer[SExpr]()
      val templateSeq = (templates zip sourceSeq).map { case (t, source) =>
        val ps = t.params.map(_ => it.next())
        val first = templateAsserts.size
        templateAsserts ++= t.clauses.map(_ => SList(Seq(Atom("assert"), it.next())))
        Template(ps, first until templateAsserts.size, source)
      }
      val instances = rules.map(_.instance.map(i => Instance(i.template, i.values.map(_ => Value(it.next(), it.next())))))
      val ruleSeq = (rules zip instances).map { case (r, instance) =>
        Rule(r.kind, r.arguments.map(a => Argument(a.name, a.terms.map(_ => it.next()))), instance, names(r.clauses))
      }
      val (complete, query) = (clauses.size until asserts).partition(i => assumptions(i - clauses.size).complete)
      val simplifications = simplified(sourceSeq, printer, functionEquality)
      // what the encoders make of the constraints of the input, and the steps of its
      // simplification, are sources
      val encoded = encoding.map { case Encoding(encoders, _, constraints, _, equality) =>
        val after = printer.printSources(constraints.map(_._2)).terms
        val steps = constraints.map(c => c._3.map(_._1) zip printer.printSources(c._3.map(_._2)).terms)
        Input(encoders, Seq(), (after zip steps).map { case (a, s) => Constraint(a, a, s) }, functionEquality = equality)
      }
      // the functions that the sources define, after those of `done`: printing a function may
      // define more of them, until the sources define them all
      def definitions(done: Seq[Constraint]): Seq[Constraint] = encoding.fold(done) { e =>
        Iterator.iterate(done.toVector) { done =>
          done ++ e.definitions().drop(done.size).map { (call, body, steps) =>
            val printed = printer.printSources(call +: body +: steps.map(_._2)).terms
            Constraint(printed(0), printed(1), steps.map(_._1) zip printed.drop(2))
          }
        }.sliding(2).collectFirst { case Seq(a, b) if a.size == b.size => b }.get
      }
      def withDefinitions(c: Certificate): Certificate =
        c.copy(input = c.input.map(in => in.copy(functions = definitions(in.functions))))
      val certificate = withDefinitions(Certificate(proof, declarations ++ sessionDeclarations ++ templateAsserts, templateSeq,
        ruleSeq, Assumptions(query, complete), simplifications = simplifications, input = encoded))
      // the sorts of the symbols, which may declare more datatypes in the printer, whose
      // declarations are then those of the sources: of the symbols of the session that depend on a
      // type, and of the variables and uninterpreted functions of the sources and definitions
      def sorts(refs: Seq[Ref]): Map[Ref, SExpr] = refs.distinct.flatMap(ref => printer.sort(ref).map(ref -> _)).toMap
      def ofSources(ref: Ref) = ref.isInstanceOf[Ref.Variable] || ref.isInstanceOf[Ref.Uninterpreted]
      val solverSorts = sorts(certificate.solverSymbols.map(_._2).filterNot(_.isInstanceOf[Ref.Variable]))
      // printing the sorts may define more functions (such as the equality of a sort), which may
      // have symbols with more sorts
      val (withSorts, sourceSorts) = Iterator.iterate((certificate, Map.empty[Ref, SExpr])) { (c, _) =>
        val sourceSorts = sorts(c.copy(sourceDefinitions = printer.declarations).sourceSymbols.map(_._2).filter(ofSources))
        (withDefinitions(c), sourceSorts)
      }.drop(1).sliding(2).collectFirst { case Seq(a, b) if a._1 == b._1 => b }.get
      // the input: its constraints are printed by its printer, whose declarations they make
      val input = encoding.map { case Encoding(encoders, inputPrinter, constraints, _, equality) =>
        val before = inputPrinter.printSources(constraints.map(_._1)).terms
        val in = Input(encoders, inputPrinter.declarations, (before zip encoded.get.constraints).map { case (b, c) => c.copy(input = b) },
          functions = withSorts.input.get.functions, functionEquality = equality)
        val inputSorts = in.symbols.map(_._2).filter(ofSources).distinct.flatMap(ref => inputPrinter.sort(ref).map(ref -> _)).toMap
        // the sorts may declare more datatypes
        in.copy(definitions = inputPrinter.declarations, sorts = inputSorts)
      }
      Right(withSorts.copy(sourceDefinitions = printer.declarations, solverSorts = solverSorts, sourceSorts = sourceSorts,
        input = input))
    } catch {
      case e: Throwable if !e.isInstanceOf[VirtualMachineError] =>
        Left(s"the certificate's terms or sources can't be printed in SMT-LIB (${e.getMessage})")
    }
  }

  /** The simplifications of a certificate whose templates have the sources `sources`, printed by
    * `printer`: for each function whose body the solver simplified, and for each expression
    * source that it simplified, the original and the steps that rewrite it into what the
    * certificate has, which the simplifiers recorded (see `transformers.TransformationRecorder`):
    * {{{
    * (function-equality <none, intensional or extensional>)
    * (function <symbol> <original body> <steps>)
    * (expression <template index> <original> (names (<name> <subterm>) ...) <steps>)
    * }}}
    * where `<steps>` is `(steps (<rule> <position> <subterm>) ...)`, the rule of each step, the
    * position of the subterm that it rewrites and what the subterm becomes. The rules are the
    * names that the simplifiers give to what they do: the checker checks those that it knows,
    * and reports the others. The body of a function is that of its definition, over the
    * parameters of the definition, and the simplified expression is that of the source, where
    * each name is the subterm that it names. The first entry is how the program compares
    * functions: the checker only checks steps when it doesn't (see `proofs/certificates`). */
  private def simplified[E](sources: Seq[Source[SExpr]], printer: Printer[E], functionEquality: String): Seq[SExpr] = {
    // A step is recorded as the whole term after it. The certificate only has what the step
    // rewrites: the position of the smallest subterm outside of which the term is the one before
    // the step, and that subterm after the step.
    def steps(original: SExpr, recorded: Seq[(String, SExpr)]): SExpr = {
      var current = original
      SList(Atom("steps") +: recorded.flatMap { (rule, term) =>
        if (term == current) None else {
          val position = difference(current, term)
          val subterm = position.foldLeft(term) { case (SList(items), i) => items(i); case (t, _) => t }
          current = term
          Some(SList(Seq(Atom(rule), SList(position.map(i => Atom(i.toString))), subterm)))
        }
      })
    }
    def difference(a: SExpr, b: SExpr): List[Int] = (a, b) match {
      case (SList(xs), SList(ys)) if xs.size == ys.size =>
        xs.indices.filter(i => xs(i) != ys(i)).toList match {
          case List(i) => i :: difference(xs(i), ys(i))
          case _ => Nil
        }
      case _ => Nil
    }
    val functions = printer.originals.collect {
      case (f, original, recorded) if recorded.exists(_._2 != original) =>
        SList(Seq(Atom("function"), f, original, steps(original, recorded)))
    }
    val expressions = sources.zipWithIndex.collect {
      case (Source.Expression(expr, _, Some(Source.Original(original, names, recorded))), i) =>
        val names_ = SList(Atom("names") +: names.map((n, t) => SList(Seq(n, t))))
        SList(Seq(Atom("expression"), Atom(i.toString), original, names_, steps(original, recorded)))
    }
    SList(Seq(Atom("function-equality"), Atom(functionEquality))) +: (functions ++ expressions)
  }

  /** The CPC proof that cvc5 answers to `(get-proof)`, or why it isn't one that checkers accept. */
  def cpc(answer: String): Either[String, Seq[SExpr]] = SExpr.parse(answer) match {
    case Left(why) => Left(s"cvc5's proof can't be read ($why)")
    case Right(Seq(SList(Atom("error") +: _))) => Left(s"cvc5 answered: ${answer.take(200)}")
    // cvc5 wraps the proof in parentheses, which the checkers don't accept
    case Right(Seq(SList(steps))) =>
      def trusted(step: SExpr): Boolean = step match {
        case SList(items) => items.sliding(2).exists { case Seq(Atom(":rule"), Atom("trust")) => true; case _ => false }
        case _ => false
      }
      if (steps.exists(trusted)) Left("cvc5's proof has trusted steps") else Right(steps)
    case _ => Left(s"cvc5 answered: ${answer.take(200)}")
  }
}
