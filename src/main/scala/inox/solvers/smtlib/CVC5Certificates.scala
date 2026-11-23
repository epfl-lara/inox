/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.trees.Terms.{SExpr, SSymbol, Sort, Term, QualifiedIdentifier, Identifier => SMTIdentifier}
import _root_.smtlib.trees.Commands._
import _root_.smtlib.printer.RecursivePrinter
import scala.collection.mutable.ListBuffer

/** A cvc5 solver for a program of Inox trees, which answers an unsat check with its proof and
  * prints the terms of certificates (see [[certificates.Certificates.CertificatePrinter]]):
  * certificates are for programs of Inox trees (see [[certificates.Ref]]). */
trait CVC5Certificates extends CVC5Solver with SymbolRefs with certificates.Certificates.CertificatePrinter {
  self: SMTLIBSolver { val program: InoxProgram } =>

  import context.{given, _}
  import program.trees._
  import SolverResponses._

  private lazy val producesProofs: Boolean = options.findOptionOrDefault(certificates.optProduceProofs)

  override def interpreterOpts =
    super.interpreterOpts ++ (if (producesProofs) Seq("--produce-proofs", "--proof-format-mode=cpc") else Seq())


  // With proofs, the commands of the session that declare symbols and assert clauses, in each of
  // its scopes (innermost first), and those that `printing` records. They are left uninitialized
  // since the session starts with a command while the solver is constructed (see `initialize`).
  private var scopes: List[ListBuffer[SExpr]] = scala.compiletime.uninitialized
  private var declared: ListBuffer[SExpr] = scala.compiletime.uninitialized

  override def emit(cmd: SExpr, rawOut: Boolean = false): SExpr = {
    val res = super.emit(cmd, rawOut)
    if (scopes == null) scopes = List(ListBuffer.empty)
    if (producesProofs) cmd match {
      case Push(n) => for (_ <- 1 to n) scopes = ListBuffer.empty[SExpr] :: scopes
      case Pop(n) => scopes = scopes.drop(n.min(scopes.size - 1))
      case Reset() => scopes = List(ListBuffer.empty)
      case _: SetLogic | _: DeclareConst | _: DeclareDatatypes | _: DeclareFun | _: DeclareSort | _: DefineFun |
           _: DefineFunRec | _: DefineFunsRec | _: DefineSort | _: Assert =>
        scopes.head += cmd
        if (declared != null) declared += cmd
      case _ =>
    }
    res
  }

  /** Under a configuration with proofs, an unsat answer comes with the proof of the session. */
  override def check(config: CheckConfiguration): config.Response[Model, Assumptions] =
    config.cast((super.check(config): SolverResponse[Model, Assumptions]) match {
      case _: Unsatisfiable if config.withProof => UnsatWithProof(proof())
      case res => res
    })

  /** With proofs, the commands of the session, which declare its symbols and assert its clauses,
    * and cvc5's CPC proof that they have no model, after an unsat check:
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
  private def proof(): Either[String, certificates.Proof] = {
    if (!producesProofs) Left("the solver does not produce proofs")
    else try interpreter match {
      case _: PipelinedInterpreter if version.exists(Ordering[(Int, Int)].lt(_, minimumVersion)) =>
        val (major, minor) = version.get
        val (minMajor, minMinor) = minimumVersion
        Left(s"certificates need cvc5 $minMajor.$minMinor or later, and the solver is cvc5 $major.$minor")
      case pipelined: PipelinedInterpreter =>
        val table = symbolRefs
        val commands = scopes.reverse.flatten.map(c => proofSExpr(RecursivePrinter.toString(c), table))
        certificates.Certificates.cpc(pipelined.raw("(get-proof)"))
          .map(steps => certificates.ScriptProof(commands, steps.map(_.resolve(table.get))))
      case _ => Left("the solver can't be asked for its proof")
    } catch {
      case e: java.io.IOException => Left(s"cvc5 gave no proof (${e.getMessage})")
    }
  }

  // the oldest cvc5 whose proofs the CPC signature of the checkers (cvc5 1.4) accepts
  private val minimumVersion = (1, 4)

  // the session's cvc5 version, as (major, minor)
  private lazy val version: Option[(Int, Int)] = interpreter match {
    case pipelined: PipelinedInterpreter =>
      certificates.SExpr.parse(pipelined.raw("(get-info :version)")) match {
        case Right(Seq(certificates.SList(Seq(certificates.Atom(":version"), certificates.Atom(text))))) =>
          """(\d+)\.(\d+)""".r.findFirstMatchIn(text).map(m => (m.group(1).toInt, m.group(2).toInt))
        case _ => None
      }
    case _ => None
  }

  /** `es` as terms of the session, and the declarations of their symbols that printing them made. */
  def printedTerms(es: Seq[Expr]): certificates.Certificates.Printed = printing {
    val terms = es.map(e => toSMT(e)(using Map()))
    // the symbols are known once the terms are translated
    (terms.map(RecursivePrinter.toString), symbolRefs)
  }

  /** `es` as the sources of templates (see [[certificates.Certificates.CertificatePrinter]]), and
    * the declarations of the session's symbols that printing them made: Inox's SMT-LIB 3 printer
    * prints them, where their variables are those of the session. */
  def printedSources(es: Seq[Expr]): certificates.Certificates.Printed = printing {
    import certificates.Ref
    val free = es.flatMap(exprOps.variablesOf).distinct
    val bindings = free.map(v => v.id -> toSMT(v)(using Map())).toMap
    val texts = es.map(e => sourcePrinter.termText(e, bindings))
    val variables = free.map(v => bindings(v.id) match {
      case QualifiedIdentifier(SMTIdentifier(s, Seq()), None) => s.name -> Ref.Variable(v)
      case term => throw new IllegalStateException(s"the session's variable ${v.id} is the term $term")
    })
    val symbols = sourcePrinter.symbolRefs
    for ((name, ref) <- variables if symbols.get(name).exists(_ != ref))
      throw new IllegalStateException(s"$name is a symbol of the printer and a variable of the session")
    (texts, symbols ++ variables)
  }

  // The printer of the sources names identifiers as the session does, so that a name of a source
  // stands for one identifier. Its definitions and declarations aren't printed: the symbols of a
  // source are those of the printer and the variables of the session, which the session declares.
  private lazy val sourcePrinter = new SourcePrinter(symbolNames)

  private class SourcePrinter(names: SymbolNames)
    extends inox.smtlib3.Printer(program, context, java.io.Writer.nullWriter()) with SymbolRefs {
    override protected def symbolNames = names

    /** `e` as the text of a term, where the variables that `bindings` binds are their terms. */
    def termText(e: Expr, bindings: Map[Identifier, Term]): String = {
      val writer = new java.io.StringWriter
      printingContext(writer).output(toSMT(e)(using bindings))
      writer.toString
    }

    /** What the symbols that the printer printed stand for, by name: those of the target, the
      * variables that the printer declared, the functions of the uninterpreted calls, and the
      * datatypes with type parameters, whose sorts are applied to the sorts of their arguments. */
    override def symbolRefs: Map[String, certificates.Ref] = {
      import certificates.Ref
      val generic = sorts.iterator.collect { case (t: ADTType, Sort(id, _ +: _)) => id.symbol.name -> Ref.Sort(t) }
      super.symbolRefs ++ generic ++
        extraVars.iterator.map { case (v, s) => s.name -> Ref.Variable(v) } ++
        uninterpreted.iterator.map { case ((id, _), s) => s.name -> Ref.Uninterpreted(id) }
    }
  }

  /** The terms whose texts `print` gives, with what their symbols stand for, and the commands
    * of the session that declare symbols while it prints them. */
  private def printing(print: => (Seq[String], Map[String, certificates.Ref])): certificates.Certificates.Printed = {
    val commands = ListBuffer.empty[SExpr]
    declared = commands
    try {
      val (texts, table) = print
      certificates.Certificates.Printed(texts.map(proofSExpr(_, table)),
        commands.toSeq.map(c => proofSExpr(RecursivePrinter.toString(c), symbolRefs)))
    } finally declared = null
  }

  /** The text `text` of the session or of the sources as an s-expression of a proof. */
  private def proofSExpr(text: String, table: Map[String, certificates.Ref]): certificates.SExpr =
    certificates.SExpr.parse(text) match {
      case Right(Seq(sexpr)) => sexpr.resolve(table.get)
      case other => throw new IllegalStateException(s"$text isn't one s-expression: $other")
    }
}

/** What the symbols of a target for a program of Inox trees stand for, in the trees that
  * certificates are for (see [[certificates.Ref]]): the session and the printer of the sources
  * are such targets. */
private trait SymbolRefs extends SMTLIBTarget { self: SMTLIBTarget { val program: InoxProgram } =>
  import program.trees._

  /** What the symbols of the target stand for, by name. */
  def symbolRefs: Map[String, certificates.Ref] = {
    import certificates.Ref
    def cons(c: ConsType): Option[Identifier] = c match {
      case ADTCons(id, _) => Some(id)
      case _ => None
    }
    def sym[A](b: utils.Bijection[A, SSymbol])(ref: A => Ref) = b.iterator.map { case (a, s) => s.name -> ref(a) }
    // several types may have the same sort, such as the functions, which are integers
    val sortRefs = sorts.iterator.collect { case (t, Sort(id, Seq())) => id.symbol.name -> Ref.Sort(t) }
      .toSeq.groupBy(_._1).collect { case (_, Seq(one)) => one }
    (sortRefs.iterator ++
      sym(constructors)(c => Ref.Constructor(cons(c), c.getType)) ++
      sym(selectors) { case (c, i) => Ref.Selector(cons(c), c.getType, i) } ++
      sym(testers)(c => Ref.Tester(cons(c), c.getType)) ++
      sym(functions)(tfd => Ref.Function(tfd.id, tfd.tps)) ++
      sym(firstOrderFunctions)(Ref.Uninterpreted(_)) ++
      sym(lambdas)(Ref.Lambda(_)) ++
      sym(predicates)(Ref.Variable(_)) ++
      sym(variables)(Ref.Variable(_))).toMap
  }
}
