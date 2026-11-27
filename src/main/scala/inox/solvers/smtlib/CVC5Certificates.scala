/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.trees.Terms.{SExpr, SSymbol, Sort, SortedVar, Term, FunctionApplication, QualifiedIdentifier, Identifier => SMTIdentifier}
import _root_.smtlib.trees.Commands._
import _root_.smtlib.extensions.tip.Commands._
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
  private def printTerms(es: Seq[Expr]): certificates.Certificates.Printed = printing {
    val terms = es.map(e => toSMT(e)(using Map()))
    // the symbols are known once the terms are translated
    (terms.map(RecursivePrinter.toString), symbolRefs)
  }

  lazy val certificatePrinter: certificates.Certificates.Printer[Expr] = new SourcePrinter(symbolNames)

  /** The printer of the sources of templates: Inox's SMT-LIB 3 printer, which names identifiers
    * as the session does, so that a name of a source stands for one identifier, and where the
    * variables of the sources are those of the session. Its definitions and declarations aren't
    * printed: the symbols of a source are those of the printer and the variables of the session,
    * which the session declares. It prints the markers of sources (see [[unrolling.TemplateGenerator.markers]])
    * as their symbol, qualified by the sort of the type they are about, and applied to their
    * arguments:
    * {{{
    * ((as typing!0 <sort>) "<mode>" <value> <closures>)
    * ((as reads!0 <sort>) "<mode>" <collection> <closures>)
    * (as inhabited!0 <sort>)
    * }}}
    * It keeps the declarations and the definitions of functions that it prints, so that the
    * sources can be typed and the body of a function is printed once: it defines a function with
    * the body that the solver unfolds (see [[define]]). */
  private class SourcePrinter(names: SymbolNames)
    extends inox.smtlib3.Printer(program, context, java.io.Writer.nullWriter()) with SymbolRefs
      with certificates.Certificates.Printer[Expr] {
    import certificates.Ref

    def printTerms(es: Seq[Expr]): certificates.Certificates.Printed = CVC5Certificates.this.printTerms(es)

    override protected def symbolNames = names

    /** `e` as the text of a term, where the variables that `bindings` binds are their terms. */
    def termText(e: Expr, bindings: Map[Identifier, Term]): String = {
      val writer = new java.io.StringWriter
      printingContext(writer).output(toSMT(e)(using bindings))
      writer.toString
    }

    /** The text of the sort of `tpe`, whose variables are the terms that `bindings` binds. */
    private def sortText(tpe: Type, bindings: Map[Identifier, Term]): String = {
      val writer = new java.io.StringWriter
      printingContext(writer).output(sortOf(tpe)(using bindings))
      writer.toString
    }

    /** The symbol `head` under the sorts `key` that pick its symbol of the session, applied to
      * `args`: `((as head key) args)`, where the key is one sort, or a list of sorts. */
    private case class Keyed(head: Term, key: Seq[Sort], list: Boolean, args: Seq[Term]) extends _root_.smtlib.trees.Terms.TermExtension {
      override def print(ctx: _root_.smtlib.printer.PrintingContext): Unit = {
        if (args.nonEmpty) ctx.print("(")
        ctx.print("(as ")
        ctx.print(head)
        ctx.print(" ")
        if (list) ctx.printNary(key, (s: Sort) => ctx.print(s), "(", " ", ")") else ctx.print(key.head)
        ctx.print(")")
        args.foreach { a => ctx.print(" "); ctx.print(a) }
        if (args.nonEmpty) ctx.print(")")
      }
    }

    /** The term `t`, the symbol of the session of which depends on types, under their sorts. */
    private def keyed(t: Term, key: Seq[Sort], list: Boolean = false): Term = t match {
      case QualifiedIdentifier(id, _) => Keyed(QualifiedIdentifier(id), key, list, Seq())
      case FunctionApplication(QualifiedIdentifier(id, _), args) => Keyed(QualifiedIdentifier(id), key, list, args)
      case other => throw new IllegalStateException(s"$other has no symbol to key")
    }

    // The symbols whose symbol of the session depends on a type are printed under the sort that
    // picks it (see [[sort]]), so that a checker need not infer it: the datatype of a constructor,
    // selector or tester of a datatype with type parameters, the type arguments of a function,
    // the function type of an application, and the type of a tuple.
    override protected def toSMT(e: Expr)(using bindings: Map[Identifier, Term]): Term = {
      import program.symbols.given
      keyedSMT(e)
    }
    private def keyedSMT(e: Expr)(using bindings: Map[Identifier, Term], symbols: Symbols): Term = e match {
      case UninterpretedCall(id, Seq(tpe), args, _) if unrolling.TemplateGenerator.markers(id) =>
        val head = QualifiedIdentifier(SMTIdentifier(id2sym(id)), Some(sortOf(tpe)))
        if (args.isEmpty) head else FunctionApplication(head, args.map(toSMT))
      case UninterpretedCall(_, tps, _, _) if tps.nonEmpty => keyed(super.toSMT(e), tps.map(sortOf(_)), list = true)
      case FunctionInvocation(_, tps, _) if tps.nonEmpty => keyed(super.toSMT(e), tps.map(sortOf(_)), list = true)
      case adt @ ADT(_, tps, _) if tps.nonEmpty => keyed(super.toSMT(e), Seq(sortOf(adt.getType)))
      case s @ ADTSelector(_, _) if s.constructor.tps.nonEmpty =>
        keyed(super.toSMT(e), Seq(sortOf(ADTType(s.constructor.sort.id, s.constructor.tps))))
      case IsConstructor(v, _) => v.getType match {
        case tpe: ADTType if tpe.tps.nonEmpty => keyed(super.toSMT(e), Seq(sortOf(tpe)))
        case _ => super.toSMT(e)
      }
      case Application(caller, args) =>
        Keyed(QualifiedIdentifier(SMTIdentifier(SSymbol("@"))), Seq(sortOf(caller.getType)), false, (caller +: args).map(toSMT))
      case Tuple(_) => keyed(super.toSMT(e), Seq(sortOf(e.getType)))
      // the connectives are printed as they are, where the target drops their trivial operands:
      // a step of a simplification is told by the term that it gives
      case And(es) => FunctionApplication(QualifiedIdentifier(SMTIdentifier(SSymbol("and"))), es.map(toSMT))
      case Or(es) => FunctionApplication(QualifiedIdentifier(SMTIdentifier(SSymbol("or"))), es.map(toSMT))
      case TupleSelect(t, _) => keyed(super.toSMT(e), Seq(sortOf(t.getType)))
      case _ => super.toSMT(e)
    }

    /** What the symbols that the printer printed stand for, by name: those of the target, the
      * variables that the printer declared, the functions of the uninterpreted calls, the markers
      * of sources, and the datatypes with type parameters, whose sorts are applied to the sorts of
      * their arguments. */
    override def symbolRefs: Map[String, Ref] = {
      val generic = sorts.iterator.collect { case (t: ADTType, Sort(id, _ +: _)) => id.symbol.name -> Ref.Sort(t) }
      super.symbolRefs ++ generic ++
        extraVars.iterator.map { case (v, s) => s.name -> Ref.Variable(v) } ++
        uninterpreted.iterator.map { case ((id, tps), s) => s.name -> Ref.Uninterpreted(id, tps) } ++
        unrolling.TemplateGenerator.markers.map(id => id2sym(id).name -> Ref.Uninterpreted(id))
    }

    // the body that each function is defined with (see `define`), and the functions defined so far
    private var bodies: Option[Identifier => Expr] = None
    private val defined = ListBuffer.empty[FunDef]
    override def define(body: Identifier => Expr): Unit = bodies = Some(body)
    override protected def definitionBody(fd: FunDef): Expr = {
      defined += fd
      bodies.fold(fd.fullBody)(_(fd.id))
    }

    // the steps of the simplification of the body of each function (see `defineSteps`)
    private var steps: Option[Identifier => Seq[(String, Expr)]] = None
    override def defineSteps(steps: Identifier => Seq[(String, Expr)]): Unit = this.steps = Some(steps)

    // the original bodies printed so far, and the steps of their simplifications, by function
    private type Original = (certificates.SExpr, certificates.SExpr, Seq[(String, certificates.SExpr)])
    private val printedOriginals = scala.collection.mutable.LinkedHashMap[Identifier, Original]()

    override def originals: Seq[Original] = {
      // printing an original body, or a body between two steps, may define the functions that it calls
      while (defined.exists(fd => !printedOriginals.contains(fd.id))) {
        for (fd <- defined.toList if !printedOriginals.contains(fd.id)) {
          val (_, _, bindings) = signature(fd)
          def print(e: Expr): certificates.SExpr = proofSExpr(declaring(termText(e, bindings))._1, sourceSymbols)
          // without steps, the body that the function is defined with is one step from the original
          val recorded = steps.fold(Seq("unrecorded" -> bodies.fold(fd.fullBody)(_(fd.id))))(_(fd.id))
          printedOriginals(fd.id) = (proofSExpr(RecursivePrinter.toString(id2sym(fd.id)), sourceSymbols),
            print(fd.fullBody), recorded.map((rule, body) => rule -> print(body)))
        }
      }
      printedOriginals.values.toSeq
    }

    // the declarations and definitions that printing made: those of datatypes, sorts and functions
    private val kept = ListBuffer.empty[SExpr]

    override def emit(cmd: SExpr, rawOut: Boolean = false): SExpr = {
      cmd match {
        case _: DefineFun | _: DefineFunRec | _: DefineFunPar | _: DefineFunRecPar | _: DefineFunsRec | _: DefineFunsRecPar |
             _: DeclareDatatypes | _: DeclareDatatypesPar | _: inox.smtlib3.Commands.DeclareDatatypesWithPars |
             _: DeclareSort | _: DeclareFun | _: DeclareFunPar | _: DeclareConst | _: DeclareConstPar => kept += cmd
        case _ =>
      }
      super.emit(cmd, rawOut)
    }

    def printSources(es: Seq[Expr]): certificates.Certificates.Printed = printing {
      val bindings = sessionBindings(es.flatMap(exprOps.variablesOf).distinct)
      (es.map(termText(_, bindings)), sourceSymbols)
    }

    def declarations: Seq[certificates.SExpr] = kept.toSeq.map { d =>
      val writer = new java.io.StringWriter
      printingContext(writer).output(d)
      proofSExpr(writer.toString, sourceSymbols)
    }

    private val sorted = new certificates.Certificates.DistinctSorts[Type](_.asString(using PrinterOptions()))
    private def sortSExpr(tpe: Type): certificates.SExpr = {
      val (text, _) = declaring(sortText(tpe, sessionBindings(typeOps.variablesOf(tpe).toSeq.sortBy(_.id))))
      proofSExpr(sorted(text, tpe), sourceSymbols)
    }

    def sort(ref: Ref): Option[certificates.SExpr] = ref match {
      case Ref.Variable(v) => Some(sortSExpr(v.tpe))
      case Ref.Lambda(tpe) => Some(sortSExpr(tpe))
      case Ref.Constructor(_, tpe) => Some(sortSExpr(tpe))
      case Ref.Selector(_, tpe, _) => Some(sortSExpr(tpe))
      case Ref.Tester(_, tpe) => Some(sortSExpr(tpe))
      case Ref.Sort(tpe) => Some(sortSExpr(tpe))
      case Ref.Function(_, tps) => Some(certificates.SList(tps.map(sortSExpr)))
      case Ref.Uninterpreted(_, Seq()) => None
      case Ref.Uninterpreted(_, tps) => Some(certificates.SList(tps.map(sortSExpr)))
    }

    // the variables of the session that the sources and sorts have, by name
    private val sessionVariables = scala.collection.mutable.Map[String, Ref]()
    private def sourceSymbols: Map[String, Ref] = symbolRefs ++ sessionVariables

    /** The variables `vs` bound to their symbols in the session, which the session declares. */
    private def sessionBindings(vs: Seq[Variable]): Map[Identifier, Term] = vs.map { v =>
      val term = CVC5Certificates.this.toSMT(v)(using Map())
      term match {
        case QualifiedIdentifier(SMTIdentifier(s, Seq()), None) =>
          val ref = Ref.Variable(v)
          if (symbolRefs.get(s.name).exists(_ != ref))
            throw new IllegalStateException(s"${s.name} is a symbol of the printer and a variable of the session")
          sessionVariables(s.name) = ref
        case term => throw new IllegalStateException(s"the session's variable ${v.id} is the term $term")
      }
      v.id -> term
    }.toMap
  }

  /** The terms whose texts `print` gives, with what their symbols stand for, and the commands
    * of the session that declare symbols while it prints them. */
  private def printing(print: => (Seq[String], Map[String, certificates.Ref])): certificates.Certificates.Printed = {
    val ((texts, table), commands) = declaring(print)
    certificates.Certificates.Printed(texts.map(proofSExpr(_, table)),
      commands.map(c => proofSExpr(RecursivePrinter.toString(c), symbolRefs)))
  }

  /** `body`, and the commands of the session that declare symbols while it runs. */
  private def declaring[A](body: => A): (A, Seq[SExpr]) = {
    val commands = ListBuffer.empty[SExpr]
    declared = commands
    try (body, commands.toSeq) finally declared = null
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
