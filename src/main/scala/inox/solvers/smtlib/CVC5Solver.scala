/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import inox.OptionParsers._

import _root_.smtlib.trees.Terms.SExpr
import _root_.smtlib.trees.Commands._
import _root_.smtlib.printer.RecursivePrinter
import scala.collection.mutable.ListBuffer

object optCVC5Options extends SetOptionDef[String] {
  val name = "solver:cvc5"
  val default = Set[String]()
  val elementParser = stringParser
  val usageRhs = "<cvc5-opt>"
}

// In millions of cvc5 resource units
// An Int, so that the limit in resource units can't overflow the Long it is computed in
object optCVC5Rlimit extends IntOptionDef("cvc5-rlimit", -1, "<N>")

trait CVC5Solver extends CVCSolver with CVC5Target with certificates.Certificates.CertificatePrinter {
  import context.{given, _}
  import program.trees._
  import SolverResponses._

  override def optCVCOptions: SetOptionDef[String] = optCVC5Options

  // certificates are for programs of Inox trees (see `certificates.Ref`)
  private lazy val producesProofs: Boolean =
    options.findOptionOrDefault(certificates.optProduceProofs) && (program.trees eq inox.trees)

  override def interpreterOpts = {
    val rlimit = options.findOptionOrDefault(optCVC5Rlimit).toLong * 1000000L
    // cvc5 1.4 refuses constant arrays, which Inox's maps and bags use, without `--arrays-exp`
    super.interpreterOpts ++ Seq("--arrays-exp") ++
      (if (rlimit >= 0) Seq(s"--rlimit-per=$rlimit") else Seq()) ++
      (if (producesProofs) Seq("--produce-proofs", "--proof-format-mode=cpc") else Seq())
  }

  // With proofs, the commands of the session that declare symbols and assert clauses, in each of
  // its scopes (innermost first), and those that `printed` records. They are left uninitialized
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
    if (!producesProofs && options.findOptionOrDefault(certificates.optProduceProofs))
      Left("certificates are for programs of Inox trees")
    else if (!producesProofs) Left("the solver does not produce proofs")
    else try interpreter match {
      case _: PipelinedInterpreter if version.exists(Ordering[(Int, Int)].lt(_, minimumVersion)) =>
        val (major, minor) = version.get
        val (minMajor, minMinor) = minimumVersion
        Left(s"certificates need cvc5 $minMajor.$minMinor or later, and the solver is cvc5 $major.$minor")
      case pipelined: PipelinedInterpreter =>
        val table = sessionSymbols
        val commands = scopes.reverse.flatten.map(proofSExpr(_, table))
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
  def printed(es: Seq[Expr]): certificates.Certificates.Printed = {
    val commands = ListBuffer.empty[SExpr]
    declared = commands
    try {
      val terms = es.map(e => toSMT(e)(using Map()))
      // the symbols are known once the terms are translated
      val table = sessionSymbols
      certificates.Certificates.Printed(terms.map(proofSExpr(_, table)), commands.toSeq.map(proofSExpr(_, table)))
    } finally declared = null
  }

  /** `e` as an s-expression of a proof, as the session prints it. */
  private def proofSExpr(e: SExpr, table: Map[String, certificates.Ref]): certificates.SExpr =
    certificates.SExpr.parse(RecursivePrinter.toString(e)) match {
      case Right(Seq(sexpr)) => sexpr.resolve(table.get)
      case other => throw new IllegalStateException(s"${RecursivePrinter.toString(e)} isn't one s-expression: $other")
    }

  /** What the symbols of the session stand for, by name. */
  private def sessionSymbols: Map[String, certificates.Ref] = {
    import certificates.Ref
    // the program's trees are Inox trees (see `producesProofs`)
    def tpe(t: Type): inox.trees.Type = t.asInstanceOf[inox.trees.Type]
    def variable(v: Variable): inox.trees.Variable = v.asInstanceOf[inox.trees.Variable]
    def cons(c: ConsType): Option[Identifier] = c match {
      case ADTCons(id, _) => Some(id)
      case _ => None
    }
    def sym[A](b: utils.Bijection[A, _root_.smtlib.trees.Terms.SSymbol])(ref: A => Ref) = b.iterator.map { case (a, s) => s.name -> ref(a) }
    // several types may have the same sort, such as the functions, which are integers
    val sortRefs = sorts.iterator.collect { case (t, _root_.smtlib.trees.Terms.Sort(id, Seq())) => id.symbol.name -> Ref.Sort(tpe(t)) }
      .toSeq.groupBy(_._1).collect { case (_, Seq(one)) => one }
    (sortRefs.iterator ++
      sym(constructors)(c => Ref.Constructor(cons(c), tpe(c.getType))) ++
      sym(selectors) { case (c, i) => Ref.Selector(cons(c), tpe(c.getType), i) } ++
      sym(testers)(c => Ref.Tester(cons(c), tpe(c.getType))) ++
      sym(functions)(tfd => Ref.Function(tfd.id, tfd.tps.map(tpe))) ++
      sym(firstOrderFunctions)(Ref.Uninterpreted(_)) ++
      sym(lambdas)(ft => Ref.Lambda(ft.asInstanceOf[inox.trees.FunctionType])) ++
      sym(predicates)(v => Ref.Variable(variable(v))) ++
      sym(variables)(v => Ref.Variable(variable(v)))).toMap
  }

  // cvc5 only starts spending on the assertions of a check once it runs it, so that a check is
  // charged all that was spent since the previous one
  override protected def resourcesSinceLastCheck: Boolean = true

  override protected def resourceCount(): Option[Long] = interpreter match {
    case cvc5: PipelinedCVC5Interpreter => cvc5.resourceUnitsUsed()
    case _ => None
  }

  // Under `--strings-bmp`, restrict the string alphabet to the BMP (by default, cvc5 uses all
  // 0x30000 SMT-LIB characters).
  override protected def targetOpts: Seq[String] =
    if (maxStringChar == 0xFFFF) Seq("--strings-alpha-card=65536") else Seq.empty
}
