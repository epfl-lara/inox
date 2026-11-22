/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package certificates

import java.nio.file.{Files, Paths}

/** Checks the certificates that Inox prints for its unsat answers (see `certificates/README.md`),
  * from their text alone: it shares no code with the solver.
  *
  * Given the templates, it checks that the rules account for the script that the proof refutes:
  *  - each rule is an instance of its kind, whose clauses, built from its arguments, are the
  *    asserts that it names. For a rule that instantiates a template, they are clauses of the
  *    template under the values of its symbols;
  *  - every assert of the script is a clause that a rule names, or an assumption;
  *  - each fresh symbol that a `Define`, `Hypothesis` or `Root` rule introduces is introduced once;
  *  - an assumption that an open conjunction or disjunction is complete is a literal;
  *  - the assumptions of the CPC proof are asserts of the script.
  *
  * It doesn't check the CPC proof, which Ethos does (see `check.sh`), nor that the templates are
  * those of the query and of its functions. */
object Checker {

  sealed trait SExpr
  final case class Atom(text: String) extends SExpr { override def toString: String = text }
  final case class SList(items: List[SExpr]) extends SExpr { override def toString: String = items.mkString("(", " ", ")") }

  final class Failure(msg: String) extends Exception(msg)
  private def fail(msg: String): Nothing = throw new Failure(msg)

  /** The s-expressions of `text`, whose atoms keep their text. */
  def parse(text: String): List[SExpr] = {
    var stack = List(List.newBuilder[SExpr])
    var i = 0
    val n = text.length
    def closing(end: Char): Int = {
      val j = text.indexOf(end, i + 1)
      if (j < 0) fail(s"unterminated $end at $i") else j + 1
    }
    while (i < n) text(i) match {
      case c if c.isWhitespace => i += 1
      case ';' => i = { val j = text.indexOf('\n', i); if (j < 0) n else j + 1 }
      case '(' => stack = List.newBuilder[SExpr] :: stack; i += 1
      case ')' =>
        if (stack.tail.isEmpty) fail(s"unbalanced ) at $i")
        val items = stack.head.result()
        stack = stack.tail
        stack.head += SList(items)
        i += 1
      case '|' =>
        val j = closing('|')
        stack.head += Atom(text.substring(i, j))
        i = j
      case '"' =>
        val start = i
        var j = closing('"')
        while (j < n && text(j) == '"') { i = j; j = closing('"') }
        stack.head += Atom(text.substring(start, j))
        i = j
      case _ =>
        var j = i
        while (j < n && !text(j).isWhitespace && "();|\"".indexOf(text(j)) < 0) j += 1
        stack.head += Atom(text.substring(i, j))
        i = j
    }
    if (stack.tail.nonEmpty) fail("unbalanced (")
    stack.head.result()
  }

  // Formulas

  private val True = Atom("true")
  private val False = Atom("false")

  private def app(op: String, args: SExpr*): SExpr = SList(Atom(op) :: args.toList)
  private def not(e: SExpr): SExpr = app("not", e)
  private def and(es: SExpr*): SExpr = app("and", es*)
  private def or(es: SExpr*): SExpr = app("or", es*)
  private def implies(l: SExpr, r: SExpr): SExpr = app("=>", l, r)
  private def equal(l: SExpr, r: SExpr): SExpr = app("=", l, r)

  /** A normal form of the propositional structure of `e`, which is equivalent to it: implications
    * are disjunctions, negations are on the atoms, conjunctions and disjunctions are flat, without
    * their units and repeated operands, and in the order of their text. The solver builds its
    * clauses with constructors that simplify them, which this doesn't depend on. */
  def normal(e: SExpr): SExpr = positive(e)

  private def junction(op: String, unit: Atom, zero: Atom, es: List[SExpr]): SExpr = {
    val flat = es.flatMap { case SList(Atom(`op`) :: inner) => inner; case other => List(other) }
    val operands = flat.filter(_ != unit).distinct.sortBy(_.toString)
    if (operands.contains(zero)) zero
    else operands match {
      case Nil => unit
      case List(one) => one
      case several => SList(Atom(op) :: several)
    }
  }

  private def positive(e: SExpr): SExpr = e match {
    // cvc5 prints the testers `((_ is C) e)` and `(is-C e)` as `(is C e)` in its proofs
    case SList(Atom(tester) :: args) if tester.startsWith("is-") => SList(Atom("is") :: Atom(tester.drop(3)) :: args.map(positive))
    case SList(SList(List(Atom("_"), Atom("is"), constructor)) :: args) => SList(Atom("is") :: constructor :: args.map(positive))
    case SList(List(Atom("not"), a)) => negative(a)
    case SList(Atom("and") :: es) => junction("and", True, False, es.map(positive))
    case SList(Atom("or") :: es) => junction("or", False, True, es.map(positive))
    case SList(Atom("=>") :: es) if es.size >= 2 => junction("or", False, True, es.init.map(negative) :+ positive(es.last))
    case SList(items) => SList(items.map(positive))
    case other => other
  }

  private def negative(e: SExpr): SExpr = e match {
    case True => False
    case False => True
    case SList(List(Atom("not"), a)) => positive(a)
    case SList(Atom("and") :: es) => junction("or", False, True, es.map(negative))
    case SList(Atom("or") :: es) => junction("and", True, False, es.map(negative))
    case SList(Atom("=>") :: es) if es.size >= 2 => junction("and", True, False, es.init.map(positive) :+ negative(es.last))
    case other => not(positive(other))
  }

  private def substitute(e: SExpr, subst: Map[SExpr, SExpr]): SExpr = subst.getOrElse(e, e match {
    case SList(items) => SList(items.map(substitute(_, subst)))
    case atom => atom
  })

  // Certificates

  private def asserts(script: List[SExpr]): Vector[SExpr] =
    script.collect { case SList(List(Atom("assert"), t)) => t }.toVector

  private def index(e: SExpr, bound: Int, what: String): Int = e match {
    case Atom(text) if text.nonEmpty && text.forall(_.isDigit) && text.toInt < bound => text.toInt
    case other => fail(s"$other is not the index of an assert of $what")
  }

  /** The arguments of a rule, by name. */
  private final class Arguments(kind: String, args: List[SExpr]) {
    private val byName: Map[String, List[SExpr]] = args.map {
      case SList(Atom(name) :: terms) => name -> terms
      case other => fail(s"$other is not an argument of a $kind rule")
    }.toMap
    if (byName.size != args.size) fail(s"a $kind rule has an argument twice")

    def has(name: String): Boolean = byName.contains(name)
    def opt(name: String): Option[SExpr] = byName.get(name).map {
      case List(term) => term
      case terms => fail(s"the argument $name of a $kind rule has ${terms.size} terms")
    }
    def one(name: String): SExpr = opt(name).getOrElse(fail(s"a $kind rule has no argument $name"))
    def several(name: String, size: Int = -1): List[SExpr] = byName.get(name) match {
      case Some(terms) if size < 0 || terms.size == size => terms
      case Some(terms) => fail(s"the argument $name of a $kind rule has ${terms.size} terms")
      case None => fail(s"a $kind rule has no argument $name")
    }
    /** Checks that the rule only has the arguments `names`. */
    def only(names: String*): Unit =
      for (name <- byName.keys if !names.contains(name)) fail(s"a $kind rule has no argument $name")
  }

  /** Checks that `application` applies `symbol` to `args`, where the session may apply it through
    * a function of its own. */
  private def checkApplication(application: SExpr, symbol: SExpr, args: List[SExpr]): Unit = application match {
    case SList(items) if items == symbol :: args || (items.nonEmpty && items.tail == symbol :: args) =>
    case other => fail(s"$other doesn't apply $symbol to ${args.mkString(", ")}")
  }

  /** The clauses of the rule of kind `kind` on `args`, for the rules that don't instantiate a
    * template (see `unrolling.RuleKernel` in Inox). */
  private def clauses(kind: String, args: Arguments): List[SExpr] = {
    import args._
    def guarded(guard: Option[SExpr], e: SExpr) = guard.fold(e)(implies(_, e))
    kind match {
      case "Define" =>
        only("guard", "literal", "value")
        List(guarded(opt("guard"), equal(one("literal"), one("value"))))
      case "Enables" =>
        only("blocker", "target")
        List(implies(one("blocker"), one("target")))
      case "Hypothesis" =>
        only("literal", "condition", "fact")
        List(implies(and(one("literal"), one("condition")), one("fact")))
      case "Root" =>
        only("start")
        List(one("start"))
      case "Typed" =>
        only("blocker", "typing")
        List(implies(one("blocker"), equal(one("typing"), True)))
      case "Holds" =>
        only("blocker", "quantification")
        List(implies(one("blocker"), one("quantification")))
      case "Unreachable" =>
        only("literal", "under")
        List(guarded(opt("under"), not(one("literal"))))
      case "Decreases" =>
        only("blocker", "decrease", "unless")
        List(implies(one("blocker"), opt("unless").fold(one("decrease"))(or(one("decrease"), _))))
      case "Congruence" =>
        only("premises", "result")
        List(implies(and(several("premises")*), one("result")))
      case "Witness" =>
        only("start", "differ", "failures")
        val distinguished = if (!has("failures")) one("differ") else {
          val List(err1, err2) = several("failures", 2): @unchecked
          or(not(equal(err1, err2)), and(not(err1), not(err2), one("differ")))
        }
        List(implies(one("start"), distinguished))
      case "Reflexivity" =>
        only("guard", "eq", "terms", "eq12")
        val List(e1, e2) = several("terms", 2): @unchecked
        checkApplication(one("eq12"), one("eq"), List(e1, e2))
        List(implies(opt("guard").fold(equal(e1, e2))(and(_, equal(e1, e2))), one("eq12")))
      case "Symmetry" =>
        only("blocker", "eq", "terms", "eq12", "eq21")
        val List(e1, e2) = several("terms", 2): @unchecked
        checkApplication(one("eq12"), one("eq"), List(e1, e2))
        checkApplication(one("eq21"), one("eq"), List(e2, e1))
        List(implies(one("blocker"), equal(one("eq12"), one("eq21"))))
      case "Transitivity" =>
        only("guard", "eq", "terms", "eq12", "eq23", "eq13")
        val List(e1, e2, e3) = several("terms", 3): @unchecked
        checkApplication(one("eq12"), one("eq"), List(e1, e2))
        checkApplication(one("eq23"), one("eq"), List(e2, e3))
        checkApplication(one("eq13"), one("eq"), List(e1, e3))
        List(implies(and(one("guard"), one("eq12"), one("eq23")), one("eq13")))
      case "Dispatched" =>
        only("blocker", "rest")
        List(implies(not(one("rest")), not(one("blocker"))))
      case "DispatchFailure" =>
        only("enabler", "application", "body")
        List(implies(one("enabler"), equal(one("application"), one("body"))))
      case "SameLambda" =>
        only("start", "lambda", "representative")
        List(implies(one("start"), equal(one("lambda"), one("representative"))))
      case "LambdaEquality" =>
        only("blocker", "lambdas", "closures", "intensional")
        val List(lambda1, lambda2) = several("lambdas", 2): @unchecked
        val equals = equal(lambda1, lambda2)
        (opt("closures"), has("intensional")) match {
          case (Some(eqs), true) => List(implies(one("blocker"), equal(eqs, equals)))
          case (None, true) => List(implies(one("blocker"), not(equals)))
          case (Some(eqs), false) => List(implies(and(one("blocker"), eqs), equals))
          case (None, false) => Nil
        }
      case other => fail(s"$other is not a kind of rule")
    }
  }

  /** The clauses of the rule of kind `kind` on the arguments `args`, each a list of its name and
    * terms as a certificate prints them. */
  def ruleClauses(kind: String, args: List[SExpr]): List[SExpr] = clauses(kind, new Arguments(kind, args))

  /** What a certificate has, once checked. */
  final case class Checked(asserts: Int, rules: Int, instances: Int, assumptions: Int, cpc: List[SExpr])

  /** Checks `certificate`, and fails with a [[Failure]] that says why when it doesn't hold. */
  def check(certificate: SExpr): Checked = certificate match {
    case SList(List(Atom("inox-certificate"), Atom(version),
      SList(Atom("script") :: script),
      SList(Atom("templates") :: SList(Atom("script") :: templateScript) :: templateLines),
      SList(Atom("rules") :: ruleLines),
      SList(List(Atom("assumptions"), SList(Atom("query") :: query), SList(Atom("complete") :: complete))),
      SList(Atom("symbols") :: symbols),
      SList(Atom("cpc") :: cpc))) =>

      if (version != "1") fail(s"the certificate has version $version, and the checker checks version 1")

      val clauses = asserts(script)
      val templateClauses = asserts(templateScript)

      val templates: Vector[(List[SExpr], Vector[SExpr])] = templateLines.zipWithIndex.map {
        case (SList(Atom(i) :: SList(Atom("params") :: params) :: indices), n) if i == n.toString =>
          if (params.distinct.size != params.size) fail(s"template $n has a parameter twice")
          (params, indices.map(i => templateClauses(index(i, templateClauses.size, "the templates"))).toVector)
        case (other, n) => fail(s"$other is not template $n")
      }.toVector

      val named = Array.fill(clauses.size)(false)
      // the symbols that the rules introduce, with the rule that does
      val introduced = scala.collection.mutable.Map[SExpr, String]()
      def introduce(symbol: SExpr, by: String): Unit = {
        if (!symbol.isInstanceOf[Atom]) fail(s"$symbol, which a $by rule introduces, is not a symbol")
        for (other <- introduced.get(symbol)) fail(s"$symbol is introduced by both a $other and a $by rule")
        introduced(symbol) = by
      }
      var instances = 0

      for (line <- ruleLines) line match {
        case SList(Atom(kind) :: SList(Atom("args") :: args) :: rest) =>
          val arguments = new Arguments(kind, args)
          val (instance, indices) = rest match {
            case SList(List(Atom("instance"), template, SList(values))) :: indices => (Some((template, values)), indices)
            case indices => (None, indices)
          }
          val is = indices.map(index(_, clauses.size, "the script"))
          if (is.isEmpty) fail(s"a $kind rule names no assert")
          is.foreach(named(_) = true)

          (kind, instance) match {
            case ("Unfold" | "Instance", Some((template, values))) =>
              if (kind == "Unfold") arguments.only("blocker", "failure")
              else {
                arguments.only("expression", "axiom", "counterexample")
                if (Seq("expression", "axiom", "counterexample").count(arguments.has) != 1) fail("an Instance rule is of one kind")
              }
              val (params, body) = templates(index(template, templates.size, "the templates"))
              val pairs = values.map {
                case SList(List(symbol, value)) => symbol -> value
                case other => fail(s"$other is not the value of a symbol")
              }
              if (pairs.map(_._1).distinct.size != pairs.size) fail(s"an instance gives a symbol two values")
              if (pairs.map(_._1).take(params.size) != params) fail(s"an instance doesn't give the values of its template's parameters first")
              // the template's other symbols are replaced by symbols of the instance
              for ((symbol, value) <- pairs.drop(params.size) if !symbol.isInstanceOf[Atom] || !value.isInstanceOf[Atom])
                fail(s"$symbol is replaced by $value, and they are not both symbols")
              val subst: Map[SExpr, SExpr] = pairs.toMap
              val instantiated = body.map(substitute(_, subst)).toSet
              val normalized = instantiated.map(normal)
              for (i <- is if !instantiated(clauses(i)) && !normalized(normal(clauses(i))))
                fail(s"assert $i, ${clauses(i)}, is not a clause of the instance that a $kind rule names")
              instances += 1

            case ("Unfold" | "Instance", None) => fail(s"a $kind rule has no instance")
            case (_, Some(_)) => fail(s"a $kind rule has an instance")

            case (_, None) =>
              val expected = Checker.clauses(kind, arguments).map(normal).toSet
              for (i <- is if !expected(normal(clauses(i))))
                fail(s"assert $i, ${clauses(i)}, is not a clause of the $kind rule that names it" +
                  expected.headOption.map(e => s" ($e)").getOrElse(""))
              kind match {
                case "Define" | "Hypothesis" => introduce(arguments.one("literal"), kind)
                case "Root" => introduce(arguments.one("start"), kind)
                case _ =>
              }
          }
        case other => fail(s"$other is not a rule")
      }

      val queryIndices = query.map(index(_, clauses.size, "the script"))
      val completeIndices = complete.map(index(_, clauses.size, "the script"))
      for (i <- queryIndices ++ completeIndices) {
        if (named(i)) fail(s"assert $i is both an assumption and the clause of a rule, or an assumption twice")
        named(i) = true
      }
      for (i <- completeIndices) clauses(i) match {
        case _: Atom | SList(List(Atom("not"), _: Atom)) =>
        case other => fail(s"the assumption $other doesn't state that an open conjunction or disjunction is complete")
      }
      for (i <- named.indices if !named(i)) fail(s"assert $i, ${clauses(i)}, is the clause of no rule and no assumption")

      for (line <- symbols) line match {
        case SList(Atom(_) :: Atom(_) :: described) if described.forall { case Atom(s) => s.startsWith("\""); case _ => false } =>
        case other => fail(s"$other doesn't describe a symbol")
      }

      // the proof refutes the script, where its definitions name terms
      val asserted = clauses.toSet
      val normalAsserted = asserted.map(normal)
      var definitions = Map[SExpr, SExpr]()
      for (step <- cpc) step match {
        case SList(List(Atom("define"), name: Atom, SList(Nil), term)) =>
          definitions += name -> substitute(term, definitions)
        case SList(List(Atom("assume"), _, formula)) =>
          val assumed = substitute(formula, definitions)
          if (!asserted(assumed) && !normalAsserted(normal(assumed))) fail(s"the proof assumes $assumed, which the script doesn't assert")
        case _ =>
      }

      Checked(clauses.size, ruleLines.size, instances, queryIndices.size + completeIndices.size, cpc)

    case SList(Atom("inox-certificate") :: Atom(version) :: _) if version != "1" =>
      fail(s"the certificate has version $version, and the checker checks version 1")
    case _ => fail("this is not a certificate")
  }

  /** The certificates of `text`, such as what Inox prints for a file: the s-expressions that start
    * a line with `(inox-certificate`, since Inox prints other lines there too. */
  def certificates(text: String): List[SExpr] = {
    val starts = Iterator.iterate(text.indexOf("(inox-certificate"))(i => text.indexOf("(inox-certificate", i + 1))
      .takeWhile(_ >= 0).filter(i => i == 0 || text(i - 1) == '\n').toList
    starts.map { start =>
      // the end of the s-expression
      var i = start
      var depth = 0
      while ({
        if (i >= text.length) fail("unbalanced (")
        text(i) match {
          case '(' => depth += 1
          case ')' => depth -= 1
          case '|' => i = text.indexOf('|', i + 1).max(i)
          case '"' => i = text.indexOf('"', i + 1).max(i)
          case _ =>
        }
        i += 1
        depth > 0
      }) ()
      parse(text.substring(start, i)).head
    }
  }

  /** Checks the certificates of each file, and with `--cpc <dir>`, writes their CPC proofs to
    * `<dir>/<file>.<n>.cpc` for a CPC checker. Exits with 1 unless every certificate holds. */
  def main(args: Array[String]): Unit = {
    val (cpcDir, files) = args.toList match {
      case "--cpc" :: dir :: files => (Some(Paths.get(dir)), files)
      case files => (None, files)
    }
    if (files.isEmpty) {
      Console.err.println("usage: Checker [--cpc <dir>] <file>...")
      sys.exit(2)
    }
    cpcDir.foreach(Files.createDirectories(_))
    var failed = false
    var total = 0
    for (file <- files) {
      val path = Paths.get(file)
      try {
        for ((certificate, n) <- certificates(Files.readString(path)).zipWithIndex) {
          total += 1
          try {
            val checked = check(certificate)
            println(s"ok   $file ${n + 1}: ${checked.asserts} asserts, ${checked.rules} rules, ${checked.instances} instances")
            for (dir <- cpcDir)
              Files.writeString(dir.resolve(s"${path.getFileName}.${n + 1}.cpc"), checked.cpc.map(_.toString + "\n").mkString)
          } catch {
            case e: Failure => failed = true; println(s"FAIL $file ${n + 1}: ${e.getMessage}")
          }
        }
      } catch {
        case e: Failure => failed = true; println(s"FAIL $file: ${e.getMessage}")
      }
    }
    println(s"$total certificates" + (if (failed) ", not all of which hold" else ", which all hold"))
    if (failed) sys.exit(1)
  }
}
