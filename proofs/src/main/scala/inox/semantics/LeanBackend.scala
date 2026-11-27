/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package semantics

/** Writes a [[Spec]] as Lean 4: one closed file, with an inductive type per datatype and a
  * definition per function, for proofs about the semantics. It uses core Lean only.
  *
  * Every definition is total. A function that quantifies over values is defined as written, with
  * classical decidability, so the definitions are noncomputable. Functions that call each other
  * form a `mutual` block, and Lean has to see that they terminate: `measures` gives the measure
  * of a function where Lean doesn't find one.
  *
  * A function that quantifies and is defined in terms of itself has no such measure. The file
  * declares an `Oracle` that gives these functions, and those of `assumed`, and the functions
  * that depend on them take the oracle as their first parameter. `Oracle.Sound` states that the
  * oracle satisfies their definitions.
  */
object LeanBackend {
  import Spec._

  private val keywords = Set(
    "abbrev", "at", "axiom", "by", "class", "def", "deriving", "do", "else", "end", "example",
    "export", "extends", "from", "fun", "have", "if", "import", "in", "inductive", "infix",
    "instance", "let", "local", "macro", "match", "mutual", "namespace", "notation", "of", "open",
    "private", "protected", "section", "set_option", "show", "structure", "syntax", "then",
    "theorem", "universe", "variable", "where", "with", "Type", "Prop", "Sort", "nomatch",
    "return", "for", "unless", "try", "catch", "finally", "mut", "using", "calc", "suffices",
    "obtain", "this", "termination_by", "decreasing_by", "partial", "unsafe", "opaque", "nofun")

  /** A variable, field or function name as a Lean identifier. */
  private def name(n: String): String = {
    val s = n.replace('-', '_')
    if (keywords(s)) s + "_" else s
  }

  /** The Lean names of the datatypes whose names Lean reserves. */
  private def typeName(n: String): String = n match {
    case "Type" => "Ty"
    case "Sort" => "ADTSort"
    case "Prop" => "Proposition"
    case _ => n
  }

  /** `List` and `Option`, when the semantics declares them as Lean does, are Lean's own. */
  private def isLeanList(dt: Datatype): Boolean = dt match {
    case Datatype("List", Seq(t), Seq(
      Constructor("Nil", Seq()),
      Constructor("Cons", Seq((_, Type.Param(a)), (_, Type.Named("List", Seq(Type.Param(b)))))))) =>
      a == t && b == t
    case _ => false
  }

  private def isLeanOption(dt: Datatype): Boolean = dt match {
    case Datatype("Option", Seq(t), Seq(
      Constructor("None", Seq()), Constructor("Some", Seq((_, Type.Param(a)))))) => a == t
    case _ => false
  }

  private def tpe(t: Type, atom: Boolean = false): String = t match {
    case Type.Named("Bool", Seq()) => "Bool"
    case Type.Named(n, Seq()) => typeName(n)
    case Type.Named(n, args) =>
      val s = args.map(tpe(_, atom = true)).mkString(s"${typeName(n)} ", " ", "")
      if (atom) s"($s)" else s
    case Type.Param(p) => p
  }

  private def params(t: Type): Seq[String] = t match {
    case Type.Named(_, args) => args.flatMap(params)
    case Type.Param(p) => Seq(p)
  }

  private def named(t: Type): Set[String] = t match {
    case Type.Named(n, args) => args.flatMap(named).toSet + n
    case Type.Param(_) => Set()
  }

  /** The strongly connected components of a graph, each after those it depends on, and otherwise
    * in the order of `nodes`. */
  private def components[A](nodes: Seq[A], deps: A => Seq[A]): Seq[Seq[A]] = {
    var index = 0
    val indices = scala.collection.mutable.Map[A, Int]()
    val low = scala.collection.mutable.Map[A, Int]()
    val stack = scala.collection.mutable.Stack[A]()
    val onStack = scala.collection.mutable.Set[A]()
    val res = Seq.newBuilder[Seq[A]]
    val order = nodes.zipWithIndex.toMap
    // an explicit stack: the call graph of the semantics is deep
    def visit(root: A): Unit = {
      val work = scala.collection.mutable.Stack[(A, Iterator[A])]()
      def enter(v: A): Unit = {
        indices(v) = index; low(v) = index; index += 1
        stack.push(v); onStack += v
        work.push((v, deps(v).filter(order.contains).iterator))
      }
      enter(root)
      while (work.nonEmpty) {
        val (v, it) = work.top
        if (it.hasNext) {
          val w = it.next()
          if (!indices.contains(w)) enter(w)
          else if (onStack(w)) low(v) = low(v) min indices(w)
        } else {
          work.pop()
          if (work.nonEmpty) { val (u, _) = work.top; low(u) = low(u) min low(v) }
          if (low(v) == indices(v)) {
            val comp = Seq.newBuilder[A]
            var w = stack.pop(); onStack -= w; comp += w
            while (w != v) { w = stack.pop(); onStack -= w; comp += w }
            res += comp.result().sortBy(order)
          }
        }
      }
    }
    for (n <- nodes if !indices.contains(n)) visit(n)
    res.result()
  }

  private def ind(n: Int) = "  " * n

  /** The `termination_by` and `decreasing_by` clauses of the functions of Inox's semantics for
    * which Lean needs them. */
  val measures: Map[String, String] = {
    val evalRank = Seq("eval" -> ("sizeOf e", 0), "eval-int" -> ("sizeOf e", 1), "eval-bool" -> ("sizeOf e", 1),
      "eval-bag" -> ("sizeOf e", 1), "eval-set" -> ("sizeOf e", 1), "eval-rm" -> ("sizeOf e", 1),
      "eval-string" -> ("sizeOf e", 1), "eval-list" -> ("sizeOf es", 0), "eval-or" -> ("sizeOf es", 0),
      "eval-and" -> ("sizeOf es", 0), "eval-map-entries" -> ("sizeOf es", 0),
      "eval-bag-entries" -> ("sizeOf es", 0), "call" -> ("0", 0), "apply" -> ("0", 0), "construct" -> ("0", 1))
    evalRank.map { case (f, (size, rank)) => f -> s"termination_by (fuel.toNat, $size, $rank)" }.toMap ++ Map(
      "gcd" -> "termination_by b.natAbs\ndecreasing_by\n  have := Int.emod_nonneg a _h\n  have := Int.emod_lt a _h\n  omega",
      "pow2" -> "termination_by n.toNat\ndecreasing_by omega",
      "bitlen" -> "termination_by n.toNat\ndecreasing_by omega",
      "bit-and" -> "termination_by a.toNat\ndecreasing_by omega",
      "bit-or" -> "termination_by a.toNat\ndecreasing_by omega",
      "bit-xor" -> "termination_by a.toNat\ndecreasing_by omega",
      "isqrt-from" -> "termination_by x.toNat\ndecreasing_by omega")
  }

  /** The functions of Inox's semantics whose termination Lean isn't shown yet: the oracle gives
    * them too, as the solutions of their equations. */
  val assumed: Set[String] = Set(
    "value-eq", "same-entries", "map-get", "sub-bag", "bag-get", "subset", "set-contains", "values-eq",
    "resolve", "resolve-params", "resolve-all",
    "has-type", "params-have-types", "sigma-has-type", "map-has-type", "bag-has-type", "all-have-type", "have-types")

  private class Writer(spec: Spec, measures: Map[String, String], assumed: Set[String]) {
    /** The functions that quantify and are defined in terms of themselves: an oracle gives them. */
    val oracle: Set[String] = {
      val groups = components[Function](spec.functions, f => calls(f).flatMap(spec.functionsByName.get))
      val recursive = groups.filter(g => g.size > 1 || calls(g.head).contains(g.head.name)).flatten.map(_.name).toSet
      (spec.noncomputable & recursive) ++ assumed
    }

    /** The functions that depend on the oracle, which they take as their first parameter. */
    val relative: Set[String] = {
      var res = Set[String]()
      var changed = true
      while (changed) {
        changed = false
        for (f <- spec.functions if !oracle(f.name) && !res(f.name) && calls(f).exists(g => oracle(g) || res(g))) {
          res += f.name; changed = true
        }
      }
      res
    }

    private val builtinLists = spec.datatypes.filter(isLeanList).map(_.name).toSet
    private val builtinOptions = spec.datatypes.filter(isLeanOption).map(_.name).toSet

    /** The constructors of `Result` other than `Ok`, with their numbers of fields, which `let!`
      * propagates. */
    private val outcomes: Seq[(String, Int)] =
      spec.datatypes.find(_.name == resultType).toSeq.flatMap(_.ctors.drop(1).map(c => (c.name, c.fields.size)))

    private def ctor(c: String): String = {
      val (dt, _) = spec.constructors.getOrElse(c, throw SpecError(s"no constructor $c"))
      if (builtinLists(dt.name)) (if (c == "Nil") "List.nil" else "List.cons")
      else if (builtinOptions(dt.name)) (if (c == "None") "Option.none" else "Option.some")
      else s"${typeName(dt.name)}.$c"
    }

    def datatype(dt: Datatype): String = {
      val tps = dt.tparams.map(t => s" ($t : Type)").mkString
      val self = (typeName(dt.name) +: dt.tparams).mkString(" ")
      val b = new StringBuilder
      b ++= s"inductive ${typeName(dt.name)}$tps : Type where\n"
      for (c <- dt.ctors) {
        val fields = c.fields.map { case (f, t) => s" (${name(f)} : ${tpe(t)})" }.mkString
        b ++= s"  | ${c.name}$fields : $self\n"
      }
      b.result()
    }

    private def pattern(p: Pattern): String = p match {
      case Pattern.Wildcard => "_"
      case Pattern.Bind(x) => name(x)
      case Pattern.BoolLit(v) => v.toString
      case Pattern.Ctor(c, Seq()) => ctor(c)
      case Pattern.Ctor(c, args) => args.map(pattern).mkString(s"(${ctor(c)} ", " ", ")")
    }

    /** A Boolean term as a proposition, for the condition of an `if`: a comparison stays one, so
      * that it is a hypothesis of each branch that arithmetic can use. */
    private def prop(t: Term, d: Int): String = t match {
      case Term.Builtin("<", Seq(a, b)) => s"${term(a, d)} < ${term(b, d)}"
      case Term.Builtin("<=", Seq(a, b)) => s"${term(a, d)} ≤ ${term(b, d)}"
      case Term.Builtin("=", Seq(a, b)) => s"${term(a, d)} = ${term(b, d)}"
      case Term.Builtin("not", Seq(a)) => s"¬ (${prop(a, d)})"
      case Term.Builtin("and", Seq(a, b)) => s"(${prop(a, d)}) ∧ (${prop(b, d)})"
      case Term.Builtin("or", Seq(a, b)) => s"(${prop(a, d)}) ∨ (${prop(b, d)})"
      case _ => s"${term(t, d)} = true"
    }

    private def term(t: Term, d: Int): String = t match {
      case Term.Var(x) => name(x)
      case Term.IntLit(v) => s"($v : Int)"
      case Term.BoolLit(v) => v.toString
      case Term.Ctor(c, Seq()) => ctor(c)
      case Term.Ctor(c, args) => args.map(term(_, d)).mkString(s"(${ctor(c)} ", " ", ")")
      case Term.Call(f, args) =>
        val head = if (oracle(f)) s"O.${name(f)}" else name(f)
        val all = (if (relative(f)) Seq("O") else Seq()) ++ args.map(term(_, d))
        if (all.isEmpty) head else all.mkString(s"($head ", " ", ")")
      case Term.Builtin("not", Seq(a)) => s"(!${term(a, d)})"
      case Term.Builtin(op, Seq(a, b)) =>
        val (x, y) = (term(a, d), term(b, d))
        op match {
          case "div" => s"($x / $y)"
          case "mod" => s"($x % $y)"
          case "and" => s"($x && $y)"
          case "or" => s"($x || $y)"
          case "=" => s"(decide ($x = $y))"
          case "<" => s"(decide ($x < $y))"
          case "<=" => s"(decide ($x ≤ $y))"
          case _ => s"($x $op $y)"
        }
      case Term.Builtin(op, _) => throw SpecError(s"arity of $op")
      case Term.Let(bs, body) if bs.isEmpty => term(body, d)
      case Term.Let(bs, body) =>
        val (x, v) = bs.head
        s"(let ${name(x)} := ${term(v, d + 1)}\n${ind(d)}${term(Term.Let(bs.tail, body), d)})"
      case Term.LetBang(bs, body) if bs.isEmpty => term(body, d)
      case Term.LetBang(bs, body) =>
        val ((x, v), rest) = (bs.head, bs.tail)
        s"(match ${term(v, d + 1)} with\n" +
        s"${ind(d)}| Result.Ok ${name(x)} =>\n${ind(d + 1)}${term(Term.LetBang(rest, body), d + 1)}\n" +
        outcomes.map { case (c, n) =>
          val fields = (0 until n).map(i => s" r$i").mkString
          s"${ind(d)}| Result.$c$fields => Result.$c$fields"
        }.mkString("\n") + ")"
      case Term.If(c, a, b) =>
        s"(if _h : ${prop(c, d + 1)} then\n${ind(d + 1)}${term(a, d + 1)}\n" +
        s"${ind(d)}else\n${ind(d + 1)}${term(b, d + 1)})"
      case Term.Quant(forall, binders, body) =>
        val bs = binders.map { case (x, t) => s"(${name(x)} : ${tpe(t)})" }.mkString(" ")
        s"(decide (${if (forall) "∀" else "∃"} $bs, ${term(body, d + 1)} = true))"
      case Term.Match(s, cases) =>
        val cs = cases.map { case (p, b) => s"${ind(d)}| ${pattern(p)} =>\n${ind(d + 1)}${term(b, d + 1)}" }
        s"(match ${term(s, d + 1)} with\n${cs.mkString("\n")})"
    }

    def calls(f: Function): Seq[String] = {
      def go(t: Term): Seq[String] = t match {
        case Term.Call(g, args) => g +: args.flatMap(go)
        case Term.Ctor(_, args) => args.flatMap(go)
        case Term.Builtin(_, args) => args.flatMap(go)
        case Term.Let(bs, b) => bs.flatMap(b => go(b._2)) ++ go(b)
        case Term.LetBang(bs, b) => bs.flatMap(b => go(b._2)) ++ go(b)
        case Term.If(c, a, b) => go(c) ++ go(a) ++ go(b)
        case Term.Match(s, cs) => go(s) ++ cs.flatMap(c => go(c._2))
        case Term.Quant(_, _, b) => go(b)
        case _ => Seq()
      }
      (f.body match {
        case Body.Term(t) => go(t)
        case Body.Cases(_, cs) => cs.flatMap(c => go(c._2))
      }).distinct
    }

    private def body(f: Function, d: Int): String = f.body match {
      case Body.Term(t) => s"${ind(d)}${term(t, d)}\n"
      case Body.Cases(x, cases) =>
        val cs = cases.map { case (p, b) => s"${ind(d)}| ${pattern(p)} =>\n${ind(d + 1)}${term(b, d + 1)}\n" }.mkString
        s"${ind(d)}match ${name(x)} with\n$cs"
    }

    def function(f: Function): String = {
      val tps = (f.params.flatMap(p => params(p._2)) ++ params(f.result)).distinct
      val tpsS = tps.map(t => s" {$t : Type}").mkString
      val o = if (relative(f.name)) " (O : Oracle)" else ""
      val ps = f.params.map { case (x, t) => s" (${name(x)} : ${tpe(t)})" }.mkString
      s"def ${name(f.name)}$tpsS$o$ps : ${tpe(f.result)} :=\n" + body(f, 1) +
      measures.get(f.name).map(m => m.linesIterator.map(l => s"$l\n").mkString).getOrElse("")
    }

    private def oracleFunctions: Seq[Function] = spec.functions.filter(f => oracle(f.name))

    /** The functions that the oracle gives. */
    def oracleStructure: String = {
      val b = new StringBuilder
      b ++= "/-- The functions of the semantics that quantify over values and are defined in terms of\n"
      b ++= "themselves, through the evaluation of the functions that values hold. Such a definition is no\n"
      b ++= "recursion that Lean accepts, so the semantics is relative to an oracle that gives them, and\n"
      b ++= "`Oracle.Sound` states that the oracle gives them as the semantics defines them. -/\n"
      b ++= "structure Oracle : Type where\n"
      for (f <- oracleFunctions) {
        if ((f.params.flatMap(p => params(p._2)) ++ params(f.result)).nonEmpty)
          throw SpecError(s"${f.name} quantifies, is recursive, and has type parameters")
        b ++= s"  ${name(f.name)} : ${(f.params.map(p => tpe(p._2, atom = true)) :+ tpe(f.result, atom = true)).mkString(" → ")}\n"
      }
      b.result()
    }

    /** The equations of the functions that the oracle gives. */
    def oracleSound: String = {
      val b = new StringBuilder
      b ++= "/-- The oracle gives each of its functions as the semantics defines it. -/\n"
      b ++= "structure Oracle.Sound (O : Oracle) : Prop where\n"
      for (f <- oracleFunctions) {
        val ps = f.params.map { case (x, t) => s" (${name(x)} : ${tpe(t)})" }.mkString
        val args = f.params.map(p => " " + name(p._1)).mkString
        b ++= s"  ${name(f.name)} : ∀$ps, O.${name(f.name)}$args = (\n${body(f, 2)}${ind(2)})\n"
      }
      b.result()
    }
  }

  /** The Lean source of `spec`, read from `source`, in `namespace`. `measures` maps the names of
    * functions to the `termination_by` and `decreasing_by` clauses that end their definitions. */
  def apply(spec: Spec, source: String, namespace: String,
      measures: Map[String, String] = Map(), assumed: Set[String] = Set()): String = {
    val w = new Writer(spec, measures, assumed)
    val b = new StringBuilder
    b ++= "/- Copyright 2009-2026 EPFL, Lausanne -/\n\n"
    b ++= s"-- Generated from $source by inox.semantics.Codegen. Do not edit: change $source\n"
    b ++= "-- and regenerate (see proofs/README.md).\n\n"
    b ++= "set_option autoImplicit false\n"
    b ++= "set_option linter.unusedVariables false\n\n"
    b ++= s"namespace $namespace\n\n"
    b ++= "/-- The names of variables, functions, constructors, sorts and fields. -/\n"
    b ++= "abbrev Id := String\n\n"

    val datatypes = spec.datatypes.filterNot(dt => isLeanList(dt) || isLeanOption(dt))
    val byName = datatypes.map(dt => dt.name -> dt).toMap
    for (group <- components[Datatype](datatypes,
        dt => dt.ctors.flatMap(_.fields.flatMap(f => named(f._2))).distinct.flatMap(byName.get))) {
      val recursive = group.size > 1
      if (recursive) b ++= "mutual\n"
      b ++= group.map(w.datatype).mkString("\n")
      if (recursive) b ++= "end\n"
      b ++= "\n"
    }

    b ++= "noncomputable section\n\n"
    b ++= "open Classical\n\n"
    if (w.oracle.nonEmpty) b ++= w.oracleStructure + "\n"
    val functions = spec.functions.filterNot(f => w.oracle(f.name))
    for (group <- components[Function](functions,
        f => w.calls(f).filterNot(w.oracle).flatMap(spec.functionsByName.get))) {
      val recursive = group.size > 1
      if (recursive) b ++= "mutual\n"
      b ++= group.map(w.function).mkString("\n")
      if (recursive) b ++= "end\n"
      b ++= "\n"
    }
    if (w.oracle.nonEmpty) b ++= w.oracleSound + "\n"
    b ++= "end\n\n"
    b ++= s"end $namespace\n"
    b.result()
  }
}
