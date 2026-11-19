/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package semantics

/** The definitions of a semantics file (`proofs/semantics.md`): its datatypes and functions, read
  * from the fenced blocks tagged `inox-sem`. The file's last section describes the language. */
final case class Spec(datatypes: Seq[Spec.Datatype], functions: Seq[Spec.Function]) {
  import Spec._

  lazy val constructors: Map[String, (Datatype, Constructor)] =
    datatypes.flatMap(dt => dt.ctors.map(c => c.name -> (dt, c))).toMap
  lazy val functionsByName: Map[String, Function] = functions.map(f => f.name -> f).toMap
}

object Spec {

  enum Type {
    case Named(name: String, args: Seq[Type])
    case Param(name: String)
  }

  final case class Constructor(name: String, fields: Seq[(String, Type)])
  final case class Datatype(name: String, tparams: Seq[String], ctors: Seq[Constructor])

  enum Body {
    case Term(term: Spec.Term)
    /** One case per constructor of the type of `param`, in the order of the datatype. */
    case Cases(param: String, cases: Seq[(Pattern.Ctor, Spec.Term)])
  }

  final case class Function(name: String, params: Seq[(String, Type)], result: Type, body: Body)

  enum Term {
    case Var(name: String)
    case IntLit(value: BigInt)
    case BoolLit(value: Boolean)
    case Ctor(name: String, args: Seq[Term])
    case Call(name: String, args: Seq[Term])
    case Builtin(op: String, args: Seq[Term])
    case Let(bindings: Seq[(String, Term)], body: Term)
    case LetBang(bindings: Seq[(String, Term)], body: Term)
    case If(cond: Term, thenn: Term, elze: Term)
    case Match(scrutinee: Term, cases: Seq[(Pattern, Term)])
  }

  enum Pattern {
    case Wildcard
    case Bind(name: String)
    case BoolLit(value: Boolean)
    case Ctor(name: String, args: Seq[Pattern])
  }

  /** The built-in operations and their arities. */
  val builtins: Map[String, Int] = Map(
    "+" -> 2, "-" -> 2, "*" -> 2, "<" -> 2, "<=" -> 2, "div" -> 2, "mod" -> 2,
    "and" -> 2, "or" -> 2, "not" -> 1, "=" -> 2)

  val builtinTypes: Map[String, Int] = Map("Int" -> 0, "Bool" -> 0, "Id" -> 0)

  /** The datatype whose constructors `let!` propagates. */
  val resultType = "Result"

  final class SpecError(msg: String) extends Exception(msg)

  private def fail(msg: String): Nothing = throw SpecError(msg)

  /** The S-expressions of the blocks tagged `inox-sem` in a Markdown text. */
  def blocks(markdown: String): Seq[Sexp] = {
    val lines = markdown.linesIterator.toSeq
    val res = Seq.newBuilder[Sexp]
    var i = 0
    while (i < lines.size) {
      if (lines(i).trim == "```inox-sem") {
        val start = i + 1
        var end = start
        while (end < lines.size && lines(end).trim != "```") end += 1
        if (end == lines.size) fail(s"block at line ${i + 1} isn't closed")
        try res ++= Sexp.parseAll(lines.slice(start, end).mkString("\n"))
        catch { case e: Sexp.ParseError => fail(s"block at line ${i + 1}: ${e.getMessage}") }
        i = end + 1
      } else i += 1
    }
    res.result()
  }

  def parse(markdown: String): Spec = {
    import Sexp._
    val forms = blocks(markdown)

    def isCapitalized(s: String) = s.nonEmpty && s.head.isUpper && s.forall(_.isLetterOrDigit)
    def isName(s: String) = s.nonEmpty && s.head.isLetter && s.forall(c => c.isLetterOrDigit || c == '-')

    def typeOf(s: Sexp, tparams: Set[String]): Type = s match {
      case Atom(n) if tparams(n) => Type.Param(n)
      case Atom(n) => Type.Named(n, Seq())
      case Lst(Atom(n) +: args) if args.nonEmpty => Type.Named(n, args.map(typeOf(_, tparams)))
      case _ => fail(s"not a type: $s")
    }

    def param(s: Sexp, tparams: Set[String]): (String, Type) = s match {
      case Lst(Seq(Atom(x), t)) if isName(x) => x -> typeOf(t, tparams)
      case _ => fail(s"not a parameter: $s")
    }

    val datatypes = forms.collect {
      case Lst(Atom("datatype") +: head +: ctors) =>
        val (name, tparams) = head match {
          case Atom(n) => (n, Seq())
          case Lst(Atom(n) +: ts) => (n, ts.map { case Atom(t) => t; case t => fail(s"not a type parameter: $t") })
          case _ => fail(s"not a datatype name: $head")
        }
        if (!isCapitalized(name)) fail(s"datatype name $name doesn't start with a capital letter")
        Datatype(name, tparams, ctors.map {
          case Lst(Atom(c) +: fields) if isCapitalized(c) =>
            Constructor(c, fields.map(param(_, tparams.toSet)))
          case c => fail(s"not a constructor of $name: $c")
        })
    }
    val ctorNames = datatypes.flatMap(_.ctors.map(_.name))
    ctorNames.diff(ctorNames.distinct).headOption.foreach(c => fail(s"constructor $c is declared twice"))
    val ctors = datatypes.flatMap(_.ctors.map(c => c.name -> c)).toMap

    val defines = forms.collect { case Lst(Atom("define") +: rest) => rest }
    val defNames = defines.map {
      case Lst(Atom(f) +: _) +: _ => f
      case d => fail(s"not a definition: $d")
    }
    defNames.diff(defNames.distinct).headOption.foreach(f => fail(s"function $f is defined twice"))
    val defSet = defNames.toSet

    def pattern(s: Sexp): Pattern = s match {
      case Atom("_") => Pattern.Wildcard
      case Atom("true") => Pattern.BoolLit(true)
      case Atom("false") => Pattern.BoolLit(false)
      case Atom(x) if isName(x) && !ctors.contains(x) => Pattern.Bind(x)
      case Lst(Atom(c) +: args) if ctors.contains(c) =>
        if (ctors(c).fields.size != args.size) fail(s"constructor $c has ${ctors(c).fields.size} fields: $s")
        Pattern.Ctor(c, args.map(pattern))
      case _ => fail(s"not a pattern: $s")
    }

    def bindings(s: Sexp, scope: Set[String]): (Seq[(String, Term)], Set[String]) = s match {
      case Lst(bs) =>
        bs.foldLeft((Seq[(String, Term)](), scope)) {
          case ((acc, sc), Lst(Seq(Atom(x), t))) if isName(x) => (acc :+ (x -> term(t, sc)), sc + x)
          case (_, b) => fail(s"not a binding: $b")
        }
      case _ => fail(s"not a list of bindings: $s")
    }

    def bound(p: Pattern): Set[String] = p match {
      case Pattern.Bind(x) => Set(x)
      case Pattern.Ctor(_, args) => args.flatMap(bound).toSet
      case _ => Set()
    }

    def term(s: Sexp, scope: Set[String]): Term = s match {
      case Atom("true") => Term.BoolLit(true)
      case Atom("false") => Term.BoolLit(false)
      case Atom(n) if n.forall(_.isDigit) => Term.IntLit(BigInt(n))
      case Atom(x) if scope(x) => Term.Var(x)
      case Atom(x) => fail(s"unbound variable $x")
      case Lst(Seq(Atom("let"), bs, body)) =>
        val (b, sc) = bindings(bs, scope)
        Term.Let(b, term(body, sc))
      case Lst(Seq(Atom("let!"), bs, body)) =>
        val (b, sc) = bindings(bs, scope)
        Term.LetBang(b, term(body, sc))
      case Lst(Seq(Atom("if"), c, t, e)) => Term.If(term(c, scope), term(t, scope), term(e, scope))
      case Lst(Atom("match") +: scrut +: cases) if cases.nonEmpty =>
        Term.Match(term(scrut, scope), cases.map {
          case Lst(Seq(p, body)) =>
            val pat = pattern(p)
            pat -> term(body, scope ++ bound(pat))
          case c => fail(s"not a case: $c")
        })
      case Lst(Atom(c) +: args) if ctors.contains(c) =>
        if (ctors(c).fields.size != args.size) fail(s"constructor $c has ${ctors(c).fields.size} fields: $s")
        Term.Ctor(c, args.map(term(_, scope)))
      case Lst(Atom(f) +: args) if defSet(f) => Term.Call(f, args.map(term(_, scope)))
      case Lst(Atom(op) +: args) if builtins.contains(op) =>
        if (builtins(op) != args.size) fail(s"$op takes ${builtins(op)} arguments: $s")
        Term.Builtin(op, args.map(term(_, scope)))
      case _ => fail(s"not a term: $s")
    }

    val caseForms = forms.collect {
      case Lst(Seq(Atom("case"), Atom(f), pat, body)) => (f, pat, body)
      case c @ Lst(Atom("case") +: _) => fail(s"not a case: $c")
    }

    val functions = defines.map {
      case Lst(Atom(name) +: ps) +: rest =>
        val params = ps.map(param(_, Set()))
        val scope = params.map(_._1).toSet
        rest match {
          case Seq(res, Atom(":cases"), Atom(x)) =>
            val tpe = params.collectFirst { case (`x`, t) => t }.getOrElse(fail(s"$name has no parameter $x"))
            val dt = tpe match {
              case Type.Named(n, Seq()) => datatypes.find(_.name == n).getOrElse(fail(s"$x of $name isn't a datatype"))
              case _ => fail(s"$x of $name isn't a datatype without type parameters")
            }
            val cases = caseForms.filter(_._1 == name).map { case (_, p, body) =>
              pattern(p) match {
                case pc @ Pattern.Ctor(c, args) if args.forall {
                      case Pattern.Bind(_) | Pattern.Wildcard => true
                      case _ => false
                    } =>
                  pc -> term(body, scope ++ bound(pc))
                case _ => fail(s"a case of $name binds a constructor's fields: $p")
              }
            }
            val byCtor = cases.groupBy(_._1.name)
            byCtor.find(_._2.size > 1).foreach(c => fail(s"$name has several cases for ${c._1}"))
            cases.map(_._1.name).find(c => !dt.ctors.exists(_.name == c))
              .foreach(c => fail(s"$c isn't a constructor of ${dt.name}"))
            dt.ctors.find(c => !byCtor.contains(c.name)).foreach(c => fail(s"$name has no case for ${c.name}"))
            Function(name, params, typeOf(res, Set()), Body.Cases(x, dt.ctors.map(c => byCtor(c.name).head)))
          case Seq(res, body) =>
            Function(name, params, typeOf(res, Set()), Body.Term(term(body, scope)))
          case _ => fail(s"not a definition of $name")
        }
      case d => fail(s"not a definition: $d")
    }
    caseForms.map(_._1).find(f => !functions.exists(fn => fn.name == f && fn.body.isInstanceOf[Body.Cases]))
      .foreach(f => fail(s"case of $f, which isn't defined by cases"))

    forms.foreach {
      case Lst(Atom("datatype" | "define" | "case") +: _) =>
      case f => fail(s"not a datatype, a definition or a case: $f")
    }

    val spec = Spec(datatypes, functions)
    checkTypes(spec)
    spec
  }

  /** Every type that a definition names is declared, with its number of type parameters. */
  private def checkTypes(spec: Spec): Unit = {
    val arity = builtinTypes ++ spec.datatypes.map(dt => dt.name -> dt.tparams.size)
    def check(t: Type): Unit = t match {
      case Type.Named(n, args) =>
        if (!arity.contains(n)) fail(s"unknown type $n")
        if (arity(n) != args.size) fail(s"type $n takes ${arity(n)} type arguments")
        args.foreach(check)
      case Type.Param(_) =>
    }
    spec.datatypes.foreach(_.ctors.foreach(_.fields.foreach(f => check(f._2))))
    spec.functions.foreach { f => f.params.foreach(p => check(p._2)); check(f.result) }
    if (!spec.datatypes.exists(dt => dt.name == resultType && dt.tparams.size == 1 &&
        dt.ctors.map(c => (c.name, c.fields.size)) == Seq(("Ok", 1), ("Stuck", 0), ("OutOfFuel", 0))))
      fail(s"the file must declare (datatype ($resultType T) (Ok (value T)) (Stuck) (OutOfFuel))")
  }
}
