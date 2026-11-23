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

  /** The functions that quantify over values: no program can compute them, so executable backends
    * leave them to an oracle. The functions that call them are computable relative to it. */
  lazy val noncomputable: Set[String] = {
    def quantifies(t: Term): Boolean = t match {
      case Term.Quant(_, _, _) => true
      case Term.Call(_, args) => args.exists(quantifies)
      case Term.Ctor(_, args) => args.exists(quantifies)
      case Term.Builtin(_, args) => args.exists(quantifies)
      case Term.Let(bs, b) => bs.exists(b => quantifies(b._2)) || quantifies(b)
      case Term.LetBang(bs, b) => bs.exists(b => quantifies(b._2)) || quantifies(b)
      case Term.If(c, a, b) => quantifies(c) || quantifies(a) || quantifies(b)
      case Term.Match(sc, cs) => quantifies(sc) || cs.exists(c => quantifies(c._2))
      case _ => false
    }
    def terms(f: Function): Seq[Term] = f.body match {
      case Body.Term(t) => Seq(t)
      case Body.Cases(_, cs) => cs.map(_._2)
    }
    functions.filter(f => terms(f).exists(quantifies)).map(_.name).toSet
  }
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
    /** `(forall ((x T) ...) body)` or `(exists ...)`, over all the values of the types. */
    case Quant(forall: Boolean, binders: Seq[(String, Type)], body: Term)
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

  /** The definitions of a semantics file that imports no other file. */
  def parse(markdown: String): Spec = {
    blocks(markdown).collectFirst { case i @ Sexp.Lst(Sexp.Atom("import") +: _) => i }
      .foreach(i => fail(s"$i: a file read on its own can't import others (see Spec.load)"))
    fromForms(blocks(markdown))
  }

  /** The definitions of the semantics file at `path`, after the files it imports with
    * `(import "relative/path.md")`, each read once, before the forms of the file that imports it
    * first. A file that extends a semantics imports it and extends its datatypes and functions. */
  def load(path: java.nio.file.Path): Spec = {
    import Sexp._
    val seen = scala.collection.mutable.Set[java.nio.file.Path]()
    def read(p: java.nio.file.Path, from: List[java.nio.file.Path]): Seq[Sexp] = {
      val file = p.toAbsolutePath.normalize
      if (from.contains(file)) fail(s"$file imports itself through ${from.reverse.mkString(", ")}")
      if (!seen.add(file)) return Seq()
      if (!java.nio.file.Files.exists(file)) fail(s"no semantics file $file")
      blocks(java.nio.file.Files.readString(file)).flatMap {
        case Lst(Seq(Atom("import"), Atom(q))) if q.length > 2 && q.head == '"' && q.last == '"' =>
          read(file.getParent.resolve(q.drop(1).dropRight(1)), file :: from)
        case i @ Lst(Atom("import") +: _) => fail(s"not an import: $i")
        case f => Seq(f)
      }
    }
    fromForms(read(path, Nil))
  }

  private def fromForms(forms: Seq[Sexp]): Spec = {
    import Sexp._

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

    val declared = forms.collect {
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
    declared.map(_.name).diff(declared.map(_.name).distinct).headOption
      .foreach(n => fail(s"datatype $n is declared twice"))

    // `(extend-datatype Name (Ctor (field Type) ...) ...)` adds constructors to a datatype declared
    // earlier, here or in an imported file, after its own.
    val datatypes = forms.foldLeft(declared) {
      case (dts, Lst(Atom("extend-datatype") +: Atom(name) +: ctors)) =>
        val dt = dts.find(_.name == name).getOrElse(fail(s"extension of $name, which isn't declared"))
        val added = ctors.map {
          case Lst(Atom(c) +: fields) if isCapitalized(c) => Constructor(c, fields.map(param(_, dt.tparams.toSet)))
          case c => fail(s"not a constructor of $name: $c")
        }
        dts.map(d => if (d.name == name) d.copy(ctors = d.ctors ++ added) else d)
      case (_, e @ Lst(Atom("extend-datatype") +: _)) => fail(s"not an extension: $e")
      case (dts, _) => dts
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
      case Lst(Seq(Atom(q @ ("forall" | "exists")), Lst(bs), body)) if bs.nonEmpty =>
        val binders = bs.map(param(_, Set()))
        Term.Quant(q == "forall", binders, term(body, scope ++ binders.map(_._1)))
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
      case Lst(Atom("datatype" | "extend-datatype" | "define" | "case") +: _) =>
      case f => fail(s"not a datatype, an extension, a definition or a case: $f")
    }

    val spec = Spec(datatypes, functions)
    checkTypes(spec)
    spec
  }

  private def params(t: Type): Set[String] = t match {
    case Type.Named(_, args) => args.flatMap(params).toSet
    case Type.Param(p) => Set(p)
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
    def checkTerm(t: Term): Unit = t match {
      case Term.Quant(_, bs, b) => bs.foreach(b => check(b._2)); checkTerm(b)
      case Term.Call(_, args) => args.foreach(checkTerm)
      case Term.Ctor(_, args) => args.foreach(checkTerm)
      case Term.Builtin(_, args) => args.foreach(checkTerm)
      case Term.Let(bs, b) => bs.foreach(b => checkTerm(b._2)); checkTerm(b)
      case Term.LetBang(bs, b) => bs.foreach(b => checkTerm(b._2)); checkTerm(b)
      case Term.If(c, a, b) => checkTerm(c); checkTerm(a); checkTerm(b)
      case Term.Match(sc, cs) => checkTerm(sc); cs.foreach(c => checkTerm(c._2))
      case _ =>
    }
    spec.functions.foreach { f =>
      f.params.foreach(p => check(p._2)); check(f.result)
      f.body match {
        case Body.Term(t) => checkTerm(t)
        case Body.Cases(_, cs) => cs.foreach(c => checkTerm(c._2))
      }
    }
    // A semantics that extends Inox's may give evaluation other outcomes, such as a failure that
    // tells a violated assertion apart from being stuck; `let!` propagates them all.
    if (!spec.datatypes.exists(dt => dt.name == resultType && dt.tparams.size == 1 &&
        dt.ctors.take(3).map(c => (c.name, c.fields.size)) == Seq(("Ok", 1), ("Stuck", 0), ("OutOfFuel", 0)) &&
        dt.ctors.drop(1).forall(_.fields.forall(f => !params(f._2)(dt.tparams.head)))))
      fail(s"the file must declare (datatype ($resultType T) (Ok (value T)) (Stuck) (OutOfFuel)), " +
        "whose other constructors don't hold a T")
  }
}
