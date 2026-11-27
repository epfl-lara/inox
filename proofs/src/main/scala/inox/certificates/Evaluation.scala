/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package certificates

import java.io.StringReader

import semantics.Embedding
import semantics.generated.{Semantics => S}

import Checker.{SExpr, Atom, SList}

/** The evaluation of the closed terms of a certificate, which are terms of Inox's SMT-LIB 3 as
  * its source definitions are: they are read with Inox's parser, and evaluated by the evaluator
  * that is generated from `proofs/semantics.md`, the definition of Inox's semantics, with the
  * functions that `definitions` define.
  *
  * The evaluator covers a fragment of Inox, and evaluates with fuel: a term outside of the
  * fragment, or that the fuel gives no value to, has no value here. */
private[certificates] final class Evaluation(definitions: List[SExpr]) {
  import inox.trees._

  /** The selectors of the datatypes of the definitions. */
  private val selectors: Set[String] = {
    def fields(constructors: List[SExpr]) = constructors.flatMap {
      case SList(Atom(_) :: fs) => fs.collect { case SList(Atom(s) :: _) => s }
      case _ => Nil
    }
    definitions.flatMap {
      case SList(List(Atom("declare-datatypes"), _, SList(decls))) => decls.flatMap {
        case SList(List(Atom("par"), _, SList(cs))) => fields(cs)
        case SList(cs) => fields(cs)
        case _ => Nil
      }
      case SList(List(Atom("declare-datatype"), _, SList(List(Atom("par"), _, SList(cs))))) => fields(cs)
      case SList(List(Atom("declare-datatype"), _, SList(cs))) => fields(cs)
      case _ => Nil
    }.toSet
  }

  /** `t` without the sorts that certificates write the symbols of the syntax under (applications,
    * tuples, their selections and testers), which Inox's parser infers. */
  private def plain(t: SExpr): SExpr = t match {
    case SList(List(Atom("as"), a @ Atom("@" | "tuple"), _)) => a
    case SList(List(Atom("as"), a @ Atom(x), _)) if selectors(x) => a
    case SList(List(Atom("as"), s @ SList(List(Atom("_"), Atom("tuple.select" | "is"), _)), _)) => s
    case SList(items) => SList(items.map(plain))
    case a => a
  }

  /** The definitions in an order that Inox's parser reads: the functions, which the certificate
    * may define before those that they call, are defined together, after the rest. */
  private def script: List[SExpr] = {
    val functions = definitions.flatMap {
      case SList(List(Atom("define-fun" | "define-fun-rec"), SList(List(par @ Atom("par"), tps, SList(List(f, ps, sort, body)))))) =>
        List(SList(List(par, tps, SList(List(f, ps, sort)))) -> body)
      case SList(List(Atom("define-fun" | "define-fun-rec"), f, ps, sort, body)) => List(SList(List(f, ps, sort)) -> body)
      case SList(List(Atom("define-funs-rec"), SList(decls), SList(bodies))) if decls.size == bodies.size => decls zip bodies
      case _ => Nil
    }
    // the invariants of the datatypes call functions
    val (invariants, others) = definitions.filter {
      case SList(Atom("define-fun" | "define-fun-rec" | "define-funs-rec") :: _) => false
      case _ => true
    }.partition {
      case SList(Atom("datatype-invariant") :: _) => true
      case _ => false
    }
    others ++ (if (functions.isEmpty) Nil
      else List(SList(List(Atom("define-funs-rec"), SList(functions.map(_._1)), SList(functions.map(_._2)))))) ++ invariants
  }

  /** The definitions as Inox has them, and the terms that refer to them. */
  private final class Source extends smtlib3.Parser(new StringReader(script.map(plain).mkString("\n")), None) {
    private val locals = newParser(positions.reader).parseScript.commands
      .foldLeft(NoLocals)((locals, cmd) => extractCommand(cmd)(using locals)._2)
    val symbols: Symbols = locals.symbols
    def term(t: SExpr): Expr = locals.extractTerm(newParser(new StringReader(plain(t).toString)).parseTerm)
  }

  // definitions that Inox's parser doesn't read give no value to any term
  private lazy val source: Option[Source] = try Some(new Source) catch { case _: Exception => None }

  private lazy val functions: Map[Identifier, S.FunDef] = Embedding.coveredFunctions(using source.get.symbols)
  private lazy val program: S.Program = Embedding.program(functions)(using source.get.symbols)

  private object evaluator extends Embedding.Evaluator(Evaluation.fuel)

  /** The value of the closed term `t`, if it is in the fragment and has one within the fuel. */
  private def value(t: SExpr): Option[S.Value] = source.flatMap { source =>
    given Symbols = source.symbols
    try {
      val e = source.term(t)
      if (exprOps.variablesOf(e).nonEmpty || !Embedding.inFragment(e) ||
          !exprOps.functionCallsOf(e).forall(fi => functions.contains(fi.id))) None
      else Embedding.expr(e).map(evaluator.eval(program, Evaluation.fuel, S.Env(S.Nil(), S.Nil()), _)).collect {
        case S.Ok(v) => v
      }
    } catch {
      // a term that isn't one of Inox, or that the oracles of the evaluator don't decide
      case _: Exception | _: StackOverflowError => None
    }
  }

  /** Whether the closed terms `a` and `b` have the same value, if both have one, and their
    * equality is decided (the one of functions isn't). */
  def same(a: SExpr, b: SExpr): Option[Boolean] = for {
    v <- value(a)
    w <- value(b)
    r <- try Some(evaluator.value_eq(program, v, w)).collect { case S.Ok(r) => r }
         catch { case _: Exception | _: StackOverflowError => None }
  } yield r
}

private[certificates] object Evaluation {
  /** The fuel that terms are evaluated with. */
  val fuel = BigInt(200)
}
