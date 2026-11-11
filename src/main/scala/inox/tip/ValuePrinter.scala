/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package tip

import _root_.smtlib.trees.Terms.{Identifier => SMTIdentifier, _}
import _root_.smtlib.printer.RecursivePrinter

import java.io.Writer
import scala.collection.mutable.{Set => MutableSet}

/** Prints model values as SMT-LIB terms, for tools that drive Inox
  * through its command line (see `--model-format=smtlib`).
  *
  * Values are translated by the TIP [[Printer]], so they use the syntax that
  * Inox's TIP parser reads and a printed value can be parsed back in the
  * context of the problem it answers:
  *  - integers, reals, booleans, bit-vectors, characters (as 16-bit
  *    vectors) and strings (with the SMT-LIB `\u{...}` escapes);
  *  - datatype values, with nullary constructors of parametric datatypes
  *    qualified by their sort, as in `(as nil (list Int))`. Values of a
  *    `declare-sort` sort are printed as Inox encodes them, `(S n)` for the
  *    n-th value of sort `S`;
  *  - maps as arrays, `(store ((as const (Array K V)) d) k v)`;
  *  - sets and bags in the CVC4 syntax that Inox's TIP printer and parser
  *    use, e.g. `(insert (as emptyset Int) 1 2)`; they are not part of the
  *    SMT-LIB standard;
  *  - functions as `lambda` terms, and abstract values of type parameters
  *    as `@T_n`.
  *
  * The value printer discards the declarations the TIP printer emits: free
  * variables, sorts and constructors are printed with the names they had in
  * the input, so a TIP producer can map a model back to its own terms.
  * Variables bound inside values (lambda parameters) get unique names.
  * Values the TIP printer can't translate raise its `UnsupportedTree`.
  */
class ValuePrinter(p: InoxProgram, ctx: Context)
  extends Printer(p, ctx, Writer.nullWriter()) {
  import program.trees._

  // Binders get unique names so that they can't capture the input's free names.
  private val bound = MutableSet.empty[Identifier]

  override protected def id2sym(id: Identifier): SSymbol =
    if (bound(id)) super.id2sym(id) else SSymbol(id.name)

  override protected def freshSym(name: String): SSymbol = {
    val id = FreshIdentifier(name)
    bound += id
    id2sym(id)
  }

  override protected def toSMT(e: Expr)(using bindings: Map[Identifier, Term]): Term = {
    e match {
      case Lambda(params, _) => bound ++= params.map(_.id)
      case Forall(params, _) => bound ++= params.map(_.id)
      case Let(vd, _, _) => bound += vd.id
      case Choose(vd, _) => bound += vd.id
      case _ =>
    }

    e match {
      // Solvers encode these as constructor applications, but the TIP parser reads them as names.
      case GenericValue(tp, n) => QualifiedIdentifier(SMTIdentifier(SSymbol(s"@${tp.id.name}_$n")))
      case _ => super.toSMT(e)
    }
  }

  def sort(tpe: Type): String = RecursivePrinter.toString(declareSort(tpe))

  def value(e: Expr): String = RecursivePrinter.toString(toSMT(e)(using Map.empty))

  /** The model in `get-value` response form: `((x v) (y w) ...)`. */
  def model(vars: Map[ValDef, Expr]): String =
    vars.toSeq.sortBy(_._1.id.name).map { case (vd, v) => s"(${vd.id.name} ${value(v)})" }
      .mkString("(", " ", ")")
}
