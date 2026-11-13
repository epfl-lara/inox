/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package transformers

/** Types the propositions that a program declares as booleans (see [[ast.Types.PropType]]).
  *
  * The input formats only have booleans, so under propositional quantifiers, a function that
  * returns a quantifier is declared to return a boolean, and so is a variable that names one.
  * This makes these functions predicate definitions, and these variables propositions. Programs
  * without propositions are left as they are.
  */
trait PropositionInference extends SymbolTransformer {
  val s: ast.Trees
  val t: s.type
  import s._

  /** The type of propositions that `tpe` stands for, if it is the type of booleans or a
    * refinement of it. The refinements are kept: they state what holds of the proposition. */
  protected def asProposition(tpe: Type): Option[Type] = tpe match {
    case BooleanType() => Some(PropType().copiedFrom(tpe))
    case RefinementType(vd, pred) => asProposition(vd.tpe).map { underlying =>
      val newVd = vd.copy(tpe = underlying).copiedFrom(vd)
      val newPred = exprOps.replaceFromSymbols(Map(vd -> newVd.toVariable), pred)
      RefinementType(newVd, newPred).copiedFrom(tpe)
    }
    case _ => None
  }

  /** The expression `e`, where the variables that a `Let` binds to a proposition but declares
    * as (refined) booleans are propositions. */
  def transform(e: Expr)(using Symbols): Expr = {
    object inferrer extends ConcreteSelfTreeTransformer {
      override def transform(e: Expr): Expr = e match {
        case Let(vd, value, body) =>
          val newValue = transform(value)
          asProposition(vd.tpe).filter(_ => newValue.getType == PropType()) match {
            case Some(tpe) =>
              val newVd = vd.copy(tpe = tpe).copiedFrom(vd)
              val newBody = exprOps.replaceFromSymbols(Map(vd -> newVd.toVariable), body)
              Let(newVd, newValue, transform(newBody)).copiedFrom(e)
            case None =>
              Let(vd, newValue, transform(body)).copiedFrom(e)
          }
        case _ => super.transform(e)
      }
    }
    inferrer.transform(e)
  }

  /** The symbols `syms`, where the variables that are bound to a proposition are propositions,
    * and the functions that return a (refined) boolean but whose body is a proposition return a
    * proposition. The latter makes the functions that call them propositions in turn. */
  override def transform(syms: Symbols): Symbols = {
    val changed = syms.functions.values.flatMap { fd =>
      val body = transform(fd.fullBody)(using syms)
      val returnType = asProposition(fd.returnType)
        .filter(_ => body.getType(using syms) == PropType())
        .getOrElse(fd.returnType)
      if (body != fd.fullBody || returnType != fd.returnType)
        Some(fd.copy(fullBody = body, returnType = returnType).copiedFrom(fd))
      else None
    }.toSeq
    if (changed.isEmpty) syms else transform(syms.withFunctions(changed))
  }
}

object PropositionInference {
  def apply(trees: ast.Trees): PropositionInference { val s: trees.type; val t: trees.type } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends PropositionInference
    new Impl(trees, trees)
  }
}
