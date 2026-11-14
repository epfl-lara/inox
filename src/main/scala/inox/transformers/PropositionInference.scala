/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package transformers

/** Types the propositions that a program declares as booleans (see [[ast.Types.PropType]]).
  *
  * The input formats only have booleans, so under propositional quantifiers, a function that
  * returns a quantifier is declared to return a boolean, a variable that names one is declared
  * as a boolean, and a parameter that is given one is declared as a boolean. This makes these
  * functions predicate definitions, and these variables and parameters propositions. The same
  * goes for the functions that return propositions, which are declared to return booleans.
  * Programs without propositions are left as they are.
  *
  * The inference only follows the propositions of the program: it doesn't check that they are
  * used as such. A function that branches on a parameter that is given a proposition doesn't
  * type once that parameter is a proposition.
  */
trait PropositionInference extends SymbolTransformer {
  val s: ast.Trees
  val t: s.type
  import s._

  /** The type `declared` where the booleans that are propositions in `actual` are propositions:
    * the type itself, or the result of a function type. The refinements of `declared` are
    * kept: they state what holds of the proposition. This is `None` if nothing changes. */
  protected def asProposition(declared: Type, actual: Type): Option[Type] = (declared, actual) match {
    case (BooleanType(), PropType()) => Some(PropType().copiedFrom(declared))
    case (RefinementType(vd, pred), _) => asProposition(vd.tpe, actual).map { underlying =>
      val newVd = vd.copy(tpe = underlying).copiedFrom(vd)
      val newPred = exprOps.replaceFromSymbols(Map(vd -> newVd.toVariable), pred)
      RefinementType(newVd, newPred).copiedFrom(declared)
    }
    case (FunctionType(from, to), FunctionType(from2, to2)) if from.size == from2.size =>
      asProposition(to, to2).map(FunctionType(from, _).copiedFrom(declared))
    case _ => None
  }

  /** The expression `e`, where the variables that a `Let` binds to a proposition, or to a
    * function that returns one, but declares with booleans are declared with propositions. */
  def transform(e: Expr)(using Symbols): Expr = {
    object inferrer extends ConcreteSelfTreeTransformer {
      override def transform(e: Expr): Expr = e match {
        case Let(vd, value, body) =>
          val newValue = transform(value)
          asProposition(vd.tpe, newValue.getType) match {
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
    * the functions whose body is a proposition return a proposition, and the parameters that
    * are given a proposition are propositions. The same goes for functions that return
    * propositions. Each of these can make more expressions propositions, so this iterates. */
  override def transform(syms: Symbols): Symbols = {
    val typed = syms.functions.values.flatMap { fd =>
      val body = transform(fd.fullBody)(using syms)
      val returnType = asProposition(fd.returnType, body.getType(using syms)).getOrElse(fd.returnType)
      if (body != fd.fullBody || returnType != fd.returnType)
        Some(fd.copy(fullBody = body, returnType = returnType).copiedFrom(fd))
      else None
    }.toSeq
    val newSyms = if (typed.isEmpty) syms else syms.withFunctions(typed)

    // the types of the parameters that some call gives a proposition to
    var params: Map[Identifier, Map[Int, Type]] = Map.empty
    for (fd <- newSyms.functions.values) exprOps.preTraversal {
      case FunctionInvocation(id, _, args) =>
        for {
          callee <- newSyms.lookupFunction(id) if callee.params.size == args.size
          ((vd, arg), i) <- callee.params.zip(args).zipWithIndex
          tpe <- asProposition(vd.tpe, arg.getType(using newSyms))
        } params = params.updatedWith(id)(ps => Some(ps.getOrElse(Map.empty) + (i -> tpe)))
      case _ =>
    } (fd.fullBody)

    val retyped = params.toSeq.map { case (id, tpes) =>
      val fd = newSyms.getFunction(id)
      val newParams = fd.params.zipWithIndex.map { case (vd, i) =>
        tpes.get(i).map(tpe => vd.copy(tpe = tpe).copiedFrom(vd)).getOrElse(vd)
      }
      val subst = fd.params.zip(newParams).collect { case (vd, nvd) if vd != nvd => vd -> nvd.toVariable }.toMap
      fd.copy(
        params = newParams,
        returnType = typeOps.replaceFromSymbols(subst, fd.returnType),
        fullBody = exprOps.replaceFromSymbols(subst, fd.fullBody)
      ).copiedFrom(fd)
    }

    if (typed.isEmpty && retyped.isEmpty) syms else transform(newSyms.withFunctions(retyped))
  }
}

object PropositionInference {
  def apply(trees: ast.Trees): PropositionInference { val s: trees.type; val t: trees.type } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends PropositionInference
    new Impl(trees, trees)
  }
}
