/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package transformers

/** Types the propositions that a program declares as booleans (see [[ast.Types.PropType]]).
  *
  * The input formats only have booleans, so under propositional quantifiers, a function that
  * returns a quantifier is declared to return a boolean, a variable that names one is declared
  * as a boolean, and a parameter or a field that is given one is declared as a boolean. This
  * makes these functions predicate definitions, and these variables, parameters and fields
  * propositions. The same goes for the functions that return propositions, which are declared
  * to return booleans, and for the tuples and maps that hold them. Programs without
  * propositions are left as they are.
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
    * the type itself, the result of a function type, the components of a tuple or the values of
    * a map. The refinements of `declared` are kept: they state what holds of the proposition.
    * This is `None` if nothing changes. */
  protected def asProposition(declared: Type, actual: Type): Option[Type] = (declared, actual) match {
    case (BooleanType(), PropType()) => Some(PropType().copiedFrom(declared))
    case (RefinementType(vd, pred), _) => asProposition(vd.tpe, actual).map { underlying =>
      val newVd = vd.copy(tpe = underlying).copiedFrom(vd)
      val newPred = exprOps.replaceFromSymbols(Map(vd -> newVd.toVariable), pred)
      RefinementType(newVd, newPred).copiedFrom(declared)
    }
    case (FunctionType(from, to), FunctionType(from2, to2)) if from.size == from2.size =>
      asProposition(to, to2).map(FunctionType(from, _).copiedFrom(declared))
    case (TupleType(tps), TupleType(tps2)) if tps.size == tps2.size =>
      val inferred = tps.zip(tps2).map((tp, tp2) => asProposition(tp, tp2))
      if (inferred.forall(_.isEmpty)) None
      else Some(TupleType(tps.zip(inferred).map((tp, tpe) => tpe.getOrElse(tp))).copiedFrom(declared))
    case (MapType(from, to), MapType(_, to2)) =>
      asProposition(to, to2).map(MapType(from, _).copiedFrom(declared))
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
    * the functions whose body is a proposition return a proposition, and the parameters and the
    * fields that are given a proposition are propositions. The same goes for the types that
    * hold propositions (see [[asProposition]]). Each of these can make more expressions
    * propositions, so this iterates. */
  override def transform(syms: Symbols): Symbols = {
    val typed = syms.functions.values.flatMap { fd =>
      val body = transform(fd.fullBody)(using syms)
      val returnType = asProposition(fd.returnType, body.getType(using syms)).getOrElse(fd.returnType)
      if (body != fd.fullBody || returnType != fd.returnType)
        Some(fd.copy(fullBody = body, returnType = returnType).copiedFrom(fd))
      else None
    }.toSeq
    val newSyms = if (typed.isEmpty) syms else syms.withFunctions(typed)

    // the types of the parameters and of the fields that some call or construction gives a
    // proposition to, by function or constructor
    var params: Map[Identifier, Map[Int, Type]] = Map.empty
    var fields: Map[Identifier, Map[Int, Type]] = Map.empty
    def propositions(declared: Seq[ValDef], args: Seq[Expr]): Map[Int, Type] = (for {
      ((vd, arg), i) <- declared.zip(args).zipWithIndex if declared.size == args.size
      tpe <- asProposition(vd.tpe, arg.getType(using newSyms))
    } yield i -> tpe).toMap
    for (fd <- newSyms.functions.values) exprOps.preTraversal {
      case FunctionInvocation(id, _, args) =>
        for (callee <- newSyms.lookupFunction(id); tpes = propositions(callee.params, args) if tpes.nonEmpty)
          params = params.updatedWith(id)(ps => Some(ps.getOrElse(Map.empty) ++ tpes))
      case ADT(id, _, args) =>
        for (cons <- newSyms.lookupConstructor(id); tpes = propositions(cons.fields, args) if tpes.nonEmpty)
          fields = fields.updatedWith(id)(fs => Some(fs.getOrElse(Map.empty) ++ tpes))
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

    val retypedSorts = fields.keys.map(newSyms.getConstructor(_).sort).toSeq.distinct.map { id =>
      val sort = newSyms.getSort(id)
      sort.copy(constructors = sort.constructors.map { cons =>
        fields.get(cons.id).map { tpes =>
          cons.copy(fields = cons.fields.zipWithIndex.map { case (vd, i) =>
            tpes.get(i).map(tpe => vd.copy(tpe = tpe).copiedFrom(vd)).getOrElse(vd)
          })
        }.getOrElse(cons)
      }).copiedFrom(sort)
    }

    if (typed.isEmpty && retyped.isEmpty && retypedSorts.isEmpty) syms
    else transform(newSyms.withFunctions(retyped).withSorts(retypedSorts))
  }
}

object PropositionInference {
  def apply(trees: ast.Trees): PropositionInference { val s: trees.type; val t: trees.type } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends PropositionInference
    new Impl(trees, trees)
  }
}
