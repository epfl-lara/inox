/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package grammars
package utils

trait Helpers { self: GrammarsUniverse =>
  import program._
  import trees.{ Minus => EMinus, Plus => EPlus, Variable => EVariable, _ }
  import exprOps._
  import symbols._

  /**
   * Filter functions potentially returning target type
   *
   * If the function takes type parameters, it will try to find an assignment
   * such that the function returns the target type.
   *
   * The return is thus a set of typed functions.
   */
  def functionsReturning(fds: Set[FunDef], tpe: Type): Set[TypedFunDef] = {
    fds.flatMap { fd =>
      canBeSubtypeOf(fd.returnType, tpe) match {
        case Some(tpsMap) =>
          Some(fd.typed(fd.typeArgs.map(tp => tpsMap.getOrElse(tp, tp))))
        case None =>
          None
      }
    }
  }

  /** Given an initial set of function calls provided by a list of [[Terminating]],
    * returns function calls that will hopefully be safe to call recursively from within this initial function calls.
    *
    * For each returned call, one argument is substituted by a "smaller" one, while the rest are left as holes.
    *
    * @param prog The current program
    * @param ws Helper predicates that contain [[Terminating]]s with the initial calls
    * @param pc The path condition
    * @param tpe The expected type for the returned function calls. If absent, all types are permitted.
    * @return A list of pairs (safe function call, holes),
    *         where holes stand for the rest of the arguments of the function.
    */
  def terminatingCalls(prog: Program, wss: Seq[FunctionInvocation], pc: Path, tpe: Option[Type], introduceHoles: Boolean): List[(FunctionInvocation, Option[Set[Identifier]])] = {

    def subExprsOf(expr: Expr, v: EVariable): Option[(EVariable, Expr)] = expr match {
      case CaseClassSelector(r, _) => subExprsOf(r, v)
      case (r: EVariable) if leastUpperBound(r.getType, v.getType).isDefined => Some(r -> v)
      case _ => None
    }

    val z   = IntegerLiteral(0)
    val one = IntegerLiteral(1)
    val knownSmallers = (pc.bindings.flatMap {
      // @nv: used to check both Equals(id, selector) and Equals(selector, id)
      case (id, s @ CaseClassSelector(r, _)) => subExprsOf(s, id.toVariable)
      case _ => None
    } ++ pc.conditions.flatMap {
      case GreaterThan(v: EVariable, `z`) =>
        Some(v -> EMinus(v, one))
      case LessThan(`z`, v: EVariable) =>
        Some(v -> EMinus(v, one))
      case LessThan(v: EVariable, `z`) =>
        Some(v -> EPlus(v, one))
      case GreaterThan(`z`, v: EVariable) =>
        Some(v -> EPlus(v, one))
      case _ => None
    }).groupBy(_._1).mapValues(v => v.map(_._2))

    def argsSmaller(e: Expr, tpe: Type): Seq[Expr] = e match {
      case CaseClass(cct, args) =>
        (cct.tcd.asInstanceOf[TypedCaseClassDef].fields.map(_.getType) zip args).collect {
          case (t, e) if isSubtypeOf(t, tpe) =>
            List(e) ++ argsSmaller(e, tpe) 
        }.flatten
      case v: EVariable =>
        knownSmallers.getOrElse(v, Seq())
      case _ => Nil
    }

    val res = wss.flatMap {
      case FunctionInvocation(fid, tps, args) =>
        val resFun = getFunction(fid)
        if (tpe forall (isSubtypeOf(resFun.returnType, _))) Nil else {
          val ids = resFun.params.map(vd => EVariable(FreshIdentifier("<hole>", true), vd.getType)).toList

          for (((a, i), tpe) <- args.zipWithIndex zip resFun.params.map(_.getType);
                smaller <- argsSmaller(a, tpe)) yield {
            val newArgs = (if (introduceHoles) ids else args).updated(i, smaller)
            val newFd = FunctionInvocation(fid, tps, newArgs)
            val freeIds = if(introduceHoles) Some((ids.toSet - ids(i)).map(_.id)) else None
            (newFd, freeIds)
          }
        }
    }

    res.toList
  }


  /**
   * All functions we call use in synthesis, which includes:
   *  - all functions in main units
   *  - all functions imported, or methods of classes imported
   */
  def functionsAvailable(p: Program): Set[FunDef]// = {
  //  visibleFunDefsFromMain(p)
  //}


}
