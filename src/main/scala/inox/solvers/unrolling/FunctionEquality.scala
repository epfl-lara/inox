/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

/** The semantics of equality between first-class functions.
  *
  * - [[FunctionEquality.None]]: functions can't be compared, and solvers reject queries that
  *   compare values containing functions, or that use sets and bags of such values or maps with
  *   such keys, which compare them implicitly. Counterexamples then never depend on function
  *   equality.
  * - [[FunctionEquality.Intensional]]: functions are compared structurally (Inox's historical
  *   semantics).
  * - [[FunctionEquality.Extensional]]: functions are equal iff they agree on every input.
  *
  * Under `none` and `extensional`, distinct functions always have a distinguishing input, in
  * refutations as well as in models (see [[WitnessTemplates.functionWitnesses]]). */
enum FunctionEquality {
  case None, Intensional, Extensional
}

object FunctionEquality {
  /** Whether values of type `tpe` can contain functions. Type parameters are assumed not to. */
  def containsFunctions(program: Program)(tpe: program.trees.Type): Boolean = {
    import program.trees._
    import program.symbols.{given, _}

    def rec(tpe: Type, seen: Set[Identifier]): Boolean = tpe match {
      case _: FunctionType | _: PiType => true
      case adt: ADTType =>
        !seen(adt.id) && adt.getSort.constructors.exists(_.fields.exists(vd => rec(vd.getType, seen + adt.id)))
      case NAryType(tps, _) => tps.exists(rec(_, seen))
    }

    rec(tpe.getType, Set.empty)
  }

  /** Whether values of type `tpe` can contain a set or a bag whose elements can contain functions, or
    * a map whose keys can. These collections compare their elements and keys, so they compare
    * functions. Type parameters are assumed not to contain functions. */
  def containsFunctionKeys(program: Program)(tpe: program.trees.Type): Boolean = {
    import program.trees._
    import program.symbols.{given, _}

    def keys(tpe: Type): Boolean = containsFunctions(program)(tpe)

    def rec(tpe: Type, seen: Set[Identifier]): Boolean = tpe match {
      case SetType(base) => keys(base) || rec(base, seen)
      case BagType(base) => keys(base) || rec(base, seen)
      case MapType(from, to) => keys(from) || rec(from, seen) || rec(to, seen)
      case adt: ADTType =>
        !seen(adt.id) && adt.getSort.constructors.exists(_.fields.exists(vd => rec(vd.getType, seen + adt.id)))
      case NAryType(tps, _) => tps.exists(rec(_, seen))
    }

    rec(tpe.getType, Set.empty)
  }

  /** The expressions of `expr` and of the functions it transitively calls that `select` picks.
    * Callees are visited at the type arguments they are called with, so that a type parameter is
    * checked at the types it is instantiated with. */
  private def collectReachable(program: Program)(expr: program.trees.Expr)
                              (select: program.trees.Expr => Seq[program.trees.Expr]): Seq[program.trees.Expr] = {
    import program.trees._
    import program.symbols.{given, _}

    // polymorphic recursion can instantiate a function at ever larger types, so past a few
    // instantiations of the same function, we check its generic body instead
    val seen = scala.collection.mutable.Set[(Identifier, Seq[Type])]()
    val result = scala.collection.mutable.ListBuffer[Expr]()
    var queue: List[Expr] = List(expr)
    while (queue.nonEmpty) {
      val e = queue.head
      queue = queue.tail
      result ++= select(e)
      for (fi <- exprOps.functionCallsOf(e)) {
        val instances = seen.count(_._1 == fi.id)
        val key = if (instances < 8) (fi.id, fi.tps) else (fi.id, getFunction(fi.id).typeArgs: Seq[Type])
        if (seen.add(key)) queue ::= getFunction(key._1, key._2).fullBody
      }
    }
    result.distinct.toSeq
  }

  /** The comparisons between values that may contain functions in `expr`, and in the functions it
    * transitively calls, which `none` rejects. The type parameters left free in `expr` are assumed
    * not to contain functions. */
  def comparisons(program: Program)(expr: program.trees.Expr): Seq[program.trees.Expr] = {
    import program.trees._
    import program.symbols.{given, _}

    def containsFunctions(tpe: Type): Boolean = FunctionEquality.containsFunctions(program)(tpe)

    collectReachable(program)(expr)(exprOps.collect[Expr] {
      // a constructor without functions in its fields is only equal to itself, so comparing
      // against it never compares functions
      case Equals(ADT(_, _, args), _) if !args.exists(a => containsFunctions(a.getType)) => Set.empty
      case Equals(_, ADT(_, _, args)) if !args.exists(a => containsFunctions(a.getType)) => Set.empty
      case eq @ Equals(l, _) if containsFunctions(l.getType) => Set(eq)
      case _ => Set.empty
    } (_).toSeq)
  }

  /** The expressions of `expr`, and of the functions it transitively calls, that introduce a set or a
    * bag of values that may contain functions, or a map with such keys (see [[containsFunctionKeys]]),
    * which `none` rejects since these collections compare their elements. These are the variables,
    * binders, literals and uninterpreted calls of such types. */
  def functionKeyedCollections(program: Program)(expr: program.trees.Expr): Seq[program.trees.Expr] = {
    import program.trees._
    import program.symbols.{given, _}

    def keyed(tpe: Type): Boolean = containsFunctionKeys(program)(tpe)

    collectReachable(program)(expr)(exprOps.collect[Expr] {
      case e @ (_: Variable | _: FiniteSet | _: FiniteBag | _: FiniteMap | _: UninterpretedCall | _: Error)
        if keyed(e.getType) => Set(e)
      case l: Lambda if l.params.exists(vd => keyed(vd.getType)) => Set(l)
      case f: Forall if f.params.exists(vd => keyed(vd.getType)) => Set(f)
      case _ => Set.empty
    } (_).toSeq)
  }
}

object optFunctionEquality extends OptionDef[FunctionEquality] {
  val name: String = "function-equality"
  val usageRhs: String = "none|intensional|extensional"
  val default: FunctionEquality = FunctionEquality.None
  override def formatDefault: String = default.toString.toLowerCase

  override def parser: OptionParsers.OptionParser[FunctionEquality] = s =>
    FunctionEquality.values.find(_.toString.toLowerCase == s.toLowerCase)
}
