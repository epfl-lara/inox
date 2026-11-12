/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package transformers

import org.scalatest.funsuite.AnyFunSuite

/** Generic transformers, traversers and their compositions. */
class TransformersSuite extends AnyFunSuite {
  import inox.trees._

  val x = Variable.fresh("x", IntegerType())
  val y = Variable.fresh("y", IntegerType())
  val p = Variable.fresh("p", BooleanType())
  val q = Variable.fresh("q", BooleanType())
  val marker = Variable.fresh("marker", IntegerType())

  /** Records the path under which each occurrence of `marker` appears. */
  class PathRecorder extends TransformerWithPC {
    val s: inox.trees.type = inox.trees
    val t: inox.trees.type = inox.trees
    type Env = Path
    val paths = scala.collection.mutable.ListBuffer.empty[Path]
    override def transform(e: Expr, env: Path): Expr = e match {
      case `marker` => paths += env; e
      case _ => super.transform(e, env)
    }
  }

  private def pathsOf(e: Expr): Seq[Path] = {
    val rec = new PathRecorder
    assert(rec.transform(e, Path.empty) == e)
    rec.paths.toSeq
  }

  private def pathsOf(tpe: Type): Seq[Path] = {
    val rec = new PathRecorder
    assert(rec.transform(tpe, Path.empty) == tpe)
    rec.paths.toSeq
  }

  test("Transformers with path conditions track bindings, bounds and conditions") {
    val vd = ValDef.fresh("z", IntegerType())
    val Seq(letPath) = pathsOf(Let(vd, x, marker))
    assert(letPath.bindings == Seq(vd -> x))

    val Seq(lambdaPath) = pathsOf(Lambda(Seq(vd), marker))
    assert(lambdaPath.open == Seq(vd))
    val Seq(forallPath) = pathsOf(Forall(Seq(vd), Equals(marker, x)))
    assert(forallPath.open == Seq(vd))

    val Seq(assumePath) = pathsOf(Assume(p, marker))
    assert(assumePath.conditions == Seq(p))

    val Seq(thenPath, elsePath) = pathsOf(IfExpr(p, marker, marker))
    assert(thenPath.conditions == Seq(p))
    assert(elsePath.conditions == Seq(Not(p)))

    val Seq(andPath) = pathsOf(And(Seq(p, q, Equals(marker, x))))
    assert(andPath.conditions == Seq(p, q))
    val Seq(orPath) = pathsOf(Or(Seq(p, Equals(marker, x))))
    assert(orPath.conditions == Seq(Not(p)))
    val Seq(impliesPath) = pathsOf(Implies(p, Equals(marker, x)))
    assert(impliesPath.conditions == Seq(p))

    val Seq(plainPath) = pathsOf(Plus(marker, x))
    assert(plainPath.isEmpty)
  }

  test("Transformers with path conditions bind the variables of dependent types") {
    val vd = ValDef.fresh("z", IntegerType())
    val Seq(refPath) = pathsOf(RefinementType(vd, Equals(marker, vd.toVariable)))
    assert(refPath.open == Seq(vd))

    val res = ValDef.fresh("r", IntegerType())
    val refined = RefinementType(res, Equals(marker, vd.toVariable))
    val Seq(piPath) = pathsOf(PiType(Seq(vd), refined))
    assert(piPath.open.take(1) == Seq(vd))
    val Seq(sigmaPath) = pathsOf(SigmaType(Seq(vd), refined))
    assert(sigmaPath.open.take(1) == Seq(vd))
    assert(pathsOf(IntegerType()).isEmpty)
  }

  test("Paths") {
    val vd = ValDef.fresh("z", IntegerType())
    val path = Path(Seq(Path.CloseBound(vd, x), Path.OpenBound(ValDef.fresh("o", IntegerType())), Path.Condition(p)))
    assert(Path(path) == path)
    assert(path.hashCode == Path(path.elements).hashCode)
    assert(path != x)
    val mapped = path.map(v => v.freshen, e => e)
    assert(mapped.bound.size == 2 && mapped.bound != path.bound)
    val tp = TypeParameter.fresh("T")
    val tpPath = Path(Seq(Path.OpenBound(ValDef.fresh("g", tp)), Path.Condition(BooleanLiteral(true))))
    assert(tpPath.isEmpty)
    assert(tpPath.instantiate(Map(tp -> IntegerType())).open.head.tpe == IntegerType())
  }

  /** Renames `x` into `y` everywhere, including in flags. */
  class Renamer extends inox.trees.ConcreteSelfTreeTransformer {
    override def transform(e: Expr): Expr = e match {
      case `x` => y
      case _ => super.transform(e)
    }
  }

  test("Tree transformers transform flags, definitions and compositions") {
    val r = new Renamer
    val flagged = ValDef(FreshIdentifier("v"), IntegerType(), Seq(Annotation("ann", Seq(x, IntegerType(), "str"))))
    val renamed = r.transform(flagged)
    assert(renamed.flags == Seq(Annotation("ann", Seq(y, IntegerType(), "str"))))

    val unchanged = ValDef(FreshIdentifier("w"), IntegerType(), Seq(Annotation("ann", Seq(y))))
    assert(r.transform(unchanged) eq unchanged)

    val tpd = TypeParameterDef(TypeParameter.fresh("T"))
    assert(r.transform(tpd) eq tpd)

    val fd = new FunDef(FreshIdentifier("f"), Seq(tpd), Seq(flagged), IntegerType(), Plus(x, flagged.toVariable),
      Seq(Annotation("fn", Seq(x))))
    val newFd = r.transform(fd)
    assert(newFd.fullBody == Plus(y, renamed.toVariable))
    assert(newFd.flags == Seq(Annotation("fn", Seq(y))))
    assert(newFd.params.head.flags == renamed.flags)

    val sortId = FreshIdentifier("S")
    val sort = new ADTSort(sortId, Seq(), Seq(new ADTConstructor(FreshIdentifier("C"), sortId, Seq(flagged))),
      Seq(Annotation("sort", Seq(x))))
    val newSort = r.transform(sort)
    assert(newSort.flags == Seq(Annotation("sort", Seq(y))))
    assert(newSort.constructors.head.fields.head.flags == renamed.flags)

    // Expressions whose flags change are rebuilt
    val lambda = Lambda(Seq(flagged), flagged.toVariable)
    assert(r.transform(lambda) == Lambda(Seq(renamed), renamed.toVariable))

    // y to z after x to y
    val z = Variable.fresh("z", IntegerType())
    class Second extends inox.trees.ConcreteSelfTreeTransformer {
      override def transform(e: Expr): Expr = e match {
        case `y` => z
        case _ => super.transform(e)
      }
    }
    val composed = (new Second).compose(r)
    assert(composed.transform(Plus(x, y)) == Plus(z, z))
    assert(composed.transform(IntegerType()) == IntegerType())
    assert(composed.transform(flagged).flags == Seq(Annotation("ann", Seq(z, IntegerType(), "str"))))
    assert(composed.transform(Annotation("a", Seq(x))) == Annotation("a", Seq(z)))
    assert(composed.transform(fd).fullBody == Plus(z, composed.transform(flagged).toVariable))
    assert(composed.transform(sort).flags == Seq(Annotation("sort", Seq(z))))
    val id = FreshIdentifier("id")
    assert(composed.transform(id) == id)
    assert(composed.transform(id, IntegerType()) == (id, IntegerType()))
  }

  test("Symbol transformers and their compositions") {
    val fd = new FunDef(FreshIdentifier("f"), Seq(), Seq(), IntegerType(), x, Seq())
    val syms = NoSymbols.withFunctions(Seq(fd))
    val st1 = SymbolTransformer(new Renamer)
    val z = Variable.fresh("z", IntegerType())
    class Second extends inox.trees.ConcreteSelfTreeTransformer {
      override def transform(e: Expr): Expr = e match {
        case `y` => z
        case _ => super.transform(e)
      }
    }
    val st2 = SymbolTransformer(new Second)
    val composed = st1.andThen(st2)
    assert(composed.transform(syms).functions(fd.id).fullBody == z)
    assert(st2.compose(st1).transform(syms).functions(fd.id).fullBody == z)
    assert(composed == st2.compose(st1))
    assert(composed.hashCode == st2.compose(st1).hashCode)
    assert(composed != st1)

    val program = InoxProgram(syms)
    val enc = ProgramEncoder(program)(st1)
    assert(enc.targetProgram.symbols.functions(fd.id).fullBody == y)
    val twice = enc.compose(ProgramEncoder.empty(program).asInstanceOf[ProgramTransformer { val targetProgram: enc.sourceProgram.type }])
    assert(twice.targetProgram.symbols.functions(fd.id).fullBody == y)
  }

  test("Traversers with operations") {
    val seen = scala.collection.mutable.ListBuffer.empty[Expr]
    val seenTypes = scala.collection.mutable.ListBuffer.empty[Type]
    class Collector extends inox.trees.ConcreteSelfTraverser with TraverserWithExprOp with TraverserWithTypeOp {
      type Env = Unit
      protected val exprOp = (e: Expr, env: Unit, op: TraverserOp[Expr, Unit]) => {
        seen += e
        op.sup(e, env)
      }
      protected val typeOp = (tpe: Type, env: Unit, op: TraverserOp[Type, Unit]) => {
        seenTypes += tpe
        op.sup(tpe, env)
      }
    }
    val c = new Collector
    c.traverse(Plus(x, IntegerLiteral(1)), ())
    assert(seen.toSeq == Seq(Plus(x, IntegerLiteral(1)), x, IntegerLiteral(1)))
    assert(seenTypes.toSeq == Seq(IntegerType()))
    val op = new TraverserOp[Expr, Unit]((e, _) => seen += e, (_, _) => ())
    op(x, ())
    assert(seen.last == x)

    // Flags of definitions and value definitions are traversed
    val flaggedSeen = scala.collection.mutable.ListBuffer.empty[Expr]
    class FlagCollector extends inox.trees.ConcreteSelfTreeTraverser {
      override def traverse(e: Expr): Unit = { flaggedSeen += e; super.traverse(e) }
    }
    val flagged = ValDef(FreshIdentifier("v"), IntegerType(), Seq(Annotation("ann", Seq(x))))
    val sortId = FreshIdentifier("S")
    val tpd = TypeParameterDef(TypeParameter.fresh("T"))
    val sort = new ADTSort(sortId, Seq(tpd), Seq(new ADTConstructor(FreshIdentifier("C"), sortId, Seq(flagged))),
      Seq(Annotation("sort", Seq(y))))
    val fc = new FlagCollector
    fc.traverse(sort)
    fc.traverse(new FunDef(FreshIdentifier("f"), Seq(), Seq(), IntegerType(), IntegerLiteral(0), Seq(Annotation("fn", Seq(p)))))
    assert(Set(x, y, p).subsetOf(flaggedSeen.toSet))
  }
}
