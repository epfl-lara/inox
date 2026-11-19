/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package semantics

import java.nio.file.{Files, Paths}

import org.scalatest.funsuite.AnyFunSuite

import generated.{Semantics => S}

/** The semantics of `proofs/semantics.md`, as the Scala evaluator generated from it, against
  * [[evaluators.RecursiveEvaluator]], and the generated evaluator against the file. */
class SemanticsSuite extends AnyFunSuite {
  import inox.trees._
  given PrinterOptions = PrinterOptions()

  private def list[A](xs: Seq[A]): S.List[A] = xs.foldRight(S.Nil(): S.List[A])(S.Cons(_, _))

  /** An Inox expression in the semantics, if it is in its fragment. */
  def expr(e: Expr): Option[S.Expr] = {
    def all(es: Seq[Expr]): Option[S.List[S.Expr]] = {
      val cs = es.map(expr)
      if (cs.forall(_.isDefined)) Some(list(cs.flatten)) else None
    }
    def two(l: Expr, r: Expr)(f: (S.Expr, S.Expr) => S.Expr) = for (a <- expr(l); b <- expr(r)) yield f(a, b)
    e match {
      case v: Variable => Some(S.Variable(v.id))
      case IntegerLiteral(i) => Some(S.IntegerLiteral(i))
      case BooleanLiteral(b) => Some(S.BooleanLiteral(b))
      case UnitLiteral() => Some(S.UnitLiteral())
      case Let(vd, v, b) => two(v, b)(S.Let(vd.id, _, _))
      case IfExpr(c, t, f) => for (a <- expr(c); b <- expr(t); d <- expr(f)) yield S.IfExpr(a, b, d)
      case Assume(p, b) => two(p, b)(S.Assume(_, _))
      case Error(_, _) => Some(S.Error())
      case FunctionInvocation(id, _, args) => all(args).map(S.FunctionInvocation(id, _))
      case ADT(id, _, args) => all(args).map(S.ADT(id, _))
      case IsConstructor(a, id) => expr(a).map(S.IsConstructor(_, id))
      case ADTSelector(a, id) => expr(a).map(S.ADTSelector(_, id))
      case Equals(l, r) => two(l, r)(S.Equals(_, _))
      case And(es) => all(es).map(S.And(_))
      case Or(es) => all(es).map(S.Or(_))
      case Implies(l, r) => two(l, r)(S.Implies(_, _))
      case Not(a) => expr(a).map(S.Not(_))
      case Plus(l, r) => two(l, r)(S.Plus(_, _))
      case Minus(l, r) => two(l, r)(S.Minus(_, _))
      case UMinus(a) => expr(a).map(S.UMinus(_))
      case Times(l, r) => two(l, r)(S.Times(_, _))
      case Division(l, r) => two(l, r)(S.Division(_, _))
      case Remainder(l, r) => two(l, r)(S.Remainder(_, _))
      case Modulo(l, r) => two(l, r)(S.Modulo(_, _))
      case LessThan(l, r) => two(l, r)(S.LessThan(_, _))
      case GreaterThan(l, r) => two(l, r)(S.GreaterThan(_, _))
      case LessEquals(l, r) => two(l, r)(S.LessEquals(_, _))
      case GreaterEquals(l, r) => two(l, r)(S.GreaterEquals(_, _))
      case _ => None
    }
  }

  /** Whether the semantics covers the types of `e`'s values: the integer operations are also
    * bit-vector and real operations in Inox. */
  def firstOrder(e: Expr)(using Symbols): Boolean = exprOps.collect[Type] {
    case e => Set(e.getType)
  }(e).forall(supported)

  def supported(t: Type): Boolean = t match {
    case IntegerType() | BooleanType() | UnitType() | _: TypeParameter => true
    case ADTType(_, tps) => tps.forall(supported)
    case _ => false
  }

  /** The functions of `symbols` in the fragment, with the functions they call. */
  def coveredFunctions(using symbols: Symbols): Map[Identifier, S.FunDef] = {
    val candidates = symbols.functions.values.flatMap { fd =>
      if (!firstOrder(fd.fullBody) || !(fd.params.map(_.tpe) :+ fd.returnType).forall(supported)) None
      else expr(fd.fullBody).map(b => fd.id -> S.FunDef(fd.id, list(fd.params.map(_.id)), b))
    }.toMap
    var covered = candidates
    var changed = true
    while (changed) {
      val next = covered.filter { case (id, _) => symbols.getFunction(id).fullBody match {
        case body => exprOps.functionCallsOf(body).forall(fi => covered.contains(fi.id)) &&
          // the invariants of the sorts that the body builds
          exprOps.collect[Identifier] { case ADT(c, _, _) => symbols.getConstructor(c).getSort.invariant.map(_.id).toSet
                                       case _ => Set() }(body).forall(covered.contains)
      }}
      changed = next.size != covered.size
      covered = next
    }
    covered
  }

  def program(functions: Map[Identifier, S.FunDef])(using symbols: Symbols): S.Program = S.Program(
    list(functions.values.toSeq),
    list(symbols.constructors.values.toSeq.map(c => S.Constructor(c.id, c.sort, list(c.fields.map(_.id))))),
    list(symbols.sorts.values.toSeq.map(s => S.Sort(s.id, s.invariant.map(_.id) match {
      case scala.Some(id) => S.Some(id)
      case scala.None => S.None()
    }))))

  /** A value of Inox's evaluator in the semantics. */
  def value(e: Expr): S.Value = e match {
    case IntegerLiteral(i) => S.IntV(i)
    case BooleanLiteral(b) => S.BoolV(b)
    case UnitLiteral() => S.UnitV()
    case ADT(id, _, args) => S.ADTV(id, list(args.map(value)))
    case _ => fail(s"not a value of the semantics: $e")
  }

  val fuel = BigInt(40)
  val maxCalls = 20000

  enum Outcome {
    case Value, Stuck, Skipped
  }

  /** Evaluates `e` (closed, in the fragment) with both evaluators, and fails if they disagree. */
  def compare(e: Expr, sp: S.Program, label: => String)(using symbols: Symbols): Outcome = {
    val ctx = TestContext(Options(Seq(evaluators.optMaxCalls(maxCalls))))
    val ev = evaluators.RecursiveEvaluator(InoxProgram(symbols), ctx)
    val reference = try ev.eval(e) catch {
      case _: StackOverflowError => return Outcome.Skipped
    }
    val ours = S.eval(sp, fuel, S.Nil(), expr(e).get)
    (reference, ours) match {
      case (_, S.OutOfFuel()) => Outcome.Skipped
      case (evaluators.EvaluationResults.RuntimeError(msg), _) if msg.startsWith("Exceeded") => Outcome.Skipped
      case (evaluators.EvaluationResults.Successful(v), S.Ok(w)) =>
        assert(value(v) == w, s"$label: ${e.asString}")
        Outcome.Value
      case (evaluators.EvaluationResults.RuntimeError(_), S.Stuck()) => Outcome.Stuck
      case (r, o) => fail(s"$label: ${e.asString} gives $r and $o in the semantics")
    }
  }

  /** Small values of type `t`, of ADT depth at most `depth`. */
  def values(t: Type, depth: Int, rnd: scala.util.Random)(using symbols: Symbols): scala.Option[Expr] = t match {
    case IntegerType() => scala.Some(IntegerLiteral(Seq(-17, -3, -2, -1, 0, 1, 2, 3, 5, 100)(rnd.nextInt(10))))
    case BooleanType() => scala.Some(BooleanLiteral(rnd.nextBoolean()))
    case UnitType() => scala.Some(UnitLiteral())
    case adt: ADTType =>
      val sort = adt.getSort
      val ctors = sort.constructors
      val leaves = ctors.filter(_.fields.forall(f => !f.tpe.isInstanceOf[ADTType] || f.tpe != adt))
      val pool = if (depth <= 0 && leaves.nonEmpty) leaves else ctors
      val c = pool(rnd.nextInt(pool.size))
      val args = c.fields.map(f => values(f.tpe, depth - 1, rnd))
      if (args.forall(_.isDefined) && depth > -3) scala.Some(ADT(c.id, adt.tps, args.flatten)) else scala.None
    case _ => scala.None
  }

  test("The generated evaluator is up to date with proofs/semantics.md") {
    val generated = Codegen.scala(Paths.get(Codegen.source))
    assert(generated == Files.readString(Paths.get(Codegen.scalaOutput)),
      "run `sbt proofs/run` to regenerate it")
  }

  test("Integer division and remainders are euclidean, and stuck on zero") {
    given Symbols = NoSymbols
    val sp = program(Map())
    def run(e: Expr) = S.eval(sp, fuel, S.Nil(), expr(e).get)
    for ((a, b, q, r) <- Seq((7, 2, 3, 1), (-7, 2, -4, 1), (7, -2, -3, 1), (-7, -2, 4, 1))) {
      val (x, y) = (IntegerLiteral(a), IntegerLiteral(b))
      assert(run(Division(x, y)) == S.Ok(S.IntV(q)))
      assert(run(Remainder(x, y)) == S.Ok(S.IntV(r)))
      assert(run(Modulo(x, y)) == S.Ok(S.IntV(r)))
      for (e <- Seq(Division(x, y), Remainder(x, y), Modulo(x, y)))
        assert(compare(e, sp, "division") == Outcome.Value)
    }
    for (e <- Seq(Division(IntegerLiteral(1), IntegerLiteral(0)), Modulo(IntegerLiteral(1), IntegerLiteral(0)))) {
      assert(run(e) == S.Stuck())
      assert(compare(e, sp, "division by zero") == Outcome.Stuck)
    }
  }

  test("Assumptions, errors, invariants, selectors and fuel") {
    import dsl._
    val (listId, nilId, consId) = (FreshIdentifier("List"), FreshIdentifier("Nil"), FreshIdentifier("Cons"))
    val (headId, tailId) = (FreshIdentifier("head"), FreshIdentifier("tail"))
    val List = mkSort(listId)() { _ => Seq(
      (nilId, Seq()),
      (consId, Seq(ValDef(headId, IntegerType()), ValDef(tailId, T(listId)()))))
    }
    val sizeId = FreshIdentifier("size")
    val size = mkFunDef(sizeId)() { _ =>
      (Seq("l" :: T(listId)()), IntegerType(), { case Seq(l) =>
        if_ (l.is(consId)) { E(BigInt(1)) + E(sizeId)(l.getField(tailId)) } else_ { E(BigInt(0)) }
      })
    }
    val loopId = FreshIdentifier("loop")
    val loop = mkFunDef(loopId)() { _ => (Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) => E(loopId)(x) }) }
    given symbols: Symbols = NoSymbols.withSorts(Seq(List)).withFunctions(Seq(size, loop))
    val sp = program(coveredFunctions)
    def cons(h: Int, t: Expr) = ADT(consId, Seq(), Seq(IntegerLiteral(h), t))
    val nil = ADT(nilId, Seq(), Seq())
    def run(e: Expr) = S.eval(sp, fuel, S.Nil(), expr(e).get)

    assert(run(E(sizeId)(cons(1, cons(2, nil)))) == S.Ok(S.IntV(2)))
    assert(run(ADTSelector(nil, headId)) == S.Stuck())
    assert(run(Assume(BooleanLiteral(false), IntegerLiteral(1))) == S.Stuck())
    assert(run(Error(IntegerType(), "e")) == S.Stuck())
    assert(run(E(loopId)(IntegerLiteral(0))) == S.OutOfFuel())
    // `false && error` doesn't evaluate the error
    assert(run(And(BooleanLiteral(false), Error(BooleanType(), "e"))) == S.Ok(S.BoolV(false)))
    for (e <- Seq(E(sizeId)(cons(1, cons(2, nil))), ADTSelector(nil, headId), IsConstructor(nil, consId),
                  Assume(BooleanLiteral(false), IntegerLiteral(1)), Error(IntegerType(), "e"),
                  And(BooleanLiteral(false), Error(BooleanType(), "e")),
                  Equals(cons(1, nil), cons(1, nil)), Equals(cons(1, nil), nil)))
      assert(compare(e, sp, "unit") != Outcome.Skipped)
  }

  test("The semantics agrees with RecursiveEvaluator on the functions of the regression files") {
    val root = Paths.get("../src/it/resources/regression")
    val files = scala.jdk.CollectionConverters.ListHasAsScala(
      Files.walk(root).sorted().toList).asScala.toSeq.filter { f =>
        val n = f.toString
        (n.endsWith(".tip") && !n.contains("PARSING")) || n.endsWith(".smt3")
      }
    assert(files.nonEmpty, s"no regression files under $root")
    val rnd = new scala.util.Random(0)
    var valueCount = 0
    var stuck = 0
    var skipped = 0
    var testedFunctions = 0
    for (file <- files) {
      val parsed = try {
        if (file.toString.endsWith(".tip")) tip.Parser(file.toFile).parseScript
        else smtlib3.Parser(file.toFile).parseScript
      } catch { case _: Throwable => Seq() }
      for ((p, _) <- parsed.take(1)) {
        given symbols: Symbols = p.symbols.asInstanceOf[Symbols]
        val covered = coveredFunctions
        val sp = program(covered)
        for (id <- covered.keys.toSeq.sortBy(_.uniqueName)) {
          // type parameters range over the integers here: evaluation doesn't depend on them
          val tps = symbols.getFunction(id).tparams.map(_ => IntegerType())
          val tfd = symbols.getFunction(id, tps)
          testedFunctions += 1
          for (_ <- 1 to (if (tfd.params.isEmpty) 1 else 30)) {
            val args = tfd.params.map(vd => values(vd.tpe, 3, rnd))
            // the invariants of the arguments' sorts must be in the fragment
            val invariants = args.flatten.flatMap(exprOps.collect[Identifier] {
              case ADT(c, _, _) => symbols.getConstructor(c).getSort.invariant.map(_.id).toSet
              case _ => Set()
            })
            if (args.forall(_.isDefined) && invariants.forall(covered.contains)) {
              compare(FunctionInvocation(id, tps, args.flatten), sp, file.getFileName.toString) match {
                case Outcome.Value => valueCount += 1
                case Outcome.Stuck => stuck += 1
                case Outcome.Skipped => skipped += 1
              }
            }
          }
        }
      }
    }
    info(s"${valueCount + stuck} calls agree ($valueCount on a value, $stuck stuck), $skipped skipped for fuel, " +
      s"over $testedFunctions functions of ${files.size} files")
    assert(valueCount >= 1000 && stuck >= 50, s"only $valueCount values and $stuck stuck calls compared")
  }
}
