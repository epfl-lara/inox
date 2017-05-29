/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package tip

import smtlib.trees.Terms.{Forall => SMTForall, Identifier => SMTIdentifier, _}
import smtlib.trees.Commands.{Constructor => SMTConstructor, _}
import smtlib.theories._
import smtlib.theories.experimental._
import smtlib.extensions.tip.Terms.{Lambda => SMTLambda, Application => SMTApplication, _}
import smtlib.extensions.tip.Commands._
import smtlib.Interpreter

import Terms.{Assume => SMTAssume, Choose => SMTChoose}
import Commands._

import java.io.Writer
import scala.collection.mutable.{Map => MutableMap}

import utils._

class Printer(val program: InoxProgram, writer: Writer) extends solvers.smtlib.SMTLIBTarget {
  import program._
  import program.trees._
  import program.symbols._

  def targetName = "tip"

  protected def unsupported(t: Tree, str: String): Nothing = {
    throw new Unsupported(t, s"(of class ${t.getClass}) is unsupported by TIP printer:\n  " + str)
  }

  /* Note that we are NOT relying on a "real" interpreter here. We just
   * need the printer for calls to [[emit]] to function correctly. */
  protected val interpreter = new Interpreter {
    // the parser should never be used
    val parser: smtlib.parser.Parser = null

    object printer extends smtlib.printer.Printer {
      val name: String = "tip-printer"
      protected def newContext(writer: Writer) = new smtlib.printer.PrintingContext(writer)
    }

    def eval(cmd: SExpr): SExpr = {
      printer.printSExpr(cmd, writer)
      writer.write("\n")
      writer.flush()

      smtlib.trees.CommandsResponses.Success
    }

    def free(): Unit = {
      writer.close()
    }

    def interrupt(): Unit = free()
  }

  protected val semantics: program.Semantics = program.getSemantics

  protected val extraVars = new Bijection[Variable, SSymbol]

  def printScript(expr: Expr): Unit = {
    val tparams = exprOps.collect(e => typeParamsOf(e.getType))(expr)
    val cmd = if (tparams.nonEmpty) {
      AssertPar(tparams.map(tp => id2sym(tp.id)).toSeq, toSMT(expr)(Map.empty))
    } else {
      Assert(toSMT(expr)(Map.empty))
    }

    val invariants = adtManager.types
      .collect { case adt: ADTType => adt }
      .map(_.getADT.definition)
      .flatMap(_.invariant)

    for (fd <- invariants) {
      val Seq(vd) = fd.params
      if (fd.tparams.isEmpty) {
        emit(DatatypeInvariant(
          id2sym(vd.id),
          declareSort(vd.tpe),
          toSMT(fd.fullBody)(Map(vd.id -> id2sym(vd.id)))
        ))
      } else {
        val tps = fd.tparams.map(tpd => declareSort(tpd.tp).id.symbol)
        emit(DatatypeInvariantPar(
          tps,
          id2sym(vd.id),
          declareSort(vd.tpe),
          toSMT(fd.fullBody)(Map(vd.id -> id2sym(vd.id)))
        ))
      }
    }

    emit(cmd)
  }

  def emit(s: String): Unit = writer.write(s)

  protected def liftADTType(adt: ADTType): Type = adt.getADT.definition.root.typed.toType

  protected val tuples: MutableMap[Int, TupleType] = MutableMap.empty

  override protected def computeSort(t: Type): Sort = t match {
    case FunctionType(from, to) =>
      Sort(SimpleIdentifier(SSymbol("=>")), from.map(declareSort) :+ declareSort(to))

    case BagType(base) =>
      Bags.BagSort(declareSort(base))

    case SetType(base) =>
      Sets.SetSort(declareSort(base))

    case StringType =>
      Strings.StringSort()

    case _ => super.computeSort(t)
  }

  override protected def declareStructuralSort(t: Type): Sort = t match {
    case adt: ADTType =>
      val tpe = liftADTType(adt)
      adtManager.declareADTs(tpe, declareDatatypes)
      val tpSorts = adt.tps.map(declareSort)
      val Sort(id, _) = sorts.toB(tpe)
      Sort(id, tpSorts)

    case TupleType(ts) =>
      val tpe = tuples.getOrElseUpdate(ts.size, {
        TupleType(List.range(0, ts.size).map(i => TypeParameter.fresh("A" + i)))
      })
      adtManager.declareADTs(tpe, declareDatatypes)
      val tpSorts = ts.map(declareSort)
      Sort(sorts.toB(tpe).id, tpSorts)

    case tp: TypeParameter =>
      Sort(SMTIdentifier(id2sym(tp.id)), Nil)

    case _ => super.declareStructuralSort(t)
  }

  override protected def declareDatatypes(datatypes: Seq[(Type, DataType)]): Unit = {
    val adts = datatypes.filterNot {
      case (_: TypeParameter, _) => true
      case _ => false
    }

    val (ours, externals) = adts.partition {
      case (adt: ADTType, _) => adt == adt.getADT.definition.typed.toType
      case (tpe @ TupleType(tps), _) => Some(tpe) == tuples.get(tps.size)
      case _ => true
    }

    for ((tpe, DataType(id, _)) <- ours) {
      val tparams: Seq[TypeParameter] = tpe match {
        case ADTType(_, tps) => tps.map(_.asInstanceOf[TypeParameter])
        case TupleType(tps) => tps.map(_.asInstanceOf[TypeParameter])
        case _ => Seq.empty
      }

      val tpSorts = tparams.map(tp => Sort(SMTIdentifier(id2sym(tp.id))))
      sorts += tpe -> Sort(SMTIdentifier(id2sym(id)), tpSorts)
    }

    val generics = ours.flatMap { case (tp, _) => typeParamsOf(tp) }.toSet
    val genericSyms = generics.map(tp => id2sym(tp.id))

    if (ours.nonEmpty) {
      emit(DeclareDatatypesPar(genericSyms.toList,
        (for ((tpe, DataType(sym, cases)) <- ours.toList) yield {
          id2sym(sym) -> (for (c <- cases) yield {
            val s = id2sym(c.sym)

            testers += c.tpe -> SSymbol("is-" + s.name)
            constructors += c.tpe -> s

            SMTConstructor(s, c.fields.zipWithIndex.map { case ((cs, t), i) =>
              selectors += (c.tpe, i) -> id2sym(cs)
              (id2sym(cs), declareSort(t))
            })
          }).toList
        }).toList
      ))
    }
  }

  override protected def declareFunction(tfd: TypedFunDef): SSymbol = {
    val fd = tfd.fd

    functions.getB(fd.typed) match {
      case Some(sym) => sym
      case None =>
        functions += fd.typed -> id2sym(fd.id)

        val scc = transitiveCallees(fd).filter(fd2 => transitivelyCalls(fd2, fd))
        if (scc.size <= 1) {
          val (sym, params, returnSort, body) = (
            id2sym(fd.id),
            fd.params.map(vd => SortedVar(id2sym(vd.id), declareSort(vd.tpe))),
            declareSort(fd.returnType),
            toSMT(fd.fullBody)(fd.params.map(vd => vd.id -> (id2sym(vd.id): Term)).toMap)
          )

          val tps = fd.tparams.map(tpd => declareSort(tpd.tp).id.symbol)

          emit((scc.isEmpty, tps.isEmpty) match {
            case (true, true) => DefineFun(FunDef(sym, params, returnSort, body))
            case (false, true) => DefineFunRec(FunDef(sym, params, returnSort, body))
            case (true, false) => DefineFunPar(tps, FunDef(sym, params, returnSort, body))
            case (false, false) => DefineFunRecPar(tps, FunDef(sym, params, returnSort, body))
          })
        } else {
          functions ++= scc.toList.map(fd => fd.typed -> id2sym(fd.id))

          val (decs, bodies) = (for (fd <- scc.toList) yield {
            val (sym, params, returnSort) = (
              id2sym(fd.id),
              fd.params.map(vd => SortedVar(id2sym(vd.id), declareSort(vd.tpe))),
              declareSort(fd.returnType)
            )

            val tps = fd.tparams.map(tpd => declareSort(tpd.tp).id.symbol)

            val dec = if (tps.isEmpty) {
              Right(FunDec(sym, params, returnSort))
            } else {
              Left(FunDecPar(tps, sym, params, returnSort))
            }

            val body = toSMT(fd.fullBody)(fd.params.map(vd => vd.id -> (id2sym(vd.id): Term)).toMap)
            (dec, body)
          }).unzip

          emit(if (decs.exists(_.isLeft)) {
            DefineFunsRecPar(decs, bodies)
          } else {
            DefineFunsRec(decs.map(_.right.get), bodies)
          })
        }

        id2sym(fd.id)
    }
  }

  override protected def toSMT(e: Expr)(implicit bindings: Map[Identifier, Term]): Term = e match {
    case v @ Variable(id, tp, flags) =>
      val sort = declareSort(tp)
      bindings.get(id) orElse variables.getB(v).map(s => s: Term) getOrElse {
        val tps = typeParamsOf(tp).toSeq
        val sym = extraVars.cachedB(v) {
          val sym = id2sym(id)
          emit(if (tps.nonEmpty) {
            DeclareConstPar(tps.map(tp => id2sym(tp.id)), sym, sort)
          } else {
            DeclareConst(sym, sort)
          })
          sym
        }

        if (tps.nonEmpty) QualifiedIdentifier(SMTIdentifier(sym), Some(sort))
        else QualifiedIdentifier(SMTIdentifier(sym), None)
      }

    case Lambda(args, body) =>
      val (newBindings, params) = args.map { vd =>
        val sym = id2sym(vd.id)
        (vd.id -> (sym: Term), SortedVar(sym, declareSort(vd.tpe)))
      }.unzip
      SMTLambda(params, toSMT(body)(bindings ++ newBindings))

    case Forall(args, body) =>
      val (newBindings, param +: params) = args.map { vd =>
        val sym = id2sym(vd.id)
        (vd.id -> (sym: Term), SortedVar(sym, declareSort(vd.tpe)))
      }.unzip
      SMTForall(param, params, toSMT(body)(bindings ++ newBindings))

    case Not(Forall(args, body)) =>
      val (newBindings, param +: params) = args.map { vd =>
        val sym = id2sym(vd.id)
        (vd.id -> (sym: Term), SortedVar(sym, declareSort(vd.tpe)))
      }.unzip
      Exists(param, params, toSMT(Not(body))(bindings ++ newBindings))

    case Application(caller, args) => SMTApplication(toSMT(caller), args.map(toSMT))

    case Assume(pred, body) => SMTAssume(toSMT(pred), toSMT(body))

    case FiniteBag(elems, base) =>
      elems.foldLeft(Bags.EmptyBag(declareSort(base))) { case (b, (k, v)) =>
        Bags.Union(b, Bags.Singleton(toSMT(k), toSMT(v)))
      }

    case BagAdd(bag, elem) => Bags.Insert(toSMT(bag), toSMT(elem))
    case MultiplicityInBag(elem, bag) => Bags.Multiplicity(toSMT(elem), toSMT(bag))
    case BagUnion(b1, b2) => Bags.Union(toSMT(b1), toSMT(b2))
    case BagIntersection(b1, b2) => Bags.Intersection(toSMT(b1), toSMT(b2))
    case BagDifference(b1, b2) => Bags.Difference(toSMT(b1), toSMT(b2))

    case FiniteSet(elems, base) =>
      val empty = Sets.EmptySet(declareSort(base))
      elems match {
        case x :: xs => Sets.Insert(empty, toSMT(x), xs.map(toSMT) : _*)
        case _ => empty
      }

    case SetAdd(set, elem) => Sets.Insert(toSMT(set), toSMT(elem))
    case ElementOfSet(elem, set) => Sets.Member(toSMT(elem), toSMT(set))
    case SubsetOf(s1, s2) => Sets.Subset(toSMT(s1), toSMT(s2))
    case SetIntersection(s1, s2) => Sets.Intersection(toSMT(s1), toSMT(s2))
    case SetUnion(s1, s2) => Sets.Union(toSMT(s1), toSMT(s2))
    case SetDifference(s1, s2) => Sets.Setminus(toSMT(s1), toSMT(s2))

    case StringLiteral(value) => Strings.StringLit(value)
    case StringConcat(s1, s2) => Strings.Concat(toSMT(s1), toSMT(s2))
    case SubString(s, start, end) => Strings.Substring(toSMT(s), toSMT(start), toSMT(end))
    case StringLength(s) => Strings.Length(toSMT(s))

    case ADT(tpe @ ADTType(id, tps), es) =>
      val d = tpe.getADT.definition
      val tcons = d.typed(d.root.typeArgs).toConstructor
      val adt = tcons.toType
      val sort = declareSort(tpe)
      val constructor = constructors.toB(adt)
      if (es.isEmpty) {
        if (tcons.tps.nonEmpty) QualifiedIdentifier(SMTIdentifier(constructor), Some(sort))
        else constructor
      } else {
        FunctionApplication(constructor, es.map(toSMT))
      }

    case s @ ADTSelector(e, id) =>
      val d = e.getType.asInstanceOf[ADTType].getADT.definition
      val tcons = d.typed(d.root.typeArgs).toConstructor
      val adt = tcons.toType
      declareSort(adt)
      val selector = selectors.toB(adt -> s.selectorIndex)
      FunctionApplication(selector, Seq(toSMT(e)))

    case IsInstanceOf(e, t: ADTType) =>
      val d = t.getADT.definition
      val tdef = d.typed(d.root.typeArgs)
      if (tdef.definition.isSort) {
        toSMT(BooleanLiteral(true))
      } else {
        val adt = tdef.toConstructor.toType
        declareSort(adt)
        val tester = testers.toB(adt)
        FunctionApplication(tester, Seq(toSMT(e)))
      }

    case t @ Tuple(es) =>
      declareSort(t.getType)
      val tpe = tuples(es.size)
      val constructor = constructors.toB(tpe)
      FunctionApplication(constructor, es.map(toSMT))

    case ts @ TupleSelect(t, i) =>
      declareSort(t.getType)
      val tpe = tuples(t.getType.asInstanceOf[TupleType].dimension)
      val selector = selectors.toB((tpe, i - 1))
      FunctionApplication(selector, Seq(toSMT(t)))

    case fi @ FunctionInvocation(id, tps, args) =>
      val tfd = fi.tfd
      val retTpArgs = typeParamsOf(tfd.fd.returnType)
      val paramTpArgs = tfd.fd.params.flatMap(vd => typeParamsOf(vd.tpe)).toSet
      if ((retTpArgs -- paramTpArgs).nonEmpty) {
        val caller = QualifiedIdentifier(
          SMTIdentifier(declareFunction(tfd)),
          Some(declareSort(tfd.returnType))
        )
        if (args.isEmpty) caller
        else FunctionApplication(caller, args.map(toSMT))
      } else {
        super.toSMT(e)
      }

    case Choose(vd, pred) =>
      val sym = id2sym(vd.id)
      val sort = declareSort(vd.tpe)
      SMTChoose(sym, declareSort(vd.tpe), toSMT(pred)(bindings + (vd.id -> (sym: Term))))

    case _ => super.toSMT(e)
  }
}

