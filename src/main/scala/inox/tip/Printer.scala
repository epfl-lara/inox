/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package tip

import ast.Identifier

import smtlib.parser.Terms.{Forall => SMTForall, Identifier => SMTIdentifier, _}
import smtlib.parser.Commands.{Constructor => SMTConstructor, _}
import smtlib.extensions.tip.Terms.{Lambda => SMTLambda, Application => SMTApplication, _}
import smtlib.extensions.tip.Commands._
import smtlib.Interpreter

import java.io.Writer
import scala.collection.mutable.{Map => MutableMap}

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

      smtlib.parser.CommandsResponses.Success
    }

    def free(): Unit = {
      writer.close()
    }

    def interrupt(): Unit = free()
  }

  def printScript(expr: Expr): Unit = {
    val tparams = exprOps.collect(e => typeParamsOf(e.getType))(expr)
    val bindings = exprOps.variablesOf(expr).map(v => v.id -> (id2sym(v.id): Term)).toMap
    val cmd = if (tparams.nonEmpty) {
      AssertPar(tparams.map(tp => id2sym(tp.id)).toSeq, toSMT(expr)(bindings))
    } else {
      Assert(toSMT(expr)(bindings))
    }
    emit(cmd)
  }

  protected def liftADTType(adt: ADTType): Type = adt.getADT.definition.typed.toType

  protected val tuples: MutableMap[Int, TupleType] = MutableMap.empty

  override protected def declareStructuralSort(t: Type): Sort = t match {
    case adt: ADTType =>
      adtManager.declareADTs(liftADTType(adt), declareDatatypes)
      val tpSorts = adt.tps.map(declareSort)
      Sort(SMTIdentifier(id2sym(adt.id)), tpSorts)

    case TupleType(ts) =>
      val tpe = tuples.getOrElseUpdate(ts.size, {
        TupleType(List.range(0, ts.size).map(i => TypeParameter.fresh("A" + i)))
      })
      adtManager.declareADTs(tpe, declareDatatypes)
      val tpSorts = ts.map(declareSort)
      Sort(sorts.toB(tpe).id, tpSorts)

    case _ => super.declareStructuralSort(t)
  }

  override protected def declareDatatypes(datatypes: Seq[(Type, DataType)]): Unit = {
    for ((tpe, DataType(id, _)) <- datatypes) {
      sorts += tpe -> Sort(SMTIdentifier(id2sym(id)))
    }

    val (generics, adts) = datatypes.partition {
      case (_: TypeParameter, _) => true
      case _ => false
    }

    val genericSyms = generics.map { case (_, DataType(id, _)) => id2sym(id) }

    if (adts.nonEmpty) {
      emit(DeclareDatatypesPar(genericSyms,
        (for ((tpe, DataType(sym, cases)) <- adts.toList) yield {
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

  override protected def toSMT(e: Expr)(implicit bindings: Map[Identifier, Term]): Term = e match {
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
      Exists(param, params, toSMT(body)(bindings ++ newBindings))

    case Application(caller, args) =>
      SMTApplication(toSMT(caller), args.map(toSMT))

    case Assume(pred, body) =>
      FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("assume")), None),
        Seq(toSMT(pred), toSMT(body))
      )

    case _ => super.toSMT(e)
  }
}

