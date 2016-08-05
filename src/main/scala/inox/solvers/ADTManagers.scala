/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

import utils._

trait ADTManagers {
  val program: Program
  import program._
  import program.trees._
  import program.symbols._

  case class DataType(sym: Identifier, cases: Seq[Constructor]) extends Printable {
    def asString(implicit opts: PrinterOptions) = {
      "Datatype: " + sym.asString(opts) + "\n" + cases.map(c => " - " + c.asString(opts)).mkString("\n")
    }
  }

  case class Constructor(sym: Identifier, tpe: Type, fields: Seq[(Identifier, Type)]) extends Printable {
    def asString(implicit opts: PrinterOptions) = {
      sym.asString(opts) + " [" + tpe.asString(opts) + "] " + fields.map(f => f._1.asString(opts) + ": " + f._2.asString(opts)).mkString("(", ", ", ")")
    }
  }

  class ADTManager extends IncrementalStateWrapper {

    protected def freshId(id: Identifier): Identifier = freshId(id.name)

    protected def freshId(name: String): Identifier = FreshIdentifier(name)

    private val declared = new IncrementalSet[Type]
    protected val incrementals = Seq(declared)

    def declareADTs(tpe: Type, declare: Seq[(Type, DataType)] => Unit): Unit = {
      val deps = typeDependencies(tpe)
      val transitiveDeps: Map[Type, Set[Type]] = utils.fixpoint { (map: Map[Type, Set[Type]]) =>
        map.map {  case (tpe, types) => tpe -> (types ++ types.flatMap(map.getOrElse(_, Set.empty))) }
      } (deps)

      val sccs = SCC.scc(deps)

      // check whether all types can be defined
      for (scc <- sccs if scc.exists(tpe => (transitiveDeps(tpe) & scc).nonEmpty); tpe <- scc) tpe match {
        case t @ ((_: MapType) | (_: SetType) | (_: BagType)) =>
          val str = "Encountered ADT that can't be defined.\n" +
            "It appears it has recursive references through non-structural types (such as arrays, maps, or sets)."
          val err = new Unsupported(t, str)
          ctx.reporter.warning(err.getMessage)
          throw err
        case _ =>
      }

      for (scc <- sccs) {

        val declarations = (for (tpe <- scc if !declared(tpe)) yield (tpe match {
          case ct: ClassType =>
            val (root, deps) = ct.tcd.root match {
              case tacd: TypedAbstractClassDef =>
                (tacd, tacd.descendants)
              case tccd: TypedCaseClassDef =>
                (tccd, Seq(tccd))
            }

            Some(ct -> DataType(freshId(root.id), deps.map { tccd =>
              Constructor(freshId(tccd.id), tccd.toType, tccd.fields.map(vd => freshId(vd.id) -> vd.tpe))
            }))

          case TupleType(tps) =>
            val sym = freshId("tuple" + tps.size)

            Some(tpe -> DataType(sym, Seq(Constructor(freshId(sym.name), tpe, tps.zipWithIndex.map {
              case (tpe, i) => (freshId("_" + (i + 1)), tpe)
            }))))

          case UnitType =>
            Some(tpe -> DataType(freshId("Unit"), Seq(Constructor(freshId("Unit"), tpe, Nil))))

          case TypeParameter(id) =>
            val sym = freshId(id.name)

            Some(tpe -> DataType(sym, Seq(Constructor(freshId(sym.name), tpe, List(
              (freshId("val"), IntegerType)
            )))))

          case _ => None
        })).flatten

        if (declarations.nonEmpty) {
          declare(declarations.toSeq)
          declared ++= declarations.map(_._1)
        }
      }
    }
  }
}
