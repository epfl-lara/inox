/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

import utils._

trait ADTManagers {
  val program: Program
  val context: Context

  import context._
  import program._
  import program.trees._
  import program.symbols._

  protected def unsupported(t: Tree, str: String): Nothing

  case class DataType(sym: Identifier, cases: Seq[Constructor]) extends Printable {
    def asString(implicit opts: PrinterOptions) = {
      "Datatype: " + sym.toString + "\n" + cases.map(c => " - " + c.asString(opts)).mkString("\n")
    }
  }

  case class Constructor(sym: Identifier, tpe: Type, fields: Seq[(Identifier, Type)]) extends Printable {
    def asString(implicit opts: PrinterOptions) = {
      sym.toString + " [" + tpe.asString(opts) + "] " + fields.map(f => f._1.toString + ": " + f._2.toString).mkString("(", ", ", ")")
    }
  }

  class ADTManager extends IncrementalStateWrapper {

    protected def freshId(id: Identifier): Identifier = freshId(id.name)

    protected def freshId(name: String): Identifier = FreshIdentifier(name)

    private val declared = new IncrementalSet[Type]
    protected val incrementals = Seq(declared)

    def types: Set[Type] = declared.toSet

    def declareADTs(tpe: Type, declare: Seq[(Type, DataType)] => Unit): Unit = {
      val deps = typeDependencies(tpe)
      val transitiveDeps: Map[Type, Set[Type]] = utils.fixpoint { (map: Map[Type, Set[Type]]) =>
        map.map {  case (tpe, types) => tpe -> (types ++ types.flatMap(map.getOrElse(_, Set.empty))) }
      } (deps)

      val sccs = SCC.scc(deps)

      // check whether all types can be defined
      for (scc <- sccs if scc.exists(tpe => (transitiveDeps(tpe) & scc).nonEmpty); tpe <- scc) tpe match {
        case t @ ((_: MapType) | (_: SetType) | (_: BagType)) =>
          unsupported(t, "Encountered ADT that can't be defined.\n" +
            "It has recursive references through non-structural types (such as arrays, maps, or sets): " +
            t.asString)
        case _ =>
      }

      for (scc <- sccs.map(scc => scc.map(bestRealType))) {

        val declarations = (for (tpe <- scc if !declared(tpe)) yield (tpe match {
          case adt: ADTType =>
            val tdef = adt.getADT
            if (!tdef.definition.isWellFormed) {
              unsupported(adt, "Not well-founded ADT:\n" + tdef.definition.asString)
            }

            val (root, deps) = tdef.root match {
              case tsort: TypedADTSort =>
                (tsort, tsort.constructors)
              case tcons: TypedADTConstructor =>
                (tcons, Seq(tcons))
            }

            Some(adt -> DataType(freshId(root.id), deps.map { tccd =>
              Constructor(freshId(tccd.id), tccd.toType, tccd.fields.map(vd => freshId(vd.id) -> vd.tpe))
            }))

          case TupleType(tps) =>
            val sym = freshId("tuple" + tps.size)

            Some(tpe -> DataType(sym, Seq(Constructor(freshId(sym.name), tpe, tps.zipWithIndex.map {
              case (tpe, i) => (freshId("_" + (i + 1)), tpe)
            }))))

          case UnitType =>
            Some(tpe -> DataType(freshId("Unit"), Seq(Constructor(freshId("Unit"), tpe, Nil))))

          case TypeParameter(id, _) =>
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
