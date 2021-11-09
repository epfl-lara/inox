/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers

import utils._

trait ADTManagers {
  val program: Program
  val context: Context

  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  protected def unsupported(t: Tree, str: String): Nothing

  case class DataType(sym: Identifier, cases: Seq[Constructor]) extends Printable {
    def asString(using opts: PrinterOptions) = {
      "Datatype: " + sym.asString + "\n" + cases.map(c => " - " + c.asString).mkString("\n")
    }
  }

  sealed abstract class ConsType extends Tree {
    override def asString(using PrinterOptions) = this match {
      case ADTCons(id, tps) =>
        id.asString +
        (if (tps.nonEmpty) tps.map(_.asString).mkString("[", ",", "]") else "")
      case TupleCons(tps) => TupleType(tps).asString
      case TypeParameterCons(tp) => tp.asString
      case UnitCons => UnitType().asString
    }

    def getType: Type
  }
  case class ADTCons(id: Identifier, tps: Seq[Type]) extends ConsType {
    override def getType: ADTType = ADTType(getConstructor(id).sort, tps)
  }
  case class TupleCons(tps: Seq[Type]) extends ConsType {
    override def getType: TupleType = TupleType(tps)
  }
  case class TypeParameterCons(tp: TypeParameter) extends ConsType {
    override def getType: TypeParameter = tp
  }
  case object UnitCons extends ConsType {
    override def getType: UnitType = UnitType()
  }

  case class Constructor(sym: Identifier, tpe: ConsType, fields: Seq[(Identifier, Type)]) extends Printable {
    def asString(using PrinterOptions) = {
      sym.asString +
      " [" + tpe.asString + "] " +
      fields.map(f => f._1.asString + ": " + f._2.asString).mkString("(", ", ", ")")
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

      for (scc <- sccs) {

        val declarations = (for (tpe <- scc if !declared(tpe)) yield (tpe match {
          case adt: ADTType =>
            val tsort = adt.getSort
            if (!tsort.definition.isWellFormed) {
              unsupported(adt, "Not well-founded ADT:\n" + tsort.definition.asString)
            }

            Some(adt -> DataType(freshId(tsort.id), tsort.constructors.map { tcons =>
              Constructor(
                freshId(tcons.id),
                ADTCons(tcons.id, adt.tps),
                tcons.fields.map(vd => freshId(vd.id) -> vd.getType))
            }))

          case TupleType(tps) =>
            val sym = freshId("tuple" + tps.size)

            Some(tpe -> DataType(sym, Seq(Constructor(freshId(sym.name), TupleCons(tps), tps.zipWithIndex.map {
              case (tpe, i) => (freshId("_" + (i + 1)), tpe)
            }))))

          case UnitType() =>
            Some(tpe -> DataType(freshId("Unit"), Seq(Constructor(freshId("Unit"), UnitCons, Nil))))

          case tp @ TypeParameter(id, _) =>
            val sym = freshId(id.name)

            Some(tpe -> DataType(sym, Seq(Constructor(freshId(sym.name), TypeParameterCons(tp), List(
              (freshId("val"), IntegerType())
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
