/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

trait ADTManagers {
  val program: Program
  import program._
  import trees._

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

  class ADTManager(ctx: InoxContext) {
    val reporter = ctx.reporter

    protected def freshId(id: Identifier): Identifier = freshId(id.name)

    protected def freshId(name: String): Identifier = FreshIdentifier(name)

    protected def getHierarchy(ct: TypedClassDef): (TypedClassDef, Seq[TypedCaseClassDef]) = ct match {
      case acd: TypedAbstractClassDef =>
        (acd, acd.descendants)
      case ccd: TypedCaseClassDef =>
        (ccd, List(ccd))

    }

    protected var defined = Set[Type]()
    protected var locked = Set[Type]()

    protected var discovered = Map[Type, DataType]()

    def defineADT(t: Type): Either[Map[Type, DataType], Set[Type]] = {
      discovered = Map()
      locked = Set()

      findDependencies(t)

      val conflicts = discovered.keySet & locked

      if (conflicts(t)) {
        // There is no way to solve this, the type we requested is in conflict
        val str = "Encountered ADT that can't be defined.\n" +
          "It appears it has recursive references through non-structural types (such as arrays, maps, or sets)."
        val err = new Unsupported(t, str)(ctx)
        reporter.warning(err.getMessage)
        throw err
      } else {
        // We might be able to define some despite conflicts
        if (conflicts.isEmpty) {
          for ((t, dt) <- discovered) {
            defined += t
          }
          Left(discovered)
        } else {
          Right(conflicts)
        }
      }
    }

    def forEachType(t: Type, alreadyDone: Set[Type] = Set())(f: Type => Unit): Unit = if (!alreadyDone(t)) {
      t match {
        case NAryType(tps, builder) =>
          f(t)
          val alreadyDone2 = alreadyDone + t
          // note: each of the tps could be abstract classes in which case we need to
          // lock their dependencies, transitively.
          tps.foreach {
            case ct: ClassType =>
              val (root, sub) = getHierarchy(ct.lookupClass.get)
              sub.flatMap(_.fields.map(_.getType)).foreach(subt => forEachType(subt, alreadyDone2)(f))
            case othert =>
              forEachType(othert, alreadyDone2)(f)
          }
      }
    }

    protected def findDependencies(t: Type): Unit = t match {
      case _: SetType | _: MapType =>
        forEachType(t) { tpe =>
          if (!defined(tpe)) {
            locked += tpe
          }
        }

      case ct: ClassType =>
        val (root, sub) = getHierarchy(ct.lookupClass.get)

        if (!(discovered contains root.toType) && !(defined contains root.toType)) {
          val sym = freshId(root.id)

          val conss = sub.map { case cct =>
            Constructor(freshId(cct.id), cct.toType, cct.fields.map(vd => (freshId(vd.id), vd.getType)))
          }

          discovered += (root.toType -> DataType(sym, conss))

          // look for dependencies
          for (ct <- sub; f <- ct.fields) {
            findDependencies(f.getType)
          }
        }

      case tt@TupleType(bases) =>
        if (!(discovered contains t) && !(defined contains t)) {
          val sym = freshId("tuple" + bases.size)

          val c = Constructor(freshId(sym.name), tt, bases.zipWithIndex.map {
            case (tpe, i) => (freshId("_" + (i + 1)), tpe)
          })

          discovered += (tt -> DataType(sym, Seq(c)))

          for (b <- bases) {
            findDependencies(b)
          }
        }

      case UnitType =>
        if (!(discovered contains t) && !(defined contains t)) {
          discovered += (t -> DataType(freshId("Unit"), Seq(Constructor(freshId("Unit"), t, Nil))))
        }

      case tp@TypeParameter(id) =>
        if (!(discovered contains t) && !(defined contains t)) {
          val sym = freshId(id.name)

          val c = Constructor(freshId(sym.name), tp, List(
            (freshId("val"), IntegerType)
          ))

          discovered += (tp -> DataType(sym, Seq(c)))
        }

      case _ =>
    }
  }

}