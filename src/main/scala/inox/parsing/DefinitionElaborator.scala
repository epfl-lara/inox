/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package parsing

import scala.util.parsing.input._

trait DefinitionElaborators { self: Elaborators =>

  trait DefinitionElaborator { self0: Elaborator =>

    import DefinitionIR._

    def getFunction(fd: FunDef)(implicit store: Store): Constrained[trees.FunDef] = {
      for (ds <- getDefinitions(Seq(fd))) yield { implicit u => ds.head.asInstanceOf[trees.FunDef] }
    }

    def getSort(td: TypeDef)(implicit store: Store): Constrained[trees.ADTSort] = {
      for (ds <- getDefinitions(Seq(td))) yield { implicit u => ds.head.asInstanceOf[trees.ADTSort] }
    }

    def getDefinitions(definitions: Seq[Definition]): Constrained[Seq[trees.Definition]] = {

      // Check for duplicate definitions
      def duplicates(names: Seq[(String, Position)], symbols: Set[String]): Option[(String, Position)] = {
        names.groupBy(_._1).filter(p => symbols(p._1) || p._2.size > 1)
          .map { case (n, ps) => (n, ps.map(_._2).sortWith(_ < _).head) }.toSeq
          .sortWith((a,b) => a._2 < b._2).headOption
      }

      val duplicateTypeNames = duplicates(
        definitions.collect { case td: TypeDef => td.id.getName -> td.pos },
        symbols.sorts.keySet.map(_.name)
      )

      val duplicateFunctionNames = duplicates(
        definitions.flatMap {
          case fd: FunDef => Seq(fd.id.getName -> fd.pos)
          case td: TypeDef => td.constructors.map(p => p._1.getName -> td.pos)
        },
        symbols.sorts.values.flatMap(_.constructors.map(_.id.name)).toSet ++
        symbols.functions.keySet.map(_.name)
      )

      val duplicateFields: Option[ExprIR.IdentifierIdentifier] = (
        definitions
          .flatMap {
            case td: TypeDef => td.constructors.flatMap(_._2.map(_._1))
            case _ => Seq()
          }.collect { case ident @ ExprIR.IdentifierIdentifier(_) => ident } ++
        symbols.sorts.values.toSeq
          .flatMap(_.constructors.flatMap(_.fields.map(_.id)))
          .map(id => ExprIR.IdentifierIdentifier(id)))
        .groupBy(id => id)
        .filter(_._2.size > 1)
        .map { case (id, ids) => ids.find(_.pos != NoPosition).getOrElse(id) }
        .headOption

      val sortsStore = definitions.foldLeft(Store.empty) {
        case (store, TypeDef(ident, tparams, _)) =>
          store + (ident.getName, new trees.ADTSort(
            getIdentifier(ident),
            tparams.map(id => trees.TypeParameterDef(trees.TypeParameter(getIdentifier(id), Seq()))),
            Seq(), Seq()
          ))
        case (store, _) => store
      }

      val newStore = definitions.foldLeft(sortsStore) {
        case (store, td: TypeDef) =>
          val sort = sortsStore getSort td.id.getName
          val tpStore = (td.tparams zip sort.typeArgs).foldLeft(store) {
            case (store, (id, tp)) => store + (id.getName, tp)
          }

          td.constructors.foldLeft(store) { case (store, (ident, params)) =>
            val id = getIdentifier(ident)
            val fields = params.map { case (ident, tpe) =>
              trees.ValDef(getIdentifier(ident), getSimpleType(tpe)(tpStore))
            }
            store + (ident.getName, sort, new trees.ADTConstructor(id, sort.id, fields))
          }

        case (store, fd: FunDef) =>
          val id = getIdentifier(fd.id)
          val tparams = fd.tparams.map(id => trees.TypeParameter(getIdentifier(id), Seq()))
          val tpds = tparams.map(trees.TypeParameterDef(_))
          val tpStore = (fd.tparams zip tparams).foldLeft(store) {
            case (store, (id, tp)) => store + (id.getName, tp)
          }

          val params = fd.params.map(p => trees.ValDef(getIdentifier(p._1), getSimpleType(p._2)(tpStore)))
          val resultType = getSimpleType(fd.returnType)(tpStore)
          val body = trees.Choose(trees.ValDef.fresh("res", resultType), trees.BooleanLiteral(true))
          store + (fd.id.getName, new trees.FunDef(id, tpds, params, resultType, body, Seq()))
      }

      Constrained.sequence({
        definitions.map {
          case td: TypeDef =>
            implicit val position: Position = td.pos
            val sort = newStore getSort td.id.getName
            val tpStore = (td.tparams zip sort.typeArgs).foldLeft(newStore) {
              case (store, (id, tp)) => store + (id.getName, tp)
            }

            Constrained.sequence({
              (td.constructors zip sort.constructors).map { case ((_, params), cons) =>
                val (_, _, vds) = getExprBindings((params zip cons.fields).map {
                  case ((_, tpe), vd) => (ExprIR.IdentifierIdentifier(vd.id), Some(tpe))
                })(tpStore, position)
                vds.transform(cons.id -> _)
              }
            }).transform({ constructors =>
              new trees.ADTSort(sort.id, sort.tparams, constructors.map {
                case (cid, params) => new trees.ADTConstructor(cid, sort.id, params)
              }, Seq())
            })

          case fd: FunDef =>
            implicit val position: Position = fd.pos
            val signature = newStore getFunction fd.id.getName
            val initStore = (fd.tparams zip signature.typeArgs).foldLeft(newStore) {
              case (store, (id, tp)) => store + (id.getName, tp)
            }

            val (bodyStore, _, vds) = getExprBindings((fd.params zip signature.params).map {
              case ((_, tpe), vd) => (ExprIR.IdentifierIdentifier(vd.id), Some(tpe))
            })(initStore, position)

            val returnType = Unknown.fresh

            (for {
              params <- vds
              tpe <- getType(fd.returnType)(bodyStore)
              body <- getExpr(fd.body, returnType)(bodyStore)
            } yield { implicit u =>
              new trees.FunDef(signature.id, signature.tparams, params, tpe, body, Seq())
            }).addConstraint({
              Constraint.equal(returnType, signature.returnType)
            })
        }
      }).checkImmediate(
        duplicateTypeNames.isEmpty,
        "Multiple type definitions with name " + duplicateTypeNames.get._1 + ".",
        duplicateTypeNames.get._2
      ).checkImmediate(
        duplicateFunctionNames.isEmpty,
        "Multiple function definitions with name " + duplicateFunctionNames.get._1 + ".",
        duplicateFunctionNames.get._2
      ).checkImmediate(
        duplicateFields.isEmpty,
        "Duplicate field identifiers with name " + duplicateFields.get.getName + ".",
        duplicateFields.get.pos
      )
    }
  }
}
