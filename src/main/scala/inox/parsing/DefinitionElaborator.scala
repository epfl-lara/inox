/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package parsing

import scala.util.parsing.input._

trait DefinitionElaborators { self: Elaborators =>

  trait DefinitionElaborator { self0: Elaborator =>

    import DefinitionIR._

    def replaceHoles(definition: FunctionDefinition)(implicit holes: HoleValues): FunctionDefinition = definition match {
      case FunctionDefinition(id, tparams, params, returnType, body) => FunctionDefinition(
        replaceHoles(id),
        tparams.map(replaceHoles(_)),
        params.map(replaceHoles(_)),
        replaceHoles(returnType),
        replaceHoles(body))
    }

    def replaceHoles(definition: TypeDefinition)(implicit holes: HoleValues): TypeDefinition = definition match {
      case TypeDefinition(id, tparams, constructors) => TypeDefinition(
        replaceHoles(id),
        tparams.map(replaceHoles(_)),
        constructors.map {
          case (cid, cparams) => (replaceHoles(cid), cparams.map(replaceHoles(_)))
        })
    }

    def getFunction(fd: FunctionDefinition)(implicit store: Store): Constrained[trees.FunDef] = {
      for (ds <- getDefinitions(Seq(fd))) yield { implicit u => ds.head.asInstanceOf[trees.FunDef] }
    }

    def getSort(td: TypeDefinition)(implicit store: Store): Constrained[trees.ADTSort] = {
      for (ds <- getDefinitions(Seq(td))) yield { implicit u => ds.head.asInstanceOf[trees.ADTSort] }
    }

    def getDefinitions(definitions: Seq[Definition])(implicit store: Store): Constrained[Seq[trees.Definition]] = {

      // Check for duplicate definitions
      def duplicates(names: Seq[(String, Position)], symbols: Set[String]): Option[(String, Position)] = {
        names.groupBy(_._1).filter(p => symbols(p._1) || p._2.size > 1)
          .map { case (n, ps) => (n, ps.map(_._2).sortWith(_ < _).head) }.toSeq
          .sortWith((a,b) => a._2 < b._2).headOption
      }

      val duplicateTypeNames = duplicates(
        definitions.collect { case td: TypeDefinition => td.id.getName -> td.pos },
        symbols.sorts.keySet.map(_.name)
      )

      val duplicateFunctionNames = duplicates(
        definitions.flatMap {
          case fd: FunctionDefinition => Seq(fd.id.getName -> fd.pos)
          case td: TypeDefinition => td.constructors.map(p => p._1.getName -> td.pos)
        },
        symbols.sorts.values.flatMap(_.constructors.map(_.id.name)).toSet ++
        symbols.functions.keySet.map(_.name)
      )

      val duplicateFields: Option[ExprIR.Binding] = (
        definitions
          .flatMap {
            case td: TypeDefinition => td.constructors.flatMap(_._2)
            case _ => Seq()
          } ++
        symbols.sorts.values.toSeq
          .flatMap(_.constructors.flatMap(_.fields.map(_.id)))
          .map(id => ExprIR.UntypedBinding(ExprIR.IdentifierIdentifier(id))))
        .groupBy(binding => getIdentifier(binding))
        .filter(_._2.size > 1)
        .map { case (id, ids) => ids.find(_.pos != NoPosition).getOrElse(ids.head) }
        .headOption

      val sortsStore = definitions.foldLeft(store) {
        case (store, TypeDefinition(ident, tparams, _)) =>
          store + (ident.getName, new trees.ADTSort(
            getIdentifier(ident),
            tparams.map(id => trees.TypeParameterDef(trees.TypeParameter(getIdentifier(id), Seq()))),
            Seq(), Seq()
          ))
        case (store, _) => store
      }

      val newStore = definitions.foldLeft(sortsStore) {
        case (store, td: TypeDefinition) =>
          val sort = sortsStore getSort td.id.getName
          val tpStore = (td.tparams zip sort.typeArgs).foldLeft(store) {
            case (store, (id, tp)) => store + (id.getName, tp)
          }

          td.constructors.foldLeft(store) { case (store, (ident, params)) =>
            val id = getIdentifier(ident)
            val fields = params.map { binding =>
              val tpe = getAnnotatedType(binding) match {
                case Left(Some(t)) => getSimpleType(t)(tpStore)
                case Right(t) => t
                case _ => throw new Error("Unexpected untyped binding.")
              }
              trees.ValDef(getIdentifier(binding), tpe)
            }
            store + (ident.getName, sort, new trees.ADTConstructor(id, sort.id, fields))
          }

        case (store, fd: FunctionDefinition) =>
          val id = getIdentifier(fd.id)
          val tparams = fd.tparams.map(id => trees.TypeParameter(getIdentifier(id), Seq()))
          val tpds = tparams.map(trees.TypeParameterDef(_))
          val tpStore = (fd.tparams zip tparams).foldLeft(store) {
            case (store, (id, tp)) => store + (id.getName, tp)
          }

          val params = fd.params.map { binding =>
            val tpe = getAnnotatedType(binding) match {
              case Left(Some(t)) => getSimpleType(t)(tpStore)
              case Right(t) => t
              case _ => throw new Error("Unexpected untyped binding.")
            }
            trees.ValDef(getIdentifier(binding), tpe)
          }
          val resultType = getSimpleType(fd.returnType)(tpStore)
          val body = trees.Choose(trees.ValDef.fresh("res", resultType), trees.BooleanLiteral(true))
          store + (fd.id.getName, new trees.FunDef(id, tpds, params, resultType, body, Seq()))
      }

      Constrained.sequence({
        definitions.map {
          case td: TypeDefinition =>
            implicit val position: Position = td.pos
            val sort = newStore getSort td.id.getName
            val tpStore = (td.tparams zip sort.typeArgs).foldLeft(newStore) {
              case (store, (id, tp)) => store + (id.getName, tp)
            }

            Constrained.sequence({
              td.constructors.map { case (id, params) =>
                val (_, cons) = newStore getConstructor id.getName
                val (_, _, vds) = getExprBindings((params zip cons.fields).map {
                  case (binding, vd) => binding match {
                    case ExprIR.TypedBinding(_, tpe) => ExprIR.TypedBinding(ExprIR.IdentifierIdentifier(vd.id), tpe)
                    case ExprIR.UntypedBinding(_) => ExprIR.UntypedBinding(ExprIR.IdentifierIdentifier(vd.id))
                    case _ => throw new Error("Unexpected untyped binding.")
                  }
                })(tpStore, position)
                vds.transform(cons.id -> _)
              }
            }).transform({ constructors =>
              new trees.ADTSort(sort.id, sort.tparams, constructors.map {
                case (cid, params) => new trees.ADTConstructor(cid, sort.id, params)
              }, Seq())
            })

          case fd: FunctionDefinition =>
            implicit val position: Position = fd.pos
            val signature = newStore getFunction fd.id.getName
            val initStore = (fd.tparams zip signature.typeArgs).foldLeft(newStore) {
              case (store, (id, tp)) => store + (id.getName, tp)
            }

            val (bodyStore, _, vds) = getExprBindings((fd.params zip signature.params).map {
              case (binding, vd) => binding match {
                case ExprIR.TypedBinding(_, tpe) => ExprIR.TypedBinding(ExprIR.IdentifierIdentifier(vd.id), tpe)
                case ExprIR.UntypedBinding(_) => ExprIR.UntypedBinding(ExprIR.IdentifierIdentifier(vd.id))
                case _ => throw new Error("Unexpected untyped binding.")
              }
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
        "Duplicate field identifiers with name " + getIdentifier(duplicateFields.get).name + ".",
        duplicateFields.get.pos
      )
    }
  }
}
