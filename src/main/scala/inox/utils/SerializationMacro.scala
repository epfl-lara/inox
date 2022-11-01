/* Copyright 2009-2021 EPFL, Lausanne */

package inox.utils

import java.io.{InputStream, OutputStream}
import java.nio.charset.StandardCharsets
import scala.quoted._

/**
  * Macro for creating Serializer for Inox AST.
  *
  * Due to technical limitations, the return type is approximated with a general type projection
  * as opposed to being a path-dependent type over `inoxSerializer`.
  */
inline def inoxClassSerializerMacro[T](inline inoxSerializer: InoxSerializer, inline id: Int): InoxSerializer#Serializer[T] =
  ${ inoxClassSerializerMacroImpl[T]('inoxSerializer, 'id) }

// This dummy function delegates the actual work to `classSerializerMacroWorkhorse`
def inoxClassSerializerMacroImpl[T](inoxSerializer: Expr[InoxSerializer], id: Expr[Int])
                                   (using Quotes, Type[T]): Expr[InoxSerializer#Serializer[T]] = {
  import quotes.reflect._
  // Prefixes we would like to substitute by `InoxSerializer.this.trees`
  // For instance, if we see the type `inox.ast.Expressions.Assume`,
  // we replace it with `InoxSerializer.this.trees.Assume`.
  // (see docstring of classSerializerMacroWorkhorse for an actual example)
  val prefixesToSubst = Set(
    This(TypeTree.of[inox.ast.Expressions].tpe.typeSymbol).tpe,
    This(TypeTree.of[inox.ast.Types].tpe.typeSymbol).tpe,
    This(TypeTree.of[inox.ast.Definitions].tpe.typeSymbol).tpe
  )

  classSerializerMacroWorkhorse(inoxSerializer, id)(prefixesToSubst)
}

/**
  * Generate a `Serializer` for a given `T`.
  *
  * For instance, if `T` is inox.ast.Expression.Assume, the following code is generated:
  *
  * {{{
  * // Note that we assume the macro is called within `InoxSerializer` to be able to refer to its `this`.
  * new InoxSerializer.this.Serializer[InoxSerializer.this.trees.Assume](id) {
  *    override def write(instance: InoxSerializer.this.trees.Assume, out: OutputStream): Unit = {
  *      InoxSerializer.this.writeObject(instance.pred, out)
  *      InoxSerializer.this.writeObject(instance.body, out)
  *    }
  *    override def read(in: InputStream): InoxSerializer.this.trees.Assume = {
  *      val pred = InoxSerializer.this.readObject(in).asInstanceOf[InoxSerializer.this.trees.Expr]
  *      val body = InoxSerializer.this.readObject(in).asInstanceOf[InoxSerializer.this.trees.Expr]
  *      new InoxSerializer.this.trees.Assume(pred, body)
  *    }
  * }
  * }}}
  */
def classSerializerMacroWorkhorse[T](inoxSerializer: Expr[InoxSerializer], id: Expr[Int])
                                    (using q: Quotes, t: Type[T])
                                    (prefixesToSubst: Set[q.reflect.TypeRepr]): Expr[InoxSerializer#Serializer[T]] = {
  import quotes.reflect._

  // First, get the class symbol of the type for which we would like to generate a Serializer.
  val (clsSym, tySubstArg) = TypeTree.of[T].tpe match {
    // e.g. if we have class Foo and T = Foo, we would match this branch
    case tr: TypeRef => (tr.classSymbol.get, List.empty[(Symbol, TypeRef)])
    // e.g. if we have class FooBar[A, B] and T = FooBar[Int, String],
    // then we would match this branch with args = List(Int, String)
    // We also return the mapping A -> Int, B -> String
    // (in a form of list List((A, Int), (B, String)) as we need the ordering for latter on).
    case AppliedType(tr: TypeRef, args) =>
      val clsSym = tr.classSymbol.get
      val tyParams = clsSym.primaryConstructor.paramSymss.head.map(_.asInstanceOf[Symbol])
      (clsSym, tyParams.zip(args))
    // (case) objects have a special treatment
    case tr: TermRef if tr.classSymbol.isDefined =>
      return caseObjectSerializerMacroWorkhorse(inoxSerializer, id)
    case x =>
      assert(false, s"Unable to handle type $x")
  }
  // We copy tySubstArg into a Map for cases where we are not interested in the ordering of the subst.
  val tySubstArgMap = tySubstArg.toMap

  // Get all fields that have a corresponding parameter in the primary constructor.
  // For that, we use paramSymss, which is best explained with an example.
  // E.g. paramSymss of class Foo[A](f1: Int, f2: Expr)(f3: A) is:
  //    List(List(type A), List(val f1, val f2), List(val f3))
  // We don't want the "type A", so we drop the first element of the list if our T is an applied type.
  // We the previous example, we would get List(List(val f1, val f2), List(val f3)) for ctorFields
  val ctorFields = clsSym.primaryConstructor.paramSymss
    .drop(if (tySubstArgMap.isEmpty) 0 else 1)
    .map(_.map { ctorParamSym =>
      // Now get the corresponding *field* symbol of the constructor *parameter*.
      clsSym.fieldMembers.find(_.name == ctorParamSym.name).get
    })

  // We are also intersted in the type of these parameters. We need the types for generating the `read` method.
  // To do so, we get the DefDef tree of the constructor and pick `termParams`.
  // With the previous example, `termParams` would give us:
  //    List(List(ValDef(f1, Int), ValDef(f2, inox.ast.Expression.Expr)), List(ValDef(f3, A)))
  // Here `A` is a type parameter, and need to be substituted by what it was applied to.
  // For instance, if we have T = Foo[Boolean], then we would like to get the following list:
  //    List(List(Int, inox.ast.Expression.Expr), List(Boolean))
  // However, the type inox.ast.Expression.Expr is incorrect; we actually need to have `InoxSerializer.this.trees.Expr`.
  // For that, we need to also substitute all prefixes `inox.ast.Expression` (as well as `inox.ast.Types` and `inox.ast.Types`)
  // by `InoxSerializer.this.trees`.
  // (Because Stainless also needs `classSerializerMacroWorkhorse` and introduces other such prefixes, this method
  // expects an argument `prefixesToSubst` instead of hardcoding `inox.ast.Expression` & cie).

  // Represents `InoxSerializer.this.trees`.
  val treesSel = TermRef(inoxSerializer.asTerm.tpe, "trees")

  // Map to substitute types as described above.
  val treeMap = new TreeMap {
    override def transformTypeTree(tree: TypeTree)(owner: Symbol): TypeTree = {
      tySubstArgMap.get(tree.tpe.typeSymbol) match {
        case Some(t) => Inferred(t)
        // Note that we match on a TypeRepr, and not a TypeTree, as the TypeTree is just an Inferred wrapping the TypeRepr
        // Unfortunately, there are no TypeReprMap, so we must do the traversing ourselves...
        case None => tree.tpe match {
          case TypeRef(qualifier, designator) if prefixesToSubst.exists(_ =:= qualifier) =>
            TypeSelect.copy(tree)(Ref.term(treesSel), designator)
          case AppliedType(tycon, args) =>
            val tyconRec = transformTypeTree(Inferred(tycon))(owner)
            val argsRec = transformTypeTrees(args.map(Inferred.apply))(owner)
            Applied(tyconRec, argsRec)
          // TODO: There are other TypeRef, but we do not need to currently handle them
          case _ =>
            super.transformTypeTree(tree)(owner)
        }
      }
    }
  }

  // Types of all fields, according to the above description.
  val ctorFieldsType: List[List[TypeTree]] = clsSym.primaryConstructor.tree.asInstanceOf[DefDef].termParamss
    .map(_.params.map(valDef =>
      treeMap.transformTypeTree(valDef.tpt)(valDef.symbol)))

  val generated = '{
    // For some reason, the compiler is not happy if we try to do new $inoxSerializer.Serializer[T], so we create an alias...
    val ix = $inoxSerializer
    val serializer = new ix.Serializer[T]($id) {
      // Note: the occurences of T will be substitued by the actual type we are fed with.
      override def write(instance: T, out: OutputStream): Unit = {
        ${
          // List of statements that write all (constructor) fields, one by one
          val stmts = ctorFields.flatten.map { field =>
            val fieldSelect = Select('{instance}.asTerm, field).asExpr
            '{$inoxSerializer.writeObject($fieldSelect, out)}
          }
          Expr.block(stmts, '{()})
        }
      }

      override def read(in: InputStream): T = {
        ${
          val valDefs: List[List[ValDef]] = ctorFields.zip(ctorFieldsType).map {
            case (fields, fieldTyReprs) => fields.zip(fieldTyReprs).map {
              case (field, fieldTyRepr) => fieldTyRepr.tpe.asType match {
                case '[fieldTy] =>
                  val valDefSym = Symbol.newVal(Symbol.noSymbol, field.name, fieldTyRepr.tpe, Flags.EmptyFlags, Symbol.noSymbol)
                  ValDef(valDefSym, Some('{$inoxSerializer.readObject(in).asInstanceOf[fieldTy]}.asTerm))
              }
            }
          }

          val selectCtor = Select(New(TypeTree.of[T]), clsSym.primaryConstructor)
          // If the class is parameterized, we first apply it to the args in tySubstArg.
          val tyAppliedCtor =
            if (tySubstArg.nonEmpty) selectCtor.appliedToTypes(tySubstArg.map(_._2))
            else selectCtor
          val valDefsRefs = valDefs.map(_.map(valDef => Ref(valDef.symbol)))
          val termAppliedCtor =
            tyAppliedCtor.appliedToArgss(valDefsRefs)

          Block(valDefs.flatten, termAppliedCtor).asExprOf[T]
        }
      }
    }
    serializer
  }
  // To print the generated code, uncomment the println
  // println(generated.show)
  generated
}

def caseObjectSerializerMacroWorkhorse[T](inoxSerializer: Expr[InoxSerializer], id: Expr[Int])
                                         (using q: Quotes, t: Type[T]): Expr[InoxSerializer#Serializer[T]] = {
  import quotes.reflect._

  val generated = '{
    // For some reason, the compiler is not happy if we try to do new $inoxSerializer.Serializer[T], so we create an alias...
    val ix = $inoxSerializer
    val serializer = new ix.Serializer[T]($id) {
      // Note: the occurences of T will be substitued by the actual type we are fed with.
      override def write(instance: T, out: OutputStream): Unit = ()

      override def read(in: InputStream): T = ${Ident(TypeTree.of[T].tpe.asInstanceOf[TermRef]).asExprOf[T]}
    }
    serializer
  }
  // To print the generated code, uncomment the println
  // println(generated.show)
  generated
}
