/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package rust

import org.scalatest._

import java.io.{FileInputStream, InputStream}

import scala.reflect.ClassTag

class RustInteropSuite extends FunSpec with ResourceUtils {
  import inox.trees._

  val ctx = TestContext.empty

  val files = resourceFiles("regression/rust", filter = _ endsWith ".inoxser", recursive = false)

  describe("Deserializing from rust") {
    for (file <- files) {
      val name = file.getName
      val fis = new FileInputStream(file)
      val serializer = utils.Serializer(inox.trees)
      import serializer._

      def test[T: ClassTag](expected: T)(implicit p: SerializableOrProcedure[T]): Unit = {
        val data = serializer.deserialize[T](fis)
        assert(data == expected)
      }

      it(s"deserializes $name") {
        name match {
          case "seq_of_ints.inoxser" =>
            test(Seq[Int](1, 2, 3))
          case "many_seqs.inoxser" =>
            test((Seq[Int](1, 2, 3), Seq[Boolean](true, false), Seq[String]("Hello", "world")))
          case "set_of_int_tuples.inoxser" =>
            test(Set[(Int, Int)]((1, 2), (1, 3), (2, 3), (-4, 5)))
          case "map_of_strings_and_ints.inoxser" =>
            test(Map[String, Int](("alpha", 123), ("bravo", 456), ("charlie", 789)))
          case "option_of_bigint.inoxser" =>
            test(Some(BigInt(123)))
          case "int32_literal.inoxser" =>
            test(Int32Literal(123))
          case "arithmetic_expr.inoxser" =>
            test(Times(Plus(Int32Literal(1), Int32Literal(1)), Int32Literal(1)))
          case "identity_fundef.inoxser" =>
            val idX = new Identifier("x", 1, 1)
            val idF = new Identifier("f", 2, 1)
            val varX = Variable(idX, Int32Type(), Seq.empty)
            test(new FunDef(idF, Seq.empty, Seq(varX.toVal), Int32Type(), varX, Seq.empty))
          case _ => fail(s"Unknown test case: $name")
        }
      }
    }
  }

  // TODO: Migrate this to a seperate script or sbt task
  describe("Generate code for rust-interop") {
    it("generates") {
      import scala.reflect.runtime.universe._
      import scala.collection.mutable.{ArrayBuffer, HashMap => MutableMap, HashSet => MutableSet}

      val TreeT = typeOf[inox.trees.Tree]
      val DefinitionT = typeOf[inox.trees.Definition]
      val FlagT = typeOf[inox.trees.Flag]
      val ExprT = typeOf[inox.trees.Expr]
      val TypeT = typeOf[inox.trees.Type]

      val VariableT = typeOf[inox.trees.Variable]
      val BigIntT = typeOf[scala.math.BigInt]

      case class Field(name: String, tpe: Type)
      case class Class(
        classSymbol: ClassSymbol,
        fields: List[Field],
        customIdentity: Option[String],
        markerId: Int,
        needsSerializable: Boolean)

      var definitionClasses = ArrayBuffer[Class]()
      var flagClasses = ArrayBuffer[Class]()
      var exprClasses = ArrayBuffer[Class]()
      var typeClasses = ArrayBuffer[Class]()
      var otherClasses = ArrayBuffer[Class]()

      val serializer = new utils.InoxSerializer(inox.trees) {
        def generateRustInterop() = {
          classSerializers.foreach { case (runtimeClass, serializer) =>
            val rootMirror = scala.reflect.runtime.universe.runtimeMirror(runtimeClass.getClassLoader)
            val classSymbol = rootMirror.classSymbol(runtimeClass)

            val rawFields = fieldsForClassSymbol(classSymbol)
            var fields: List[Field] = rawFields.map { field =>
              val tpe = field.info match {
                case NullaryMethodType(tpe) => tpe
                case tpe => tpe
              }
              Field(field.name.toString, tpe)
            } .toList

            val baseClasses = classSymbol.toType.baseClasses
            val isDefinition = baseClasses.contains(DefinitionT.typeSymbol)
            val isFlag = baseClasses.contains(FlagT.typeSymbol)
            val isExpr = baseClasses.contains(ExprT.typeSymbol)
            val isType = baseClasses.contains(TypeT.typeSymbol)

            val name = classSymbol.name.toString

            var customIdentity: Option[String] = None
            var needsSerializable = true

            name match {
              case "ADTSort" | "FunDef" =>
                customIdentity = Some("id")
              case "TypeParameterDef" =>
                customIdentity = Some("tp.id")
                needsSerializable = false
              case "ValDef" =>
                fields = fields :+ Field("v", VariableT)
                customIdentity = Some("v.id")
                needsSerializable = false
              case "TypeParameter" =>
                customIdentity = Some("id")
              case "ADTConstructor" =>
                customIdentity = Some("id")
              case "Annotation" =>
                fields = fields.map {
                  case f if f.name == "args" => f.copy(tpe = typeOf[Seq[inox.trees.Expr]])
                  case f => f
                }
              case "BVLiteral" =>
                fields = fields.map {
                  case f if f.name == "value" => f.copy(tpe = BigIntT)
                  case f => f
                }
                needsSerializable = false
              case "Identifier" =>
                customIdentity = Some("id")
                needsSerializable = false
              case _ =>
            }

            if (name != "SerializationResult") {
              val clazz = Class(classSymbol, fields, customIdentity, serializer.id, needsSerializable)
              if (isDefinition) definitionClasses += clazz
              else if (isFlag) flagClasses += clazz
              else if (isExpr) exprClasses += clazz
              else if (isType) typeClasses += clazz
              else otherClasses += clazz
            }
          }

          definitionClasses = definitionClasses.sortBy(_.classSymbol.name.toString)
          flagClasses = flagClasses.sortBy(_.classSymbol.name.toString)
          exprClasses = exprClasses.sortBy(_.classSymbol.name.toString)
          typeClasses = typeClasses.sortBy(_.classSymbol.name.toString)
          otherClasses = otherClasses.sortBy(_.classSymbol.name.toString)

          val allClasses = definitionClasses ++ flagClasses ++ exprClasses ++ typeClasses ++ otherClasses

          def isAllocType(tpe: Type): Boolean =
            tpe.baseClasses.contains(TreeT.typeSymbol) || tpe.typeSymbol.name.toString == "Identifier"
          def allocTypesInType(tpe: Type): Set[Type] =
            if (isAllocType(tpe)) Set(tpe)
            else tpe.typeArgs.flatMap(allocTypesInType).toSet

          val classIsDirectPartOf = {
            val result =
              MutableMap[ClassSymbol, MutableSet[ClassSymbol]]().withDefaultValue(MutableSet.empty)
            for { clazz <- allClasses
                  field <- clazz.fields
                  fieldTpe <- allocTypesInType(field.tpe)
                  fieldSym = fieldTpe.typeSymbol if fieldSym.isClass
                }
              result(fieldSym.asClass) += clazz.classSymbol

            def addParent(parentTpe: Type, classes: ArrayBuffer[Class]) = {
              val parentSym = parentTpe.typeSymbol.asClass
              classes.foreach(c => result(c.classSymbol) += parentSym)
            }
            addParent(DefinitionT, definitionClasses)
            addParent(FlagT, flagClasses)
            addParent(ExprT, exprClasses)
            addParent(TypeT, typeClasses)

            result
          }

          val classNeedsLifetime: Set[ClassSymbol] = {
            val initialLifetimeUsers =
              allClasses
                .filter(_.fields.exists(f => allocTypesInType(f.tpe).nonEmpty))
                .map(_.classSymbol)
                .toSet
            inox.utils.fixpoint[Set[ClassSymbol]]({
              classes => classes.flatMap(classIsDirectPartOf).toSet
            })(initialLifetimeUsers)
          }

          def typeNeedsLifetime(tpe: Type): Boolean = {
            val sym = tpe.typeSymbol
            sym.isClass && classNeedsLifetime(sym.asClass)
          }

          def renderLifetimeFor(tpe: Type): String =
            if (typeNeedsLifetime(tpe)) "<'a>" else ""

          def renderSimpleType(tpe: Type, asRef: Boolean): String = {
            assert(tpe.typeArgs.isEmpty, s"$tpe")
            val prefix = if (asRef && isAllocType(tpe)) "&'a " else ""
            val suffix = renderLifetimeFor(tpe)
            val name = tpe.typeSymbol.name.toString
            s"$prefix$name$suffix"
          }

          def printAbstractClass(absClassType: Type, classes: ArrayBuffer[Class]) = {
            val absClassSymbol = absClassType.typeSymbol
            val nameStr = renderSimpleType(absClassType, asRef=false)
            val variantStrs = classes.map { c =>
              s"${c.classSymbol.name}(${renderSimpleType(c.classSymbol.toType, asRef=false)})"
            }
            println(s"/// ${absClassSymbol.fullName}")
            println("#[derive(Clone, Debug, PartialEq, Eq, Hash)]")
            println(s"pub enum $nameStr {${variantStrs.mkString("\n  ", ",\n  ", "\n")}}\n")

            val simpleName = absClassSymbol.name.toString
            println(s"impl${renderLifetimeFor(absClassType)} Serializable for $nameStr {")
            println("  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {")
            println("    match self {")
            for (clazz <- classes) {
              val simpleVariantName = clazz.classSymbol.name.toString
              println(s"      $simpleName::$simpleVariantName(v) => v.serialize(s)?,")
            }
            println("    };")
            println("    Ok(())")
            println("  }")
            println("}\n")
          }

          def printClasses(classes: ArrayBuffer[Class]) = {
            classes.foreach { c =>
              def renderType(tpe: Type, asRef: Boolean): String = tpe match {
                case TypeRef(_, constr, args) if args.nonEmpty =>
                  val argsStr = args.map(renderType(_, asRef)).mkString(", ")
                  if (constr.name.toString.startsWith("Tuple")) {
                    s"($argsStr)"
                  } else {
                    s"${constr.name}<${args.map(renderType(_, asRef)).mkString(", ")}>"
                  }
                case _ =>
                  renderSimpleType(tpe, asRef)
              }

              val className = c.classSymbol.fullName
              val classType = c.classSymbol.toType
              val nameStr = renderSimpleType(classType, asRef=false)
              val fieldStrs = c.fields.map{ f => s"pub ${f.name}: ${renderType(f.tpe, asRef=true)}" }
              val derives =
                Seq("Clone", "Debug") ++
                (if (c.customIdentity.isDefined) Seq() else Seq("PartialEq", "Eq", "Hash"))

              println(s"/// $className")
              println(s"#[derive(${derives.mkString(", ")})]")
              println(s"pub struct $nameStr {${fieldStrs.mkString("\n  ", ",\n  ", "\n")}}\n")

              if (c.customIdentity.isDefined) {
                val path = c.customIdentity.get
                println(s"impl${renderLifetimeFor(classType)} PartialEq for $nameStr {")
                println(s"  fn eq(&self, other: &Self) -> bool { self.$path == other.$path }")
                println("}")
                println(s"impl${renderLifetimeFor(classType)} Eq for $nameStr {}")
                println(s"impl${renderLifetimeFor(classType)} PartialOrd for $nameStr {")
                println(s"  fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }")
                println("}")
                println(s"impl${renderLifetimeFor(classType)} Ord for $nameStr {")
                println(s"  fn cmp(&self, other: &Self) -> Ordering { self.$path.cmp(&other.$path) }")
                println("}")
                println(s"impl${renderLifetimeFor(classType)} Hash for $nameStr {")
                println(s"  fn hash<H: Hasher>(&self, state: &mut H) { self.$path.hash(state); }")
                println("}")
                println("")
              }

              if (c.needsSerializable) {
                println(s"impl${renderLifetimeFor(classType)} Serializable for $nameStr {")
                println("  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {")
                println(s"    s.write_marker(MarkerId(${c.markerId}))?;")
                for (field <- c.fields)
                  println(s"    self.${field.name}.serialize(s)?;")
                println(s"    Ok(())")
                println("  }")
                println("}")
              }
            }
          }

          def printCaption(caption: String) =
            println(s"\n// === $caption ===\n")

          println("// AUTO-GENERATED FROM STAINLESS")
          println("#![allow(non_snake_case)]")
          println("use crate::ser::{MarkerId, Serializable, SerializationResult, Serializer};")
          println("use crate::ser::types::*;")
          println("use std::cmp::Ordering;")
          println("use std::hash::{Hash, Hasher};")

          printCaption("Definition")
          printAbstractClass(DefinitionT, definitionClasses)
          printClasses(definitionClasses)

          printCaption("Flags")
          printAbstractClass(FlagT, flagClasses)
          printClasses(flagClasses)

          printCaption("Expressions")
          printAbstractClass(ExprT, exprClasses)
          printClasses(exprClasses)

          printCaption("Types")
          printAbstractClass(TypeT, typeClasses)
          printClasses(typeClasses)

          printCaption("Other")
          printClasses(otherClasses)
        }
      }
      // serializer.generateRustInterop()
    }
  }
}
