/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package binary

import org.scalatest.funspec.AnyFunSpec

import java.io.FileInputStream

import scala.reflect.ClassTag

class DeserializationSuite extends AnyFunSpec with ResourceUtils {
  import inox.trees._

  val ctx = TestContext.empty

  val files = resourceFiles("regression/binary", filter = _ endsWith ".inoxser", recursive = false)

  describe("Deserializing from binary files") {
    for (file <- files) {
      val name = file.getName
      val fis = new FileInputStream(file)
      val serializer = utils.Serializer(inox.trees)
      import serializer._

      def test[T: ClassTag](expected: T)(implicit p: SerializableOrProcedure[T]): Unit = {
        val data = serializer.deserialize[T](fis)
        assert(data == expected)
      }

      def makeIdentity(): FunDef = {
        val idX = new Identifier("x", 1, 1)
        val idF = new Identifier("f", 2, 1)
        val varX = Variable(idX, Int32Type(), Seq.empty)
        new FunDef(idF, Seq.empty, Seq(varX.toVal), Int32Type(), varX, Seq.empty)
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
            test(makeIdentity())
          case "identity_symbols.inoxser" =>
            test(NoSymbols.withFunctions(Seq(makeIdentity())))
          case _ => fail(s"Unknown test case: $name")
        }
      }
    }
  }
}
