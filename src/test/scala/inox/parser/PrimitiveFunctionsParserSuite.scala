package inox
package parser

import org.scalatest._

class PrimitiveFunctionsParserSuite extends FunSuite {

  import inox.trees._
  import interpolator._
  implicit val symbols = NoSymbols

  test("Parsing casts.") {

    assertResult(BVWideningCast(Int32Literal(1), BVType(true, 64))) {
      e"widen64(1 as Int32)"
    }

    assertResult(BVNarrowingCast(Int32Literal(2), BVType(true, 16))) {
      e"narrow16(2 as Int32)"
    }

    assertThrows[InterpolatorException] {
      e"widen32(3 as Int64)"
    }

    assertThrows[InterpolatorException] {
      e"narrow32(4 as Int16)"
    }
  }
}