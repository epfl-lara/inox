package inox
package parser

import org.scalatest._

class QuantifierParserSuite extends FunSuite {

  import inox.trees._
  import interpolator._
  implicit val symbols = NoSymbols

  test("Parsing forall.") {

    e"forall (x) => x > 2" match {
      case Forall(Seq(ValDef(id, IntegerType(), _)), expr) =>
        assertResult(GreaterThan(Variable(id, IntegerType(), Seq()), IntegerLiteral(2))) {
          expr
        }
      case e => fail("Unexpected shape: " + e)
    }

    e"forall (x: Integer) => false ==> true" match {
      case Forall(Seq(ValDef(id, IntegerType(), _)), expr) =>
        assertResult(Implies(BooleanLiteral(false), BooleanLiteral(true))) {
          expr
        }
      case e => fail("Unexpected shape: " + e)
    }

    e"true && forall (x: Integer) => false ==> true" match {
      case And(Seq(BooleanLiteral(true), Forall(Seq(ValDef(id, IntegerType(), _)), expr))) =>
        assertResult(Implies(BooleanLiteral(false), BooleanLiteral(true))) {
          expr
        }
      case e => fail("Unexpected shape: " + e)
    }

    e"forall (f, x: Int, y, z) => f(f(x, y), z) == f(x, f(y, z))" match {
      case Forall(Seq(ValDef(idF, FunctionType(Seq(Int32Type(), Int32Type()), Int32Type()), _),
                      ValDef(idX, Int32Type(), _),
                      ValDef(idY, Int32Type(), _),
                      ValDef(idZ, Int32Type(), _)), expr) => {
        val f = Variable(idF, FunctionType(Seq(Int32Type(), Int32Type()), Int32Type()), Seq())
        val x = Variable(idX, Int32Type(), Seq())
        val y = Variable(idY, Int32Type(), Seq())
        val z = Variable(idZ, Int32Type(), Seq())

        assertResult(Equals(Application(f, Seq(Application(f, Seq(x, y)), z)),
                            Application(f, Seq(x, Application(f, Seq(y, z)))))) {
          expr
        }
      }
    }
  }

  test("Parsing choose.") {

    e"choose (x) => x > 2" match {
      case Choose(ValDef(id, IntegerType(), _), expr) =>
        assertResult(GreaterThan(Variable(id, IntegerType(), Seq()), IntegerLiteral(2))) {
          expr
        }
      case e => fail("Unexpected shape: " + e)
    }

    e"choose (x: Integer) => false ==> true" match {
      case Choose(ValDef(id, IntegerType(), _), expr) =>
        assertResult(Implies(BooleanLiteral(false), BooleanLiteral(true))) {
          expr
        }
      case e => fail("Unexpected shape: " + e)
    }

    e"4 + choose (x: Integer) => false ==> true" match {
      case Plus(IntegerLiteral(_), Choose(ValDef(id, IntegerType(), _), expr)) =>
        assertResult(Implies(BooleanLiteral(false), BooleanLiteral(true))) {
          expr
        }
      case e => fail("Unexpected shape: " + e)
    }
  }

  test("Parsing lambda.") {

    e"lambda (x) => x > 2" match {
      case Lambda(Seq(ValDef(id, IntegerType(), _)), expr) =>
        assertResult(GreaterThan(Variable(id, IntegerType(), Seq()), IntegerLiteral(2))) {
          expr
        }
      case e => fail("Unexpected shape: " + e)
    }

    e"lambda (x: Integer) => false ==> true" match {
      case Lambda(Seq(ValDef(id, IntegerType(), _)), expr) =>
        assertResult(Implies(BooleanLiteral(false), BooleanLiteral(true))) {
          expr
        }
      case e => fail("Unexpected shape: " + e)
    }

    e"((x: Integer) => false ==> true)(17)" match {
      case Application(Lambda(Seq(ValDef(id, IntegerType(), _)), expr), Seq(IntegerLiteral(_))) =>
        assertResult(Implies(BooleanLiteral(false), BooleanLiteral(true))) {
          expr
        }
      case e => fail("Unexpected shape: " + e)
    }

    e"(lambda (x, y, z: Integer) => x * y + z)(1, 2, 3)" match {
      case Application(Lambda(Seq(ValDef(idX, IntegerType(), _), ValDef(idY, IntegerType(), _), ValDef(idZ, IntegerType(), _)), expr),
          Seq(vX, vY, vZ)) => {
        val x = Variable(idX, IntegerType(), Seq())
        val y = Variable(idY, IntegerType(), Seq())
        val z = Variable(idZ, IntegerType(), Seq())

        assertResult(Plus(Times(x, y), z)) {
          expr
        }

        assertResult(IntegerLiteral(1)) { vX }
        assertResult(IntegerLiteral(2)) { vY }
        assertResult(IntegerLiteral(3)) { vZ }
      }
      case e => fail("Unexpected shape: " + e)
    }
  }
}
