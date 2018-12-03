package inox
package parser

import org.scalatest._

class FunctionDefinitionsParserSuite extends FunSuite {

  import inox.trees._
  import interpolator._
  implicit val symbols = NoSymbols

  test("Parsing id.") {
    val idFunDef = fd"def id[A](x: A): A = x"

    assert(idFunDef.id.name == "id")
    assert(idFunDef.tparams.size == 1)
    assert(idFunDef.tparams(0).id.name == "A")
    assert(idFunDef.params.size == 1)
    assert(idFunDef.params(0).id.name == "x")
    assert(idFunDef.params(0).tpe.asInstanceOf[TypeParameter].id == idFunDef.tparams(0).id)
    assert(idFunDef.returnType.asInstanceOf[TypeParameter].id == idFunDef.tparams(0).id)
    assert(idFunDef.fullBody.asInstanceOf[Variable].id == idFunDef.params(0).id)
  }

  test("Parsing fac.") {
    val facFunDef = fd"def fac(n: Int) = if (n <= 0) 1 else n * fac(n - 1)"

    assert(facFunDef.id.name == "fac")
    assert(facFunDef.tparams.size == 0)
    assert(facFunDef.params.size == 1)
    assert(facFunDef.params(0).id.name == "n")
    assert(facFunDef.params(0).tpe == Int32Type())
    assert(facFunDef.returnType == Int32Type())

    facFunDef.fullBody match {
      case e"if (${ n1: Variable } <= 0) 1 else ${ n2: Variable } * $f(${ n3: Variable } - 1)" => {
        assert(n1.id == facFunDef.params(0).id)
        assert(n2.id == facFunDef.params(0).id)
        assert(n3.id == facFunDef.params(0).id)
        assert(f == facFunDef.id)
      }
      case _ => fail("Did not match.")
    }
  }

  test("Parsing rep.") {
    val repFunDef = fd"def rep[A](f: A => A, n: Int) = if (n == 0) lambda (x) => x else lambda (x) => f(rep(f, n - 1)(x))"

    assert(repFunDef.id.name == "rep")
    assert(repFunDef.tparams.size == 1)
    assert(repFunDef.tparams(0).id.name == "A")
    assert(repFunDef.params.size == 2)
    assert(repFunDef.params(0).id.name == "f")
    assert(repFunDef.params(0).tpe == FunctionType(Seq(repFunDef.tparams(0).tp), repFunDef.tparams(0).tp))
    assert(repFunDef.params(1).id.name == "n")
    assert(repFunDef.params(1).tpe == Int32Type())
    assert(repFunDef.returnType == FunctionType(Seq(repFunDef.tparams(0).tp), repFunDef.tparams(0).tp))
  }

  test("Parsing function with dependant parameters.") {
    val fooFunDef = fd"def foo(n: Int, m: { Int | n < m }) = n + m"

    assert(fooFunDef.params(0).id.name == "n")

    assert(fooFunDef.params(1).id.name == "m")

    assert(fooFunDef.params(1).tpe.isInstanceOf[RefinementType])

    val reTpe = fooFunDef.params(1).tpe.asInstanceOf[RefinementType]

    assert(reTpe.vd.id.name == fooFunDef.params(1).id.name)
    assert(reTpe.vd.id != fooFunDef.params(1).id)
    assert(reTpe.prop == LessThan(fooFunDef.params(0).toVariable, reTpe.vd.toVariable))
  }

  test("Parsing function with dependant parameters and type parameters.") {
    val barFunDef = fd"def bar[A, B](x: A, y: A, f: { A => B | f(x) == f(y) }): { r: Boolean | r ==> x != y } = x != y"

    assert(barFunDef.tparams.size == 2)

    assert(barFunDef.params.size == 3)

    assert(barFunDef.fullBody == Not(Equals(barFunDef.params(0).toVariable, barFunDef.params(1).toVariable)))

    assert(barFunDef.params(2).tpe.isInstanceOf[RefinementType])

    val reTpe = barFunDef.params(2).tpe.asInstanceOf[RefinementType]

    assert(reTpe.vd.tpe == FunctionType(Seq(barFunDef.tparams(0).tp), barFunDef.tparams(1).tp))

    assert(reTpe.vd.id.name == barFunDef.params(2).id.name)
    assert(reTpe.vd.id != barFunDef.params(2).id)
    assert(reTpe.prop == Equals(
      Application(reTpe.vd.toVariable, Seq(barFunDef.params(0).toVariable)),
      Application(reTpe.vd.toVariable, Seq(barFunDef.params(1).toVariable))))


    assert(barFunDef.returnType.isInstanceOf[RefinementType])
    val retReTpe = barFunDef.returnType.asInstanceOf[RefinementType]

    assert(retReTpe.vd.id.name == "r")
    assert(retReTpe.vd.tpe == BooleanType())
    assert(retReTpe.prop == Implies(retReTpe.vd.toVariable,
      Not(Equals(barFunDef.params(0).toVariable, barFunDef.params(1).toVariable))))
  }

  test("Matching against function definitions.") {
    val fooFunDef = fd"def foo[A, B, C](x: A, y: B, f: (A, B) => C): C = f(x, y)"

    fooFunDef match {
      case fd"def foo($xs...) = $e" => fail("Did match.")
      case fd"def foo[$ts...]($xs...): $t = $e" => {
        assert(ts.size == 3)
        assert(xs.size == 3)
      }
      case _ => fail("Did not match.")
    }

    val barFunDef = fd"def bar(x: Integer) = x + x + x"

    barFunDef match {
      case fd"def foo[$ts...](x: Integer) = x + x + x" => assert(ts.isEmpty)
      case _ => fail("Did not match.")
    }

    barFunDef match {
      case fd"def foo(x: Integer) = x + x * x" => fail("Did match.")
      case fd"def foo($x): Integer = x + ${y : Variable} + x" => {
        assert(x.id == y.id)
      }
      case _ => fail("Did not match.")
    }
  }
}