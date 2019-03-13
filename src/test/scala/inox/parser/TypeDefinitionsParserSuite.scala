package inox
package parser

import org.scalatest._

class TypeDefinitionsParserSuite extends FunSuite {

  import inox.trees._
  import interpolator._
  implicit val symbols = NoSymbols

  test("Parsing Nat.") {
    val natSort: ADTSort = td"type Nat = Succ(n: Nat) | Zero()"

    assert(natSort.id.name == "Nat")

    assert(natSort.tparams.isEmpty)

    assert(natSort.constructors.size == 2)

    val succCons: ADTConstructor = natSort.constructors(0)
    val zeroCons: ADTConstructor = natSort.constructors(1)

    assert(succCons.id.name == "Succ")
    assert(zeroCons.id.name == "Zero")

    assert(succCons.sort == natSort.id)
    assert(zeroCons.sort == natSort.id)

    assert(succCons.fields.size == 1)
    assert(zeroCons.fields.isEmpty)

    val nField: ValDef = succCons.fields(0)

    assert(nField.id.name == "n")
    assert(nField.tpe == ADTType(natSort.id, Seq()))
  }

  test("Parsing List.") {
    val listSort: ADTSort = td"type List[A] = Cons(head: A, tail: List[A]) | Nil()"

    assert(listSort.id.name == "List")

    assert(listSort.tparams.size == 1)

    val aTypeParamDef = listSort.tparams(0)

    assert(aTypeParamDef.id.name == "A")

    assert(listSort.constructors.size == 2)

    val consCons = listSort.constructors(0)
    val nilCons = listSort.constructors(1)

    assert(consCons.id.name == "Cons")
    assert(nilCons.id.name == "Nil")

    assert(consCons.sort == listSort.id)
    assert(nilCons.sort == listSort.id)

    assert(consCons.fields.size == 2)
    assert(nilCons.fields.isEmpty)

    val headField = consCons.fields(0)
    val tailField = consCons.fields(1)

    assert(headField.id.name == "head")
    assert(tailField.id.name == "tail")

    assert(headField.tpe == aTypeParamDef.tp)
    assert(tailField.tpe == ADTType(listSort.id, Seq(aTypeParamDef.tp)))
  }

  test("Parsing Either.") {
    val eitherSort: ADTSort = td"type Either[A, B] = Left(getLeft: A) | Right(getRight: B)"

    assert(eitherSort.id.name == "Either")

    assert(eitherSort.tparams.size == 2)

    val aTypeParamDef = eitherSort.tparams(0)
    val bTypeParamDef = eitherSort.tparams(1)

    assert(aTypeParamDef.id.name == "A")
    assert(bTypeParamDef.id.name == "B")

    assert(eitherSort.constructors.size == 2)

    val leftCons = eitherSort.constructors(0)
    val rightCons = eitherSort.constructors(1)

    assert(leftCons.id.name == "Left")
    assert(rightCons.id.name == "Right")

    assert(leftCons.sort == eitherSort.id)
    assert(rightCons.sort == eitherSort.id)

    assert(leftCons.fields.size == 1)
    assert(rightCons.fields.size == 1)

    val getLeftField = leftCons.fields(0)
    val getRightField = rightCons.fields(0)

    assert(getLeftField.id.name == "getLeft")
    assert(getRightField.id.name == "getRight")

    assert(getLeftField.tpe == aTypeParamDef.tp)
    assert(getRightField.tpe == bTypeParamDef.tp)
  }

  test("Elaborating with holes.") {
    val idSort = FreshIdentifier("IDSort")
    val idCons = FreshIdentifier("IDCons")
    val idField = FreshIdentifier("idField")
    val typeField = t"Integer"

    val sort = td"type $idSort = $idCons($idField: $typeField)"

    assert(sort.id == idSort)
    assert(sort.constructors.size == 1)
    assert(sort.constructors(0).id == idCons)
    assert(sort.constructors(0).fields.size == 1)
    assert(sort.constructors(0).fields(0).id == idField)
    assert(sort.constructors(0).fields(0).tpe == typeField)
  }

  test("Matching against type definitions.") {
    val lensSort = td"type Lens[S, A] = Lens(view: S => A, update: (S, A) => S)"

    lensSort match {
      case td"type $x = $cs..." => fail("Did match")
      case td"type $x[$s] = $cs..." => fail("Did match")
      case td"type $x[$s, $a] = $c1 | $c2" => fail("Did match.")
      case td"type $x[$ts...] = $cs..." => {
        assert(x.name == "Lens")
        assert(ts.size == 2)
        assert(ts(0).name == "S")
        assert(ts(1).name == "A")
        assert(cs.size == 1)
        assert(cs(0).id.name == "Lens")
      }
      case _ => fail("No match.")
    }

    lensSort match {
      case td"type $x[$s, $a] = $c" => {
        assert(x.name == "Lens")
        assert(c.id.name == "Lens")
      }
      case _ => fail("No match.")
    }

    val weirdSort = td"type Weird[A, B, C] = AB(a: A, b: B) | B() | BC(b2: B, c: C)"

    weirdSort match {
      case td"type $x[$ts...] = $cs..." => {
        assert(x.name == "Weird")
        assert(cs.size == 3)
      }
      case _ => fail("No match.")
    }

    weirdSort match {
      case td"type $x[$ts...] = $cs..." => {
        assert(x.name == "Weird")
        assert(cs.size == 3)
        assert(ts.size == 3)
      }
      case _ => fail("No match.")
    }

    weirdSort match {
      case td"type T[$ts...] = $cs..." => {
        assert(cs.size == 3)
        assert(ts.size == 3)
      }
      case _ => fail("No match.")
    }

    weirdSort match {
      case td"type $x[$ts...] = $c1" => {
        println(c1)
        fail("Should not match.")
      }
      case td"type $x[$ts...] = $c1 | $c2" => fail("Should not match.")
      case td"type $x[$ts...] = $c1 | $c2 | $c3 | $c4" => fail("Should not match.")
      case td"type $x[$ts...] = $c1 | $c2 | $c3" => {
        assert(x.name == "Weird")
        assert(c1.id.name == "AB")
        assert(c2.id.name == "B")
        assert(c3.id.name == "BC")
      }
      case _ => fail("No match.")
    }

    val optionSort = td"type Option[A] = Some(get: A) | None()"

    optionSort match {
      case td"type Option[A] = None() | Some(get: A)" => fail("Did match.")
      case td"type Opt[X] = Indeed(value: X) | Not()" => ()
      case _ => fail("No match.")
    }

    optionSort match {
      case td"type Opt[X] = Indeed(value: $t) | Not()" =>
        assert(t.asInstanceOf[TypeParameter].id.name == "A")
      case _ => fail("No match.")
    }
  }
}