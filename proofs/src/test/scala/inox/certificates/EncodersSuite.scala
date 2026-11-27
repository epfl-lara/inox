/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package certificates

import org.scalatest.funsuite.AnyFunSuite

/** The check of the input of a certificate, on inputs written as Inox prints them. */
class EncodersSuite extends AnyFunSuite {
  import Checker._

  val sourceSymbols = parse("""
    (Bag!1 sort "Bag$7[T$3]")
    (Node!1 constructor "Node$0" "Bag$7[T$3]")
    (Elem!1 constructor "Elem$0" "Bag$7[T$3]")
    (Leaf!1 constructor "Leaf$0" "Bag$7[T$3]")
    (get!1 function "get$0")
    (size!2 function "size$4")
    (List!2 sort "List$1[A$0]")
    (b!0 variable "b$0" "Bag$7[BigInt]" (Bag!1 Int))
    (k!0 variable "k$0" "BigInt" Int)
  """)

  def input(constraint: String, encoded: String, encoders: String = "\"propositions\" \"bags\" \"map-merge\""): List[SExpr] = parse(s"""
    (encoders $encoders)
    (definitions)
    (constraint $constraint (encoded $encoded) (simplified))
    (symbols
    (size!1 function "size$$4")
    (List!1 sort "List$$1[A$$0]")
    (b!0 variable "b$$0" "Bag[BigInt]" (Bag Int))
    (k!0 variable "k$$0" "BigInt" Int))
  """)

  def refused(in: List[SExpr]): String = intercept[Failure](Encoders.check(in, sourceSymbols)).getMessage

  test("a certificate without an input has nothing to check") {
    assert(Encoders.check(Nil, sourceSymbols) == 0)
  }

  test("the operations of bags are those of the encoder's datatype") {
    assert(Encoders.check(input(
      "(not (= (bag.union b!0 (as bag.empty Int)) b!0))",
      "(not (= ((as Node!1 (Bag!1 Int)) 0 b!0 (as Leaf!1 (Bag!1 Int))) b!0))"), sourceSymbols) == 1)
    assert(Encoders.check(input(
      "(= (bag.multiplicity k!0 (bag.insert (as bag.empty Int) k!0)) 1)",
      "(= ((as get!1 (Int)) ((as Node!1 (Bag!1 Int)) 0 (as Leaf!1 (Bag!1 Int)) ((as Elem!1 (Bag!1 Int)) k!0 1)) k!0) 1)"), sourceSymbols) == 1)
    assert(Encoders.check(input(
      "(= (bag.difference b!0 b!0) (bag.intersection b!0 b!0))",
      "(= ((as Node!1 (Bag!1 Int)) 1 b!0 b!0) ((as Node!1 (Bag!1 Int)) 2 b!0 b!0))"), sourceSymbols) == 1)
    assert(Encoders.check(input(
      "(= (bag.singleton k!0 3) (bag.singleton k!0 k!0))",
      "(= (ite false (as Leaf!1 (Bag!1 Int)) ((as Node!1 (Bag!1 Int)) 0 (as Leaf!1 (Bag!1 Int)) ((as Elem!1 (Bag!1 Int)) k!0 3)))" +
        " (ite false (as Leaf!1 (Bag!1 Int)) ((as Node!1 (Bag!1 Int)) 0 (as Leaf!1 (Bag!1 Int))" +
        " (ite (> k!0 0) ((as Elem!1 (Bag!1 Int)) k!0 k!0) (as Leaf!1 (Bag!1 Int))))))"), sourceSymbols) == 1)
  }

  test("a term that the encoders don't make of the input is refused") {
    // another operation, other operands, and another element
    assert(refused(input("(= (bag.union b!0 b!0) b!0)", "(= ((as Node!1 (Bag!1 Int)) 1 b!0 b!0) b!0)")).contains("is not what the encoders make"))
    assert(refused(input("(= (bag.multiplicity k!0 b!0) 1)", "(= ((as get!1 (Int)) b!0 k!0) 2)")).contains("is not what the encoders make"))
    assert(refused(input("(= (bag.insert b!0 k!0) b!0)", "(= ((as Node!1 (Bag!1 Int)) 0 b!0 ((as Elem!1 (Bag!1 Int)) k!0 2)) b!0)")).contains("is not what"))
    // a symbol of the input faces the symbol of the sources of its identifier
    assert(refused(input("(= ((as size!1 (Int)) k!0) 1)", "(= ((as get!1 (Int)) k!0) 1)")).contains("is not what the encoders make"))
    assert(Encoders.check(input("(= ((as size!1 (Int)) k!0) 1)", "(= ((as size!2 (Int)) k!0) 1)"), sourceSymbols) == 1)
    // a bag without the encoder of bags
    assert(refused(input("(= (bag.union b!0 b!0) b!0)", "(= ((as Node!1 (Bag!1 Int)) 0 b!0 b!0) b!0)", "\"propositions\"")).contains("is not what"))
  }

  test("bound variables face each other, and an unknown encoder is refused") {
    assert(Encoders.check(input(
      "(forall ((x!1 (Bag Int))) (= (bag.multiplicity k!0 x!1) 0))",
      "(forall ((x!5 (Bag!1 Int))) (= ((as get!1 (Int)) x!5 k!0) 0))"), sourceSymbols) == 1)
    assert(refused(input("(forall ((x!1 Int)) (= x!1 k!0))", "(forall ((x!5 Int)) (= k!0 x!5))")).contains("is not what"))
    assert(refused(input("true", "true", "\"strings\"")).contains("doesn't check the encoder strings"))
  }
}
