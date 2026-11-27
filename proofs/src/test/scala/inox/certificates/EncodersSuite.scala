/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package certificates

import org.scalatest.funsuite.AnyFunSuite

/** The check of the input of a certificate, on inputs written as Inox prints them. */
class EncodersSuite extends AnyFunSuite {
  import Checker._

  def sexprs(text: String): List[SExpr] = parse(text)

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
    (constraint $constraint (encoded $encoded))
    (symbols
    (size!1 function "size$$4")
    (List!1 sort "List$$1[A$$0]")
    (b!0 variable "b$$0" "Bag[BigInt]" (Bag Int))
    (k!0 variable "k$$0" "BigInt" Int))
  """)

  def refused(in: List[SExpr]): String = intercept[Failure](Encoders.check(in, Nil, sourceSymbols)).getMessage

  test("a certificate without an input has nothing to check") {
    assert(Encoders.check(Nil, Nil, sourceSymbols) == 0)
  }

  test("the operations of bags are those of the encoder's datatype") {
    assert(Encoders.check(input(
      "(not (= (bag.union b!0 (as bag.empty Int)) b!0))",
      "(not (= ((as Node!1 (Bag!1 Int)) 0 b!0 (as Leaf!1 (Bag!1 Int))) b!0))"), Nil, sourceSymbols) == 1)
    assert(Encoders.check(input(
      "(= (bag.multiplicity k!0 (bag.insert (as bag.empty Int) k!0)) 1)",
      "(= ((as get!1 (Int)) ((as Node!1 (Bag!1 Int)) 0 (as Leaf!1 (Bag!1 Int)) ((as Elem!1 (Bag!1 Int)) k!0 1)) k!0) 1)"), Nil, sourceSymbols) == 1)
    assert(Encoders.check(input(
      "(= (bag.difference b!0 b!0) (bag.intersection b!0 b!0))",
      "(= ((as Node!1 (Bag!1 Int)) 1 b!0 b!0) ((as Node!1 (Bag!1 Int)) 2 b!0 b!0))"), Nil, sourceSymbols) == 1)
    assert(Encoders.check(input(
      "(= (bag.singleton k!0 3) (bag.singleton k!0 k!0))",
      "(= (ite false (as Leaf!1 (Bag!1 Int)) ((as Node!1 (Bag!1 Int)) 0 (as Leaf!1 (Bag!1 Int)) ((as Elem!1 (Bag!1 Int)) k!0 3)))" +
        " (ite false (as Leaf!1 (Bag!1 Int)) ((as Node!1 (Bag!1 Int)) 0 (as Leaf!1 (Bag!1 Int))" +
        " (ite (> k!0 0) ((as Elem!1 (Bag!1 Int)) k!0 k!0) (as Leaf!1 (Bag!1 Int))))))"), Nil, sourceSymbols) == 1)
  }

  test("a term that the encoders don't make of the input is refused") {
    // another operation, other operands, and another element
    assert(refused(input("(= (bag.union b!0 b!0) b!0)", "(= ((as Node!1 (Bag!1 Int)) 1 b!0 b!0) b!0)")).contains("is not what the encoders make"))
    assert(refused(input("(= (bag.multiplicity k!0 b!0) 1)", "(= ((as get!1 (Int)) b!0 k!0) 2)")).contains("is not what the encoders make"))
    assert(refused(input("(= (bag.insert b!0 k!0) b!0)", "(= ((as Node!1 (Bag!1 Int)) 0 b!0 ((as Elem!1 (Bag!1 Int)) k!0 2)) b!0)")).contains("is not what"))
    // a symbol of the input faces the symbol of the sources of its identifier
    assert(refused(input("(= ((as size!1 (Int)) k!0) 1)", "(= ((as get!1 (Int)) k!0) 1)")).contains("is not what the encoders make"))
    assert(Encoders.check(input("(= ((as size!1 (Int)) k!0) 1)", "(= ((as size!2 (Int)) k!0) 1)"), Nil, sourceSymbols) == 1)
    // a bag without the encoder of bags
    assert(refused(input("(= (bag.union b!0 b!0) b!0)", "(= ((as Node!1 (Bag!1 Int)) 0 b!0 b!0) b!0)", "\"propositions\"")).contains("is not what"))
  }

  // a function `count` of the input, its source definition, and what the certificate says of it
  val counts = sexprs("""
    (define-fun-rec (par (A!1) (count!1 ((b!5 (Bag!1 A!1)) (x!5 A!1)) Int
      (ite (> ((as get!1 (A!1)) b!5 x!5) 0) ((as get!1 (A!1)) b!5 x!5) 0))))
  """)
  def function(body: String, encoded: String): List[SExpr] = parse(s"""
    (encoders "bags")
    (definitions
    (define-fun-rec (par (A!0) (count!1 ((b!2 (Bag A!0)) (x!2 A!0)) Int $body))))
    (function ((as count!1 (A!1)) b!5 x!5) (encoded $encoded))
    (symbols
    (count!1 function "count$$3"))
  """)
  val countSymbols = sourceSymbols ++ sexprs("""(count!1 function "count$3")""")
  val count = "(ite (> (bag.multiplicity x!2 b!2) 0) (bag.multiplicity x!2 b!2) 0)"
  val encodedCount = "(ite (> ((as get!1 (A!1)) b!5 x!5) 0) ((as get!1 (A!1)) b!5 x!5) 0)"

  test("a function of the sources is the encoding of the function of the input, simplified") {
    assert(Encoders.check(function(count, encodedCount), counts, countSymbols) == 1)
    // a body that the solver simplified is the original of its simplification
    val simplified = sexprs(s"(function count!1 (ite true $encodedCount 0) (steps (simplify () $encodedCount)))")
    assert(Encoders.check(function(s"(ite true $count 0)", s"(ite true $encodedCount 0)"), counts, countSymbols, simplified) == 1)
    // another body of the input, another simplification, and a function that the input doesn't give
    def refused(in: List[SExpr], definitions: Seq[SExpr] = counts, simplifications: Seq[SExpr] = Nil) =
      intercept[Failure](Encoders.check(in, definitions, countSymbols, simplifications)).getMessage
    assert(refused(function("(bag.multiplicity x!2 b!2)", encodedCount)).contains("is not what the encoders make"))
    assert(refused(function(s"(ite true $count 0)", s"(ite true $encodedCount 0)")).contains("is not the simplification of its encoded body"))
    assert(refused(function(count, encodedCount), simplifications = simplified).contains("is not the simplification of its encoded body"))
    assert(refused(input("true", "true"), counts).contains("the input doesn't say what count!1 is the simplification of"))
  }

  test("the datatype of bags is the encoder's") {
    def symbols = sourceSymbols ++ sexprs("""
      (op!1 selector "Node$0" "Bag$7[T$3]" "0")
      (left!1 selector "Node$0" "Bag$7[T$3]" "1")
      (right!1 selector "Node$0" "Bag$7[T$3]" "2")
      (key!1 selector "Elem$0" "Bag$7[T$3]" "0")
      (value!1 selector "Elem$0" "Bag$7[T$3]" "1")
    """)
    def bags(value: String) = sexprs(s"""(declare-datatypes ((Bag!1 1)) ((par (T!0) ((Node!1 (op!1 Int)
      (left!1 (Bag!1 T!0)) (right!1 (Bag!1 T!0))) (Elem!1 (key!1 T!0) ($value Int)) (Leaf!1)))))""")
    assert(Encoders.check(input("true", "true"), bags("value!1"), symbols) == 1)
    // the multiplicity of an element is its key
    assert(intercept[Failure](Encoders.check(input("true", "true"), bags("key!1"), symbols)).getMessage
      .contains("is not the definition of the encoder"))
  }

  test("bound variables face each other, and an unknown encoder is refused") {
    assert(Encoders.check(input(
      "(forall ((x!1 (Bag Int))) (= (bag.multiplicity k!0 x!1) 0))",
      "(forall ((x!5 (Bag!1 Int))) (= ((as get!1 (Int)) x!5 k!0) 0))"), Nil, sourceSymbols) == 1)
    assert(refused(input("(forall ((x!1 Int)) (= x!1 k!0))", "(forall ((x!5 Int)) (= k!0 x!5))")).contains("is not what"))
    assert(refused(input("true", "true", "\"strings\"")).contains("doesn't check the encoder strings"))
  }
}
