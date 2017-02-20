/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

import org.scalatest._

import inox.trees._

class TypeOpsSuite extends FunSuite with DatastructureUtils {
  import baseSymbols._
  import dsl._

  val tp    = TypeParameter.fresh("T")
  val tpD   = new TypeParameterDef(tp)

  val tp2   = TypeParameter.fresh("A")
  val tp3   = TypeParameter.fresh("B")

  val ListT = T(listID)(tp)
  val ConsT = T(consID)(tp)
  val NilT  = T(nilID)(tp)

  test("List subtyping") {
    assert(isSubtypeOf(tp,    tp),                            "T <: T")
    assert(isSubtypeOf(ListT, ListT),                         "List[T] <: List[T]")
    assert(isSubtypeOf(List.typed.toType, List.typed.toType), "List[T] <: List[T]")

    assert(isSubtypeOf(NilT,  ListT), "Subtypes are subtypes")
    assert(isSubtypeOf(ConsT, ListT), "Subtypes are subtypes")

    assert(!isSubtypeOf(ListT, NilT ), "Supertypes are not subtypes")
    assert(!isSubtypeOf(ListT, ConsT), "Supertypes are not subtypes")
  }

  test("Subtyping with params") {
    assert(!isSubtypeOf(T(nilID)(tp2), T(listID)(tp3)),         "Types are not subtypes with incompatible params")
    assert(!isSubtypeOf(T(nilID)(tp2), T(listID)(IntegerType)), "Types are not subtypes with incompatible params")
    assert(!isSubtypeOf(SetType(tp2),  SetType(tp3)),           "Types are not subtypes with incompatible params")
  }

  test("Invariant subtyping") {
    assert(!isSubtypeOf(T(nilID)(NilT), T(listID)(ListT)), "Classes are invariant")
    assert(!isSubtypeOf(SetType(NilT),  SetType(ListT)),   "Sets are invariant")
  }

  test("Function subtyping") {
    assert(isSubtypeOf(FunctionType(Seq(ListT), NilT), FunctionType(Seq(NilT), ListT)), "Functions have contravariant params/ covariant result")
  }

  test("Type compatibility") {
    assert(!typesCompatible(tp2,         tp3),          "Different types should be incompatible")
    assert(!typesCompatible(BooleanType, tp3),          "Different types should be incompatible")
    assert(!typesCompatible(tp2,         BooleanType),  "Different types should be incompatible")
    assert(!typesCompatible(IntegerType, Int32Type),    "Different types should be incompatible")
  }

  test("Type unification") {
    // Type parameters
    assert(unify(tp, tp2, Seq(tp) ).isDefined, "T <: A with T free")
    assert(unify(tp, tp2, Seq(tp2)).isDefined, "T <: A with A free")

    assert(unify(ListT, T(listID)(tp2), Seq(tp) ).isDefined, "List[T] <: List[A] with T free")
    assert(unify(ListT, T(listID)(tp2), Seq(tp2)).isDefined, "List[T] <: List[A] with A free")
    assert(unify(ListT, T(listID)(tp2), Seq()   ).isEmpty,   "List[T] !<: List[A] with A,T not free")
    assert(unify(ListT, NilT,           Seq(tp) ).isEmpty,   "Subtypes not unifiable")

    assert({
        val s = unify(MapType(IntegerType, tp), MapType(tp2, IntegerType), Seq(tp, tp2)).getOrElse(Seq.empty)
        s.contains(tp -> IntegerType) && s.contains(tp2 -> IntegerType)
      },
      "MapType unifiable"
    )
  }

  test("Type parameter instantiations") {
    assert(
      instantiation_>:(T(listID)(tp2), T(consID)(tp)) contains Map(tp2 -> tp),
      "List[A] >: Cons[T] under A -> T"
    )

    assert(
      instantiation_>:(T(listID)(tp2), T(consID)(IntegerType)) contains Map(tp2 -> IntegerType),
      "List[A] >: Cons[BigInt] under A -> BigInt"
    )

    assert(
      instantiation_<:(T(consID)(tp), T(listID)(tp2)) contains Map(tp -> tp2),
      "Cons[T] <: List[A] under T -> A"
    )

    assert(
      instantiation_<:(T(consID)(IntegerType), T(listID)(tp2)).isEmpty,
      "Cons[BigInt] cannot be instantiated so that it is <: List[A]"
    )

    assert(
      instantiation_>:(T(listID)(tp2), T(consID)(IntegerType)) contains Map(tp2 -> IntegerType),
      "List[A] >: Cons[BigInt] under A -> BigInt"
    )

    assert(
      instantiation_<:(
        TupleType(Seq(NilT, ConsT)),
        TupleType(Seq(T(listID)(tp2), T(listID)(tp2)))
      ).contains(Map(tp -> tp2)),
      "Covariant tuples"
    )

    assert(
      instantiation_<:(TupleType(Seq(IntegerType, Int32Type)), TupleType(Seq(IntegerType, Int32Type, IntegerType))).isEmpty,
      "Incompatible tuples"
    )

    assert(
      instantiation_<:(
        MapType(ConsT, IntegerType),
        MapType(ListT, IntegerType)
      ).isEmpty,
      "Invariant maps"
    )

    assert(
      instantiation_<:(
        MapType(tp, IntegerType),
        MapType(tp2, IntegerType)
      ).contains(Map(tp -> tp2)),
      "Instantiation within map type"
    )

    assert(
      instantiation_<:(
        FunctionType(Seq(ListT, ListT), NilT),
        FunctionType(Seq(T(consID)(tp2), T(nilID)(tp2)), T(nilID)(tp2))
      ).contains(Map(tp -> tp2)),
      "Covariant/ Contravariant function types"
    )

    // (List[A], A, List[A]) >: (List[List[BigInt]], Cons[BigInt], Nil[List[BigInt]])))
    // for A -> List[BigInt]
    assert(
      instantiation_>:(
        TupleType(Seq(ListT, tp, ListT)),
        TupleType(Seq(
          T(listID)(T(listID)(IntegerType)),
          T(consID)(IntegerType),
          T(nilID)(T(listID)(IntegerType))
        ))
      ).contains(Map(tp -> T(listID)(IntegerType))),
      "Complex example"
    )
  }
}
