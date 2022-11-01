/* Copyright 2009-2020 EPFL, Lausanne */

package inox
package solvers
package theories

class MapMergeEncoder private(override val sourceProgram: Program)
                             (theory: MapMergeTheory[sourceProgram.trees.type])
  extends SimpleEncoder(
    sourceProgram,
    new MapMergeEnc[sourceProgram.type](sourceProgram)(theory).asInstanceOf,
    new MapMergeDec[sourceProgram.type](sourceProgram)(theory).asInstanceOf,
    theory.extraFunctions)

private class MapMergeTheory[Trees <: ast.Trees](val trees: Trees) {
  import trees._
  import trees.dsl._

  val MapMergeID = FreshIdentifier("mapMerge")
  val MapMergeFun = mkFunDef(MapMergeID)("K", "V") { case Seq(keyT, valueT) =>
    val mapTpe = MapType(keyT, valueT)
    (Seq("mask" :: SetType(keyT), "map1" :: mapTpe, "map2" :: mapTpe), mapTpe, {
      case Seq(mask, map1, map2) =>
        choose("map" :: mapTpe) { map =>
          forall("x" :: keyT) { x =>
            MapApply(map, x) ===
              (if_ (ElementOfSet(x, mask)) {
                MapApply(map1, x)
              } else_ {
                MapApply(map2, x)
              })
          }
        }
    })
  }

  val extraFunctions = Seq(MapMergeFun)
}

private class MapMergeEnc[Prog <: Program]
  (val sourceProgram: Prog)
  (val theory: MapMergeTheory[sourceProgram.trees.type]) extends theory.trees.ConcreteSelfTreeTransformer {
  import theory._
  import theory.trees._
  import theory.trees.dsl._
  import sourceProgram.symbols.{given, _}

  override def transform(e: Expr): Expr = e match {
    case MapMerge(mask, map1, map2) =>
      val MapType(keyTpe, valueTpe) = map1.getType: @unchecked
      MapMergeFun(transform(keyTpe), transform(valueTpe))(
        transform(mask), transform(map1), transform(map2)).copiedFrom(e)
    case _ => super.transform(e)
  }
}

private class MapMergeDec[Prog <: Program]
  (val sourceProgram: Prog)
  (val theory: MapMergeTheory[sourceProgram.trees.type]) extends theory.trees.ConcreteSelfTreeTransformer {
  import theory._
  import theory.trees._
  import theory.trees.dsl._

  override def transform(e: Expr): Expr = e match {
    case FunctionInvocation(MapMergeID, _, Seq(mask, map1, map2)) =>
      MapMerge(transform(mask), transform(map1), transform(map2)).copiedFrom(e)
    case _ => super.transform(e)
  }
}

object MapMergeEncoder {
  def apply(p: Program): MapMergeEncoder { val sourceProgram: p.type } =
    new MapMergeEncoder(p)(new MapMergeTheory[p.trees.type](p.trees)).asInstanceOf
}
