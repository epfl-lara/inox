/* Copyright 2009-2020 EPFL, Lausanne */

package inox
package solvers
package theories

class MapMergeEncoder private(override val sourceProgram: Program)
                             (theory: MapMergeTheory[sourceProgram.trees.type])
  extends SimpleEncoder(
    sourceProgram,
    mapMergeEnc(sourceProgram)(theory),
    mapMergeDec(sourceProgram)(theory),
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

def mapMergeEnc(sourceProgram: Program)
               (theory: MapMergeTheory[sourceProgram.trees.type]): transformers.TreeTransformer { val s: sourceProgram.trees.type; val t: sourceProgram.trees.type } = {
  class MapMergeEnc extends theory.trees.ConcreteSelfTreeTransformer {
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
  new MapMergeEnc
}

def mapMergeDec(sourceProgram: Program)
               (theory: MapMergeTheory[sourceProgram.trees.type]): transformers.TreeTransformer { val s: sourceProgram.trees.type; val t: sourceProgram.trees.type } = {
  class MapMergeDec extends theory.trees.ConcreteSelfTreeTransformer {
    import theory._
    import theory.trees._
    import theory.trees.dsl._

    override def transform(e: Expr): Expr = e match {
      case FunctionInvocation(MapMergeID, _, Seq(mask, map1, map2)) =>
        MapMerge(transform(mask), transform(map1), transform(map2)).copiedFrom(e)
      case _ => super.transform(e)
    }
  }
  new MapMergeDec
}

object MapMergeEncoder {
  def apply(p: Program): MapMergeEncoder { val sourceProgram: p.type } =
    new MapMergeEncoder(p)(new MapMergeTheory[p.trees.type](p.trees)).asInstanceOf
}
