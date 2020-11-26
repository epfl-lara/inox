/* Copyright 2009-2020 EPFL, Lausanne */

package inox
package solvers
package theories

trait MapMergeEncoder extends SimpleEncoder {
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

  override val extraFunctions = Seq(MapMergeFun)

  protected object encoder extends SelfTreeTransformer {
    import sourceProgram._

    override def transform(e: Expr): Expr = e match {
      case MapMerge(mask, map1, map2) =>
        val MapType(keyTpe, valueTpe) = map1.getType
        MapMergeFun(transform(keyTpe), transform(valueTpe))(
          transform(mask), transform(map1), transform(map2)).copiedFrom(e)
      case _ => super.transform(e)
    }
  }

  protected object decoder extends SelfTreeTransformer {
    import targetProgram._

    override def transform(e: Expr): Expr = e match {
      case FunctionInvocation(MapMergeID, _, Seq(mask, map1, map2)) =>
        MapMerge(transform(mask), transform(map1), transform(map2)).copiedFrom(e)
      case _ => super.transform(e)
    }
  }
}

object MapMergeEncoder {
  def apply(p: Program): MapMergeEncoder { val sourceProgram: p.type } = new {
    val sourceProgram: p.type = p
  } with MapMergeEncoder
}
