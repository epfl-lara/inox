/* Copyright 2009-2020 EPFL, Lausanne */

package inox
package solvers
package theories

trait MapMergeEncoder extends SimpleEncoder {
  import trees._

  object MapMergeEncoded {
    def apply(e: MapMerge)(implicit s: Symbols): Expr = {
      val MapMerge(mask, map1, map2) = e
      val mapTpe @ MapType(keyTpe, _) = map1.getType
      val (mapVd, keyVd) = (ValDef.fresh("map", mapTpe), ValDef.fresh("x", keyTpe))
      val (mapV, keyV) = (mapVd.toVariable, keyVd.toVariable)
      val cond = Equals(
        MapApply(mapV, keyV).copiedFrom(e),
        IfExpr(
          ElementOfSet(keyV, mask).copiedFrom(e),
          MapApply(map1, keyV).copiedFrom(e),
          MapApply(map2, keyV).copiedFrom(e)).copiedFrom(e)).copiedFrom(e)
      Choose(mapVd, Forall(Seq(keyVd), cond).copiedFrom(e)).copiedFrom(e)
    }

    def unapply(e: Expr)(implicit s: Symbols): Option[(Expr, Expr, Expr)] =
      e match {
        case Choose(mapVd, Forall(Seq(keyVd),
            Equals(
              MapApply(mapV1: Variable, keyV1: Variable),
              IfExpr(
                ElementOfSet(keyV2: Variable, mask),
                MapApply(map1, keyV3: Variable),
                MapApply(map2, keyV4: Variable)))))
            if keyV1.id == keyVd.id && keyV2.id == keyVd.id &&
               keyV3.id == keyVd.id && keyV4.id == keyVd.id &&
               mapV1.id == mapVd.id =>
          Some((mask, map1, map2))
        case _ => None
      }
  }

  protected object encoder extends SelfTreeTransformer {
    import sourceProgram._

    override def transform(e: Expr): Expr = e match {
      case e: MapMerge => transform(MapMergeEncoded(e))
      case _ => super.transform(e)
    }
  }

  protected object decoder extends SelfTreeTransformer {
    import targetProgram._

    override def transform(e: Expr): Expr = e match {
      case MapMergeEncoded(mask, map1, map2) =>
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
