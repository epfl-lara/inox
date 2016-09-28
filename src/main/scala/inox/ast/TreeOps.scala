
package inox
package ast

trait TreeOps { self: Trees =>

  trait TreeTransformer {
    def transform(id: Identifier, tpe: Type): (Identifier, Type) = (id, transform(tpe))

    def transform(v: Variable): Variable = {
      val (id, tpe) = transform(v.id, v.tpe)
      if ((id ne v.id) || (tpe ne v.tpe)) {
        Variable(id, tpe).copiedFrom(v)
      } else {
        v
      }
    }

    def transform(vd: ValDef): ValDef = {
      val (id, es, Seq(tpe), builder) = deconstructor.deconstruct(vd)
      val (newId, newTpe) = transform(id, tpe)

      var changed = false
      val newEs = for (e <- es) yield {
        val newE = transform(e)
        if (e ne newE) changed = true
        newE
      }

      if ((id ne newId) || (tpe ne newTpe) || changed) {
        builder(newId, newEs, Seq(newTpe)).copiedFrom(vd).asInstanceOf[ValDef]
      } else {
        vd
      }
    }

    def transform(e: Expr): Expr = {
      val (vs, es, tps, builder) = deconstructor.deconstruct(e)

      var changed = false
      val newVs = for (v <- vs) yield {
        val newV = transform(v)
        if (v ne newV) changed = true
        newV
      }

      val newEs = for (e <- es) yield {
        val newE = transform(e)
        if (e ne newE) changed = true
        newE
      }

      val newTps = for (tp <- tps) yield {
        val newTp = transform(tp)
        if (tp ne newTp) changed = true
        newTp
      }

      if (changed) {
        builder(newVs, newEs, newTps).copiedFrom(e)
      } else {
        e
      }
    }

    def transform(t: Type): Type = {
      val (tps, builder) = deconstructor.deconstruct(t)

      var changed = false
      val newTps = for (tp <- tps) yield {
        val newTp = transform(tp)
        if (tp ne newTp) changed = true
        newTp
      }

      if (changed) {
        builder(newTps).copiedFrom(t)
      } else {
        t
      }
    }
  }

  trait TreeTraverser {
    def traverse(vd: ValDef): Unit = traverse(vd.tpe)

    def traverse(v: Variable): Unit = traverse(v.tpe)

    def traverse(e: Expr): Unit = {
      val (vs, es, tps, _) = deconstructor.deconstruct(e)
      vs.foreach(traverse)
      es.foreach(traverse)
      tps.foreach(traverse)
    }

    def traverse(tpe: Type): Unit = {
      val (tps, _) = deconstructor.deconstruct(tpe)
      tps.foreach(traverse)
    }
  }
}
