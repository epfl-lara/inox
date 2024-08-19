/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package transformers

trait Transformer {
  val s: ast.Trees
  val t: ast.Trees

  type Env

  lazy val deconstructor: ast.TreeDeconstructor {
    val s: Transformer.this.s.type
    val t: Transformer.this.t.type
  } = s.getDeconstructor(t)

  def transform(id: Identifier, env: Env): Identifier = id

  def transform(id: Identifier, tpe: s.Type, env: Env): (Identifier, t.Type) = {
    (transform(id, env), transform(tpe, env))
  }

  def transform(vd: s.ValDef, env: Env): t.ValDef = {
    val s.ValDef(id, tpe, flags) = vd
    val (newId, newTpe) = transform(id, tpe, env)

    var changed = false
    val newFlags = for (f <- flags) yield {
      val newFlag = transform(f, env)
      if (f ne newFlag) changed = true
      newFlag
    }

    if ((id ne newId) || (tpe ne newTpe) || changed || (s ne t)) {
      t.ValDef(newId, newTpe, newFlags).copiedFrom(vd)
    } else {
      vd.asInstanceOf[t.ValDef]
    }
  }

  def transform(tpd: s.TypeParameterDef, env: Env): t.TypeParameterDef = {
    val newTp = transform(tpd.tp, env)

    if ((tpd.tp ne newTp) || (s ne t)) {
      t.TypeParameterDef(newTp.asInstanceOf[t.TypeParameter])
    } else {
      tpd.asInstanceOf[t.TypeParameterDef]
    }
  }

  def transform(e: s.Expr, env: Env): t.Expr = {
    val (ids, vs, es, tps, flags, builder) = deconstructor.deconstruct(e)

    var changed = false

    val newIds = for (id <- ids) yield {
      val newId = transform(id, env)
      if (id ne newId) changed = true
      newId
    }

    val newVs = for (v <- vs) yield {
      val vd = v.toVal
      val newVd = transform(vd, env)
      if (vd ne newVd) changed = true
      newVd.toVariable
    }

    val newEs = for (e <- es) yield {
      val newE = transform(e, env)
      if (e ne newE) changed = true
      newE
    }

    val newTps = for (tp <- tps) yield {
      val newTp = transform(tp, env)
      if (tp ne newTp) changed = true
      newTp
    }

    val newFlags = for (flag <- flags) yield {
      val newFlag = transform(flag, env)
      if (flag ne newFlag) changed = true
      newFlag
    }

    if (changed || (s ne t)) {
      builder(newIds, newVs, newEs, newTps, newFlags).copiedFrom(e)
    } else {
      e.asInstanceOf[t.Expr]
    }
  }

  def transform(tpe: s.Type, env: Env): t.Type = {
    val (ids, vs, es, tps, flags, builder) = deconstructor.deconstruct(tpe)

    var changed = false

    val newIds = for (id <- ids) yield {
      val newId = transform(id, env)
      if (id ne newId) changed = true
      newId
    }

    val newVs = for (v <- vs) yield {
      val vd = v.toVal
      val newVd = transform(vd, env)
      if (vd ne newVd) changed = true
      newVd.toVariable
    }

    val newEs = for (e <- es) yield {
      val newE = transform(e, env)
      if (e ne newE) changed = true
      newE
    }

    val newTps = for (tp <- tps) yield {
      val newTp = transform(tp, env)
      if (tp ne newTp) changed = true
      newTp
    }

    val newFlags = for (f <- flags) yield {
      val newFlag = transform(f, env)
      if (f ne newFlag) changed = true
      newFlag
    }

    val res =
    if (changed || (s ne t)) {
      builder(newIds, newVs, newEs, newTps, newFlags).copiedFrom(tpe)
    } else {
      tpe.asInstanceOf[t.Type]
    }

    res
  }

  def transform(flag: s.Flag, env: Env): t.Flag = {
    val (ids, es, tps, builder) = deconstructor.deconstruct(flag)

    var changed = false
    val newIds = for (id <- ids) yield {
      val newId = transform(id, env)
      if (id ne newId) changed = true
      newId
    }

    val newEs = for (e <- es) yield {
      val newE = transform(e, env)
      if (e ne newE) changed = true
      newE
    }

    val newTps = for (tp <- tps) yield {
      val newTp = transform(tp, env)
      if (tp ne newTp) changed = true
      newTp
    }

    if (changed || (s ne t)) {
      builder(newIds, newEs, newTps)
    } else {
      flag.asInstanceOf[t.Flag]
    }
  }
}

trait DefinitionTransformer extends Transformer {
  def initEnv: Env

  def transform(fd: s.FunDef): t.FunDef = {
    val env = initEnv

    new t.FunDef(
      transform(fd.id, env),
      fd.tparams map (transform(_, env)),
      fd.params map (transform(_, env)),
      transform(fd.returnType, env),
      transform(fd.fullBody, env),
      fd.flags map (transform(_, env))
    ).copiedFrom(fd)
  }

  def transform(sort: s.ADTSort): t.ADTSort = {
    val env = initEnv

    new t.ADTSort(
      transform(sort.id, env),
      sort.tparams map (transform(_, env)),
      sort.constructors map { cons =>
        new t.ADTConstructor(
          transform(cons.id, env),
          transform(cons.sort, env),
          cons.fields map (transform(_, env))
        ).copiedFrom(cons)
      },
      sort.flags map (transform(_, env))
    ).copiedFrom(sort)
  }
}

trait TreeTransformer extends DefinitionTransformer { self =>
  override final type Env = Unit
  override final val initEnv: Unit = ()

  def transform(id: Identifier): Identifier = super.transform(id, ())
  override final def transform(id: Identifier, env: Env): Identifier = transform(id)

  def transform(id: Identifier, tpe: s.Type): (Identifier, t.Type) = super.transform(id, tpe, ())
  override final def transform(id: Identifier, tpe: s.Type, env: Env): (Identifier, t.Type) = transform(id, tpe)

  def transform(vd: s.ValDef): t.ValDef = super.transform(vd, ())
  override final def transform(vd: s.ValDef, env: Env): t.ValDef = transform(vd)

  def transform(tpd: s.TypeParameterDef): t.TypeParameterDef = super.transform(tpd, ())
  override final def transform(tpd: s.TypeParameterDef, env: Env): t.TypeParameterDef = transform(tpd)

  def transform(e: s.Expr): t.Expr = super.transform(e, ())
  override final def transform(e: s.Expr, env: Env): t.Expr = transform(e)

  def transform(tpe: s.Type): t.Type = super.transform(tpe, ())
  override final def transform(tpe: s.Type, env: Env): t.Type = transform(tpe)

  def transform(flag: s.Flag): t.Flag = super.transform(flag, ())
  override final def transform(flag: s.Flag, env: Env): t.Flag = transform(flag)

  def compose(that: TreeTransformer { val t: self.s.type }): TreeTransformer {
    val s: that.s.type
    val t: self.t.type
  } = {
    // the scala type checker doesn't realize that this relation must hold here
    that `andThen` this.asInstanceOf[TreeTransformer {
      val s: that.t.type
      val t: self.t.type
    }]
  }

  def andThen(that: TreeTransformer { val s: self.t.type }): TreeTransformer {
    val s: self.s.type
    val t: that.t.type
  } = {
    class TreeTransformerComposition(val t1: self.type, val t2: that.type)
                                    (override val s: this.s.type,
                                     override val t: t2.t.type)
      extends TreeTransformer {

      override final def transform(id: Identifier): Identifier = t2.transform(t1.transform(id))

      override final def transform(id: Identifier, tpe: s.Type): (Identifier, t.Type) = {
        val (id1, tp1) = t1.transform(id, tpe)
        t2.transform(id1, tp1)
      }

      override final def transform(vd: s.ValDef): t.ValDef = t2.transform(t1.transform(vd))
      override final def transform(e: s.Expr): t.Expr = t2.transform(t1.transform(e))
      override final def transform(tpe: s.Type): t.Type = t2.transform(t1.transform(tpe))
      override final def transform(flag: s.Flag): t.Flag = t2.transform(t1.transform(flag))

      override final def transform(fd: s.FunDef): t.FunDef = t2.transform(t1.transform(fd))
      override final def transform(sort: s.ADTSort): t.ADTSort = t2.transform(t1.transform(sort))
    }

    new TreeTransformerComposition(this, that)(this.s, that.t)
  }
}

class ConcreteTreeTransformer(override val s: ast.Trees, override val t: ast.Trees)
  extends TreeTransformer