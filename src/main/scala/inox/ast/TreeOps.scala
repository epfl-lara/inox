
package inox
package ast

trait TreeOps { self: Trees =>

  type SelfTransformer = TreeTransformer {
    val s: self.type
    val t: self.type
  }

  trait SelfTreeTransformer extends TreeTransformer {
    val s: self.type = self
    val t: self.type = self
  }

  trait IdentityTreeTransformer extends SelfTreeTransformer {
    override def transform(id: Identifier, tpe: s.Type): (Identifier, t.Type) = (id, tpe)
    override def transform(vd: s.ValDef): t.ValDef = vd
    override def transform(e: s.Expr): t.Expr = e
    override def transform(tpe: s.Type): t.Type = tpe
    override def transform(flag: s.Flag): t.Flag = flag
  }

  trait IdentitySymbolTransformer extends SymbolTransformer {
    val s: self.type = self
    val t: self.type = self

    override def transform(syms: s.Symbols): t.Symbols = syms
  }

  trait TreeTraverser {
    def traverse(vd: ValDef): Unit = {
      traverse(vd.tpe)
      vd.flags.foreach(traverse)
    }

    def traverse(tpd: TypeParameterDef): Unit = {
      traverse(tpd.tp)
    }

    def traverse(e: Expr): Unit = {
      val (vs, es, tps, _) = deconstructor.deconstruct(e)
      vs.foreach(v => traverse(v.toVal))
      es.foreach(traverse)
      tps.foreach(traverse)
    }

    def traverse(tpe: Type): Unit = {
      val (tps, flags, _) = deconstructor.deconstruct(tpe)
      tps.foreach(traverse)
      flags.foreach(traverse)
    }

    def traverse(flag: Flag): Unit = {
      val (es, tps, _) = deconstructor.deconstruct(flag)
      es.foreach(traverse)
      tps.foreach(traverse)
    }

    final def traverse(fd: FunDef): Unit = {
      fd.tparams.foreach(traverse)
      fd.params.foreach(traverse)
      traverse(fd.returnType)
      traverse(fd.fullBody)
      fd.flags.foreach(traverse)
    }

    final def traverse(adt: ADTDefinition): Unit = adt match {
      case sort: ADTSort =>
        sort.tparams.foreach(traverse)
        sort.flags.foreach(traverse)

      case cons: ADTConstructor =>
        cons.tparams.foreach(traverse)
        cons.fields.foreach(traverse)
        cons.flags.foreach(traverse)
    }
  }
}

trait TreeTransformer {
  val s: Trees
  val t: Trees

  lazy val deconstructor: TreeDeconstructor {
    val s: TreeTransformer.this.s.type
    val t: TreeTransformer.this.t.type
  } = s.getDeconstructor(t)

  def transform(id: Identifier, tpe: s.Type): (Identifier, t.Type) = (id, transform(tpe))

  def transform(vd: s.ValDef): t.ValDef = {
    val s.ValDef(id, tpe, flags) = vd
    val (newId, newTpe) = transform(id, tpe)

    var changed = false
    val newFlags = for (f <- flags) yield {
      val newFlag = transform(f)
      if (f ne newFlag) changed = true
      newFlag
    }

    if ((id ne newId) || (tpe ne newTpe) || changed || (s ne t)) {
      t.ValDef(newId, newTpe, newFlags).copiedFrom(vd)
    } else {
      vd.asInstanceOf[t.ValDef]
    }
  }

  def transform(tpd: s.TypeParameterDef): t.TypeParameterDef = {
    val newTp = transform(tpd.tp)

    if ((tpd.tp ne newTp) || (s ne t)) {
      t.TypeParameterDef(newTp.asInstanceOf[t.TypeParameter])
    } else {
      tpd.asInstanceOf[t.TypeParameterDef]
    }
  }

  def transform(e: s.Expr): t.Expr = {
    val (vs, es, tps, builder) = deconstructor.deconstruct(e)

    var changed = false
    val newVs = for (v <- vs) yield {
      val vd = v.toVal
      val newVd = transform(vd)
      if (vd ne newVd) changed = true
      newVd.toVariable
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

    if (changed || (s ne t)) {
      builder(newVs, newEs, newTps).copiedFrom(e)
    } else {
      e.asInstanceOf[t.Expr]
    }
  }

  def transform(tpe: s.Type): t.Type = {
    val (tps, flags, builder) = deconstructor.deconstruct(tpe)

    var changed = false
    val newTps = for (tp <- tps) yield {
      val newTp = transform(tp)
      if (tp ne newTp) changed = true
      newTp
    }

    val newFlags = for (f <- flags) yield {
      val newFlag = transform(f)
      if (f ne newFlag) changed = true
      newFlag
    }

    if (changed || (s ne t)) {
      builder(newTps, newFlags).copiedFrom(tpe)
    } else {
      tpe.asInstanceOf[t.Type]
    }
  }

  def transform(flag: s.Flag): t.Flag = {
    val (es, tps, builder) = deconstructor.deconstruct(flag)

    var changed = false
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

    if (changed || (s ne t)) {
      builder(newEs, newTps)
    } else {
      flag.asInstanceOf[t.Flag]
    }
  }

  final def transform(fd: s.FunDef): t.FunDef = {
    new t.FunDef(
      fd.id,
      fd.tparams map transform,
      fd.params map transform,
      transform(fd.returnType),
      transform(fd.fullBody),
      fd.flags map transform
    ).copiedFrom(fd)
  }

  final def transform(adt: s.ADTDefinition): t.ADTDefinition = adt match {
    case sort: s.ADTSort => new t.ADTSort(
      sort.id,
      sort.tparams map transform,
      sort.cons,
      sort.flags map transform
    )

    case cons: s.ADTConstructor => new t.ADTConstructor(
      cons.id,
      cons.tparams map transform,
      cons.sort,
      cons.fields map transform,
      cons.flags map transform
    )
  }

  protected trait TreeTransformerComposition extends TreeTransformer {
    protected val t1: TreeTransformer
    protected val t2: TreeTransformer { val s: t1.t.type }

    lazy val s: t1.s.type = t1.s
    lazy val t: t2.t.type = t2.t

    override def transform(id: Identifier, tpe: s.Type): (Identifier, t.Type) = {
      val (id1, tp1) = t1.transform(id, tpe)
      t2.transform(id1, tp1)
    }

    override def transform(vd: s.ValDef): t.ValDef = t2.transform(t1.transform(vd))
    override def transform(e: s.Expr): t.Expr = t2.transform(t1.transform(e))
    override def transform(tpe: s.Type): t.Type = t2.transform(t1.transform(tpe))
    override def transform(flag: s.Flag): t.Flag = t2.transform(t1.transform(flag))
  }

  def compose(that: TreeTransformer { val t: TreeTransformer.this.s.type }): TreeTransformer {
    val s: that.s.type
    val t: TreeTransformer.this.t.type
  } = {
    // the scala type checker doesn't realize that this relation must hold here
    that andThen this.asInstanceOf[TreeTransformer {
      val s: that.t.type
      val t: TreeTransformer.this.t.type
    }]
  }

  def andThen(that: TreeTransformer { val s: TreeTransformer.this.t.type }): TreeTransformer {
    val s: TreeTransformer.this.s.type
    val t: that.t.type
  } = new TreeTransformerComposition {
    val t1: TreeTransformer.this.type = TreeTransformer.this
    val t2: that.type = that
  }
}

/** Enables equality checks between symbol transformer compositions */
private[ast] trait SymbolTransformerComposition extends SymbolTransformer {
  protected val lhs: SymbolTransformer
  protected val rhs: SymbolTransformer { val t: lhs.s.type }

  val s: rhs.s.type = rhs.s
  val t: lhs.t.type = lhs.t

  override def transform(syms: s.Symbols): t.Symbols = lhs.transform(rhs.transform(syms))

  override def equals(that: Any): Boolean = that match {
    case c: SymbolTransformerComposition => rhs == c.rhs && lhs == c.lhs
    case _ => false
  }

  override def hashCode: Int = 31 * rhs.hashCode + lhs.hashCode
}

/** Symbol table transformer base type */
trait SymbolTransformer { self =>
  val s: Trees
  val t: Trees

  def transform(syms: s.Symbols): t.Symbols

  def compose(that: SymbolTransformer { val t: self.s.type }): SymbolTransformer {
    val s: that.s.type
    val t: self.t.type
  } = new {
    val rhs: that.type = that
    val lhs: self.type = self
  } with SymbolTransformerComposition

  def andThen(that: SymbolTransformer {
    val s: self.t.type
  }): SymbolTransformer {
    val s: self.s.type
    val t: that.t.type
  } = {
    // the scala compiler doesn't realize that this relation must hold here
    that compose this.asInstanceOf[SymbolTransformer {
      val s: self.s.type
      val t: that.s.type
    }]
  }
}

trait SimpleSymbolTransformer extends SymbolTransformer { self =>
  protected def transformFunction(fd: s.FunDef): t.FunDef
  protected def transformADT(adt: s.ADTDefinition): t.ADTDefinition

  def transform(syms: s.Symbols): t.Symbols = t.NoSymbols
    .withFunctions(syms.functions.values.toSeq.map(transformFunction))
    .withADTs(syms.adts.values.toSeq.map(transformADT))
}

object SymbolTransformer {
  def apply(trans: TreeTransformer): SymbolTransformer {
    val s: trans.s.type
    val t: trans.t.type
  } = new SimpleSymbolTransformer {
    val s: trans.s.type = trans.s
    val t: trans.t.type = trans.t

    protected def transformFunction(fd: s.FunDef): t.FunDef = trans.transform(fd)
    protected def transformADT(adt: s.ADTDefinition): t.ADTDefinition = trans.transform(adt)
  }
}
