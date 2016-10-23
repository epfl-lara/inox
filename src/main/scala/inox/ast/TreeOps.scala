
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

trait TreeTransformer {
  val s: Trees
  val t: Trees

  lazy val deconstructor: TreeDeconstructor {
    val s: TreeTransformer.this.s.type
    val t: TreeTransformer.this.t.type
  } = s.getDeconstructor(t)

  def transform(id: Identifier, tpe: s.Type): (Identifier, t.Type) = (id, transform(tpe))

  def transform(vd: s.ValDef): t.ValDef = {
    val (id, es, Seq(tpe), builder) = deconstructor.deconstruct(vd)
    val (newId, newTpe) = transform(id, tpe)

    var changed = false
    val newEs = for (e <- es) yield {
      val newE = transform(e)
      if (e ne newE) changed = true
      newE
    }

    if ((id ne newId) || (tpe ne newTpe) || changed || (s ne t)) {
      builder(newId, newEs, Seq(newTpe)).copiedFrom(vd).asInstanceOf[t.ValDef]
    } else {
      vd.asInstanceOf[t.ValDef]
    }
  }

  def transform(e: s.Expr): t.Expr = {
    val (vs, es, tps, builder) = deconstructor.deconstruct(e)

    var changed = false
    val newVs = for (v <- vs) yield {
      val newV = transformVariable(v)
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

    if (changed || (s ne t)) {
      builder(newVs, newEs, newTps).copiedFrom(e)
    } else {
      e.asInstanceOf[t.Expr]
    }
  }

  def transform(tpe: s.Type): t.Type = {
    val (tps, builder) = deconstructor.deconstruct(tpe)

    var changed = false
    val newTps = for (tp <- tps) yield {
      val newTp = transform(tp)
      if (tp ne newTp) changed = true
      newTp
    }

    if (changed || (s ne t)) {
      builder(newTps).copiedFrom(tpe)
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

  /* Type parameters can't be modified by transformed but they need to be
   * translated into the new tree definitions given by `t`. */
  @inline
  final def transformTypeParams(tparams: Seq[s.TypeParameterDef]): Seq[t.TypeParameterDef] = {
    if (s eq t) tparams.asInstanceOf[Seq[t.TypeParameterDef]]
    else tparams.map(tdef => t.TypeParameterDef(t.TypeParameter(tdef.id)))
  }

  @inline
  final def transformVariable(v: s.Variable): t.Variable = {
    val (nid, ntpe) = transform(v.id, v.tpe)
    if ((v.id ne nid) || (v.tpe ne ntpe) || (s ne t)) t.Variable(nid, ntpe).copiedFrom(v)
    else v.asInstanceOf[t.Variable]
  }

  final def transform(fd: s.FunDef): t.FunDef = {
    new t.FunDef(
      fd.id,
      transformTypeParams(fd.tparams),
      fd.params.map(transform),
      transform(fd.returnType),
      transform(fd.fullBody),
      fd.flags map transform
    )
  }

  final def transform(adt: s.ADTDefinition): t.ADTDefinition = adt match {
    case sort: s.ADTSort if (s eq t) => sort.asInstanceOf[t.ADTSort]

    case sort: s.ADTSort => new t.ADTSort(
      sort.id,
      transformTypeParams(sort.tparams),
      sort.cons,
      sort.flags map transform
    )

    case cons: s.ADTConstructor => new t.ADTConstructor(
      cons.id,
      transformTypeParams(cons.tparams),
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

/** Symbol table transformer base type */
trait SymbolTransformer { self =>
  val s: Trees
  val t: Trees

  def transform(syms: s.Symbols): t.Symbols

  def compose(that: SymbolTransformer {
    val t: self.s.type
  }): SymbolTransformer {
    val s: that.s.type
    val t: self.t.type
  } = new SymbolTransformer {
    val s: that.s.type = that.s
    val t: self.t.type = self.t
    override def transform(syms: s.Symbols): t.Symbols = self.transform(that.transform(syms))
  }

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
