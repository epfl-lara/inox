
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

    lazy val deconstructor: TreeDeconstructor {
      val s: self.type
      val t: self.type
    } = self.deconstructor
  }

  class TreeIdentity extends SelfTreeTransformer {
    override def transform(id: Identifier, tpe: s.Type): (Identifier, t.Type) = (id, tpe)
    override def transform(v: s.Variable): t.Variable = v
    override def transform(vd: s.ValDef): t.ValDef = vd
    override def transform(e: s.Expr): t.Expr = e
    override def transform(tpe: s.Type): t.Type = tpe
    override def transform(flag: s.Flag): t.Flag = flag
  }

  lazy val TreeIdentity: SelfTransformer = new TreeIdentity

  class SymbolIdentity extends SymbolTransformer {
    val transformer = TreeIdentity
    override def transform(syms: s.Symbols): t.Symbols = syms
  }

  lazy val SymbolIdentity: SymbolTransformer { val transformer: SelfTransformer } = new SymbolIdentity

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

  val deconstructor: TreeDeconstructor {
    val s: TreeTransformer.this.s.type
    val t: TreeTransformer.this.t.type
  }

  def transform(id: Identifier, tpe: s.Type): (Identifier, t.Type) = (id, transform(tpe))

  def transform(v: s.Variable): t.Variable = {
    val (id, tpe) = transform(v.id, v.tpe)
    if ((id ne v.id) || (tpe ne v.tpe) || (s ne t)) {
      t.Variable(id, tpe).copiedFrom(v)
    } else {
      v.asInstanceOf[t.Variable]
    }
  }

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

  protected trait TreeTransformerComposition extends TreeTransformer {
    protected val t1: TreeTransformer
    protected val t2: TreeTransformer { val s: t1.t.type }

    lazy val s: t1.s.type = t1.s
    lazy val t: t2.t.type = t2.t

    override def transform(id: Identifier, tpe: s.Type): (Identifier, t.Type) = {
      val (id1, tp1) = t1.transform(id, tpe)
      t2.transform(id1, tp1)
    }

    override def transform(v: s.Variable): t.Variable = t2.transform(t1.transform(v))
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

    lazy val deconstructor: TreeDeconstructor {
      val s: TreeTransformer.this.s.type
      val t: that.t.type
    } = new TreeDeconstructor {
      protected val s: TreeTransformer.this.s.type = TreeTransformer.this.s
      protected val t: that.t.type = that.t
    }
  }
}

/** Symbol table transformer */
trait SymbolTransformer {
  val transformer: TreeTransformer
  lazy val s: transformer.s.type = transformer.s
  lazy val t: transformer.t.type = transformer.t

  def transform(id: Identifier, tpe: s.Type): (Identifier, t.Type) = transformer.transform(id, tpe)
  def transform(v: s.Variable): t.Variable = transformer.transform(v)
  def transform(vd: s.ValDef): t.ValDef = transformer.transform(vd)
  def transform(e: s.Expr): t.Expr = transformer.transform(e)
  def transform(tpe: s.Type): t.Type = transformer.transform(tpe)
  def transform(flag: s.Flag): t.Flag = transformer.transform(flag)

  /* Type parameters can't be modified by transformed but they need to be
   * translated into the new tree definitions given by `t`. */
  protected def transformTypeParams(tparams: Seq[s.TypeParameterDef]): Seq[t.TypeParameterDef] = {
    if (s eq t) tparams.asInstanceOf[Seq[t.TypeParameterDef]]
    else tparams.map(tdef => t.TypeParameterDef(t.TypeParameter(tdef.id)))
  }

  protected def transformFunction(fd: s.FunDef): t.FunDef = new t.FunDef(
    fd.id,
    transformTypeParams(fd.tparams),
    fd.params.map(vd => transformer.transform(vd)),
    transformer.transform(fd.returnType),
    transformer.transform(fd.fullBody),
    fd.flags.map(f => transformer.transform(f))
  )

  protected def transformADT(adt: s.ADTDefinition): t.ADTDefinition = adt match {
    case sort: s.ADTSort if (s eq t) => sort.asInstanceOf[t.ADTSort]
    case sort: s.ADTSort => new t.ADTSort(
      sort.id,
      transformTypeParams(sort.tparams),
      sort.cons,
      sort.flags.map(f => transformer.transform(f)))
    case cons: s.ADTConstructor => new t.ADTConstructor(
      cons.id,
      transformTypeParams(cons.tparams),
      cons.sort,
      cons.fields.map(vd => transformer.transform(vd)),
      cons.flags.map(f => transformer.transform(f)))
  }

  def transform(syms: s.Symbols): t.Symbols = t.NoSymbols
    .withFunctions(syms.functions.values.toSeq.map(transformFunction))
    .withADTs(syms.adts.values.toSeq.map(transformADT))

  def compose(that: SymbolTransformer {
    val transformer: TreeTransformer { val t: SymbolTransformer.this.s.type }
  }): SymbolTransformer {
    val transformer: TreeTransformer {
      val s: that.s.type
      val t: SymbolTransformer.this.t.type
    }
  } = new SymbolTransformer {
    val transformer = SymbolTransformer.this.transformer compose that.transformer
    override def transform(syms: s.Symbols): t.Symbols = SymbolTransformer.this.transform(that.transform(syms))
  }

  def andThen(that: SymbolTransformer {
    val transformer: TreeTransformer { val s: SymbolTransformer.this.t.type }
  }): SymbolTransformer {
    val transformer: TreeTransformer {
      val s: SymbolTransformer.this.s.type
      val t: that.t.type
    }
  } = {
    // the scala compiler doesn't realize that this relation must hold here
    that compose this.asInstanceOf[SymbolTransformer {
      val transformer: TreeTransformer {
        val s: SymbolTransformer.this.s.type
        val t: that.s.type
      }
    }]
  }
}

trait TreeBijection {
  val s: Trees
  val t: Trees

  val encoder: SymbolTransformer { val transformer: TreeTransformer {
    val s: TreeBijection.this.s.type
    val t: TreeBijection.this.t.type
  }}

  val decoder: SymbolTransformer { val transformer: TreeTransformer {
    val s: TreeBijection.this.t.type
    val t: TreeBijection.this.s.type
  }}

  def encode(vd: s.ValDef): t.ValDef = encoder.transform(vd)
  def decode(vd: t.ValDef): s.ValDef = decoder.transform(vd)

  def encode(v: s.Variable): t.Variable = encoder.transform(v)
  def decode(v: t.Variable): s.Variable = decoder.transform(v)

  def encode(e: s.Expr): t.Expr = encoder.transform(e)
  def decode(e: t.Expr): s.Expr = decoder.transform(e)

  def encode(tpe: s.Type): t.Type = encoder.transform(tpe)
  def decode(tpe: t.Type): s.Type = decoder.transform(tpe)

  def inverse: TreeBijection {
    val s: TreeBijection.this.t.type
    val t: TreeBijection.this.s.type
  } = new TreeBijection {
    val s: TreeBijection.this.t.type = TreeBijection.this.t
    val t: TreeBijection.this.s.type = TreeBijection.this.s

    val encoder = TreeBijection.this.decoder
    val decoder = TreeBijection.this.encoder
  }

  def compose(that: TreeBijection { val t: TreeBijection.this.s.type }): TreeBijection {
    val s: that.s.type
    val t: TreeBijection.this.t.type
  } = new TreeBijection {
    val s: that.s.type = that.s
    val t: TreeBijection.this.t.type = TreeBijection.this.t

    val encoder = TreeBijection.this.encoder compose that.encoder
    val decoder = that.decoder compose TreeBijection.this.decoder
  }

  def andThen(that: TreeBijection { val s: TreeBijection.this.t.type }): TreeBijection {
    val s: TreeBijection.this.s.type
    val t: that.t.type
  } = new TreeBijection {
    val s: TreeBijection.this.s.type = TreeBijection.this.s
    val t: that.t.type = that.t

    val encoder = TreeBijection.this.encoder andThen that.encoder
    val decoder = that.decoder andThen TreeBijection.this.decoder
  }
}
