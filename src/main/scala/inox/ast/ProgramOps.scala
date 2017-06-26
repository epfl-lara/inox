/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

trait ProgramTransformer { self =>
  val sourceProgram: Program
  val targetProgram: Program

  protected val encoder: TreeTransformer {
    val s: self.sourceProgram.trees.type
    val t: self.targetProgram.trees.type
  }

  protected val decoder: TreeTransformer {
    val s: self.targetProgram.trees.type
    val t: self.sourceProgram.trees.type
  }

  def encode(vd: sourceProgram.trees.ValDef) = encoder.transform(vd)
  def decode(vd: targetProgram.trees.ValDef) = decoder.transform(vd)

  def encode(v: sourceProgram.trees.Variable) = encoder.transform(v).asInstanceOf[targetProgram.trees.Variable]
  def decode(v: targetProgram.trees.Variable) = decoder.transform(v).asInstanceOf[sourceProgram.trees.Variable]

  def encode(e: sourceProgram.trees.Expr) = encoder.transform(e)
  def decode(e: targetProgram.trees.Expr) = decoder.transform(e)

  def encode(tpe: sourceProgram.trees.Type) = encoder.transform(tpe)
  def decode(tpe: targetProgram.trees.Type) = decoder.transform(tpe)

  def compose(that: ProgramTransformer { val targetProgram: self.sourceProgram.type }): ProgramTransformer {
    val sourceProgram: that.sourceProgram.type
    val targetProgram: self.targetProgram.type
  } = new ProgramTransformer {
    val sourceProgram: that.sourceProgram.type = that.sourceProgram
    val targetProgram: self.targetProgram.type = self.targetProgram

    protected val encoder = self.encoder compose that.encoder
    protected val decoder = that.decoder compose self.decoder
  }

  def andThen(that: ProgramTransformer { val sourceProgram: self.targetProgram.type }): ProgramTransformer {
    val sourceProgram: self.sourceProgram.type
    val targetProgram: that.targetProgram.type
  } = new ProgramTransformer {
    val sourceProgram: self.sourceProgram.type = self.sourceProgram
    val targetProgram: that.targetProgram.type = that.targetProgram

    protected val encoder = self.encoder andThen that.encoder
    protected val decoder = that.decoder andThen self.decoder
  }

  def reverse: ProgramTransformer {
    val sourceProgram: self.targetProgram.type
    val targetProgram: self.sourceProgram.type
  } = new ProgramTransformer {
    val sourceProgram: self.targetProgram.type = self.targetProgram
    val targetProgram: self.sourceProgram.type = self.sourceProgram

    protected val encoder = self.decoder
    protected val decoder = self.encoder
  }
}

trait ProgramEncoder extends ProgramTransformer { self =>
  lazy final val s: sourceProgram.trees.type = sourceProgram.trees
  val t: Trees

  protected val extraFunctions: Seq[t.FunDef] = Seq.empty
  protected val extraADTs: Seq[t.ADTDefinition] = Seq.empty

  /** Override point for more complex program transformations */
  protected def encodedProgram: Program { val trees: t.type } = {
    sourceProgram.transform(SymbolTransformer(encoder))
  }

  lazy final val targetProgram: Program { val trees: t.type } = {
    encodedProgram.withFunctions(extraFunctions).withADTs(extraADTs)
  }
}

object ProgramEncoder {
  def empty(p: Program): ProgramEncoder {
    val sourceProgram: p.type
    val t: p.trees.type
  } = new ProgramEncoder {
    val sourceProgram: p.type = p
    val t: p.trees.type = p.trees

    protected object encoder extends p.trees.IdentityTreeTransformer
    protected object decoder extends p.trees.IdentityTreeTransformer
  }

  def apply(p: Program)(tr: SymbolTransformer { val s: p.trees.type; val t: p.trees.type }): ProgramEncoder {
    val sourceProgram: p.type
    val t: p.trees.type
  } = new ProgramEncoder {
    val sourceProgram: p.type = p
    val t: p.trees.type = p.trees

    override protected def encodedProgram: Program { val trees: p.trees.type } = p.transform(tr)

    protected object encoder extends p.trees.IdentityTreeTransformer
    protected object decoder extends p.trees.IdentityTreeTransformer
  }
}

