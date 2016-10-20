/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

trait ProgramEncoder { self =>
  val sourceProgram: Program
  val t: Trees

  protected val extraFunctions: Seq[t.FunDef] = Seq.empty
  protected val extraADTs: Seq[t.ADTDefinition] = Seq.empty

  /** Override point for more complex program transformations */
  protected def encodedProgram: Program { val trees: t.type } = {
    sourceProgram.transform(SymbolTransformer(encoder))
  }

  lazy final val s: sourceProgram.trees.type = sourceProgram.trees
  lazy final val targetProgram: Program { val trees: t.type } = {
    encodedProgram.withFunctions(extraFunctions).withADTs(extraADTs)
  }

  protected val encoder: TreeTransformer { val s: self.s.type; val t: self.t.type }
  protected val decoder: TreeTransformer { val s: self.t.type; val t: self.s.type }

  def encode(vd: s.ValDef): t.ValDef = encoder.transform(vd)
  def decode(vd: t.ValDef): s.ValDef = decoder.transform(vd)

  def encode(v: s.Variable): t.Variable = encoder.transform(v).asInstanceOf[t.Variable]
  def decode(v: t.Variable): s.Variable = decoder.transform(v).asInstanceOf[s.Variable]

  def encode(e: s.Expr): t.Expr = encoder.transform(e)
  def decode(e: t.Expr): s.Expr = decoder.transform(e)

  def encode(tpe: s.Type): t.Type = encoder.transform(tpe)
  def decode(tpe: t.Type): s.Type = decoder.transform(tpe)

  def compose(that: ProgramEncoder { val t: self.s.type }): ProgramEncoder {
    val sourceProgram: that.sourceProgram.type
    val t: self.t.type
  } = new ProgramEncoder {
    val sourceProgram: that.sourceProgram.type = that.sourceProgram
    val t: self.t.type = self.t

    val encoder = self.encoder compose that.encoder
    val decoder = that.decoder compose self.decoder
  }

  def andThen(that: ProgramEncoder { val sourceProgram: self.targetProgram.type }): ProgramEncoder {
    val sourceProgram: self.sourceProgram.type
    val t: that.t.type
  } = new ProgramEncoder {
    val sourceProgram: self.sourceProgram.type = self.sourceProgram
    val t: that.t.type = that.t

    val encoder = self.encoder andThen that.encoder
    val decoder = that.decoder andThen self.decoder
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
}

