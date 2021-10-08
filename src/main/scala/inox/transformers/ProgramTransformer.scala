/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package transformers

trait ProgramTransformer { self =>
  val sourceProgram: Program
  val targetProgram: Program

  protected val encoder: transformers.TreeTransformer {
    val s: self.sourceProgram.trees.type
    val t: self.targetProgram.trees.type
  }

  protected val decoder: transformers.TreeTransformer {
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
  } = {
    val enc = self.encoder compose that.encoder
    val dec = that.decoder compose self.decoder
    class ComposeImpl(override val sourceProgram: that.sourceProgram.type,
                      override val targetProgram: self.targetProgram.type,
                      override val encoder: enc.type,
                      override val decoder: dec.type) extends ProgramTransformer

    new ComposeImpl(that.sourceProgram, self.targetProgram, enc, dec)
  }

  def andThen(that: ProgramTransformer { val sourceProgram: self.targetProgram.type }): ProgramTransformer {
    val sourceProgram: self.sourceProgram.type
    val targetProgram: that.targetProgram.type
  } = {
    val enc = self.encoder andThen that.encoder
    val dec = that.decoder andThen self.decoder
    class AndThenImpl(override val sourceProgram: self.sourceProgram.type,
                      override val targetProgram: that.targetProgram.type,
                      override val encoder: enc.type,
                      override val decoder: dec.type) extends ProgramTransformer

    new AndThenImpl(self.sourceProgram, that.targetProgram, enc, dec)
  }

  def reverse: ProgramTransformer {
    val sourceProgram: self.targetProgram.type
    val targetProgram: self.sourceProgram.type
  } = {
    class ReverseImpl(override val sourceProgram: self.targetProgram.type,
                      override val targetProgram: self.sourceProgram.type,
                      override val encoder: self.decoder.type,
                      override val decoder: self.encoder.type) extends ProgramTransformer

    new ReverseImpl(self.targetProgram, self.sourceProgram, self.decoder, self.encoder)
  }
}

abstract class ProgramEncoder private(val t: ast.Trees)
                                     (override val sourceProgram: Program,
                                      override val targetProgram: Program { val trees: t.type })
                                     (override protected val encoder: transformers.TreeTransformer {
                                        val s: sourceProgram.trees.type
                                        val t: targetProgram.trees.type
                                      },
                                      override protected val decoder: transformers.TreeTransformer {
                                        val s: targetProgram.trees.type
                                        val t: sourceProgram.trees.type
                                      })
  extends ProgramTransformer { self =>
  final val s: sourceProgram.trees.type = sourceProgram.trees

  def this(tt: ast.Trees,
           sourceProgram: Program,
           encoder: transformers.TreeTransformer {
             val s: sourceProgram.trees.type
             val t: tt.type
           },
           decoder: transformers.TreeTransformer {
             val s: tt.type
             val t: sourceProgram.trees.type
           })
          (encodedProgram: Program { val trees: tt.type } = sourceProgram.transform(SymbolTransformer(encoder)),
           extraFunctions: Seq[tt.FunDef] = Seq.empty,
           extraSorts: Seq[tt.ADTSort] = Seq.empty) =
    this(tt)(
      sourceProgram,
      // Note that targetProgram will always be equal to this expression.
      // The only parts that can be customized are encodedProgram, extraFunctions and extraSorts,
      // which all have reasonable default values.
      encodedProgram.withFunctions(extraFunctions).withSorts(extraSorts)
    )(encoder, decoder)
}

object ProgramEncoder {
  def empty(p: Program): ProgramEncoder {
    val sourceProgram: p.type
    val t: p.trees.type
  } = {
    val identity = new p.trees.ConcreteIdentityTreeTransformer
    class EmptyImpl(override val t: p.trees.type, override val sourceProgram: p.type)
      extends ProgramEncoder(t, sourceProgram, identity, identity)()

    new EmptyImpl(p.trees, p)
  }

  def apply(p: Program)(tr: SymbolTransformer { val s: p.trees.type; val t: p.trees.type }): ProgramEncoder {
    val sourceProgram: p.type
    val t: p.trees.type
    val targetProgram: Program { val trees: p.trees.type }
  } = {
    val identity = new p.trees.ConcreteIdentityTreeTransformer
    class Impl(override val t: p.trees.type, override val sourceProgram: p.type)
      extends ProgramEncoder(t, sourceProgram, identity, identity)(p.transform(tr))

    new Impl(p.trees, p)
  }
}

