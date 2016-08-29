/* Copyright 2009-2015 EPFL, Lausanne */

package inox
package solvers
package theories

import utils._

trait TheoryEncoder {
  val sourceProgram: Program
  lazy val trees: sourceProgram.trees.type = sourceProgram.trees
  lazy val targetProgram: Program { val trees: TheoryEncoder.this.trees.type } = {
    sourceProgram.transform(encoder).withFunctions(newFunctions).withADTs(newADTs)
  }

  import trees._

  protected val encoder: TreeTransformer
  protected val decoder: TreeTransformer

  val newFunctions: Seq[FunDef] = Seq.empty
  val newADTs: Seq[ADTDefinition] = Seq.empty

  def encode(v: Variable): Variable = encoder.transform(v)
  def decode(v: Variable): Variable = decoder.transform(v)

  def encode(expr: Expr): Expr = encoder.transform(expr)
  def decode(expr: Expr): Expr = decoder.transform(expr)

  def encode(tpe: Type): Type = encoder.transform(tpe)
  def decode(tpe: Type): Type = decoder.transform(tpe)

  def >>(that: TheoryEncoder { val sourceProgram: TheoryEncoder.this.targetProgram.type }): TheoryEncoder {
    val sourceProgram: TheoryEncoder.this.sourceProgram.type
  } = new TheoryEncoder {
    val sourceProgram: TheoryEncoder.this.sourceProgram.type = TheoryEncoder.this.sourceProgram

    val encoder = new TreeTransformer {
      override def transform(id: Identifier, tpe: Type): (Identifier, Type) = {
        val (id1, tpe1) = TheoryEncoder.this.encoder.transform(id, tpe)
        that.encoder.transform(id1, tpe1)
      }

      override def transform(expr: Expr): Expr =
        that.encoder.transform(TheoryEncoder.this.encoder.transform(expr))

      override def transform(tpe: Type): Type =
        that.encoder.transform(TheoryEncoder.this.encoder.transform(tpe))
    }

    val decoder = new TreeTransformer {
      override def transform(id: Identifier, tpe: Type): (Identifier, Type) = {
        val (id1, tpe1) = that.decoder.transform(id, tpe)
        TheoryEncoder.this.decoder.transform(id1, tpe1)
      }

      override def transform(expr: Expr): Expr =
        TheoryEncoder.this.decoder.transform(that.decoder.transform(expr))

      override def transform(tpe: Type): Type =
        TheoryEncoder.this.decoder.transform(that.decoder.transform(tpe))
    }
  }
}

trait NoEncoder extends TheoryEncoder {
  import trees._

  private object NoTransformer extends TreeTransformer {
    override def transform(id: Identifier, tpe: Type): (Identifier, Type) = (id, tpe)
    override def transform(v: Variable): Variable = v
    override def transform(vd: ValDef): ValDef = vd
    override def transform(expr: Expr): Expr = expr
    override def transform(tpe: Type): Type = tpe
  }

  val encoder: TreeTransformer = NoTransformer
  val decoder: TreeTransformer = NoTransformer
}

