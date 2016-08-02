/* Copyright 2009-2015 EPFL, Lausanne */

package inox
package solvers
package theories

import utils._

trait TheoryEncoder {
  val trees: Trees
  import trees._

  private type SameTrees = TheoryEncoder {
    val trees: TheoryEncoder.this.trees.type
  }

  protected val encoder: TreeTransformer
  protected val decoder: TreeTransformer

  def encode(v: Variable): Variable = encoder.transform(v)
  def decode(v: Variable): Variable = decoder.transform(v)

  def encode(expr: Expr): Expr = encoder.transform(expr)
  def decode(expr: Expr): Expr = decoder.transform(expr)

  def encode(tpe: Type): Type = encoder.transform(tpe)
  def decode(tpe: Type): Type = decoder.transform(tpe)

  def >>(that: SameTrees): SameTrees = new TheoryEncoder {
    val trees: TheoryEncoder.this.trees.type = TheoryEncoder.this.trees

    val encoder = new TreeTransformer {
      override def transform(id: Identifier, tpe: Type): (Identifier, Type) = {
        val (id1, tpe1) = TheoryEncoder.this.transform(id, tpe)
        that.transform(id1, tpe1)
      }

      override def transform(expr: Expr): Expr = that.transform(TheoryEncoder.this.transform(expr))
      override def transform(tpe: Type): Type = that.transform(TheoryEncoder.this.transform(expr))
    }

    val decoder = new TreeTransformer {
      override def transform(id: Identifier, tpe: Type): (Identifier, Type) = {
        val (id1, tpe1) = that.transform(id, tpe)
        TheoryEncoder.this.transform(id1, tpe1)
      }

      override def transform(expr: Expr): Expr = TheoryEncoder.this.transform(that.transform(expr))
      override def transform(tpe: Type): Type = TheoryEncoder.this.transform(that.transform(tpe))
    }
  }
}

trait NoEncoder extends TheoryEncoder {

  private object NoTransformer extends trees.TreeTransformer {
    override def transform(id: Identifier, tpe: Type): (Identifier, Type) = (id, tpe)
    override def transform(v: Variable): Variable = v
    override def transform(vd: ValDef): ValDef = vd
    override def transform(expr: Expr): Expr = expr
    override def transform(tpe: Type): Type = tpe
  }

  val encoder = NoTransformer
  val decoder = NoTransformer
}

