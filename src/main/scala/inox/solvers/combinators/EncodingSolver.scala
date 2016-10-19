/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package combinators

import ast._

trait ProgramEncoder extends TreeBijection {
  val sourceProgram: Program
  lazy val s: sourceProgram.trees.type = sourceProgram.trees
  lazy val targetProgram: Program { val trees: t.type } = sourceProgram.transform(encoder)

  /* @nv XXX: ideally, we would want to replace `>>` by `override def andThen`, however this
   *          seems to break the scala compiler for some weird reason... */
  def >>(that: TreeBijection { val s: ProgramEncoder.this.t.type }): ProgramEncoder {
    val sourceProgram: ProgramEncoder.this.sourceProgram.type
    val t: that.t.type
  } = new ProgramEncoder {
    val sourceProgram: ProgramEncoder.this.sourceProgram.type = ProgramEncoder.this.sourceProgram
    val t: that.t.type = that.t

    val encoder = ProgramEncoder.this.encoder andThen that.encoder
    val decoder = that.decoder andThen ProgramEncoder.this.decoder
  }
}

object ProgramEncoder {
  def empty(p: Program): ProgramEncoder {
    val sourceProgram: p.type
    val t: p.trees.type
  } = new ProgramEncoder {
    val sourceProgram: p.type = p
    val t: p.trees.type = p.trees

    object encoder extends p.trees.IdentitySymbolTransformer
    object decoder extends p.trees.IdentitySymbolTransformer
  }
}

trait EncodingSolver extends Solver {
  import program.trees._

  protected val programEncoder: ProgramEncoder { val sourceProgram: program.type }

  protected def encode(vd: ValDef): programEncoder.t.ValDef = programEncoder.encode(vd)
  protected def decode(vd: programEncoder.t.ValDef): ValDef = programEncoder.decode(vd)

  protected def encode(v: Variable): programEncoder.t.Variable = programEncoder.encode(v)
  protected def decode(v: programEncoder.t.Variable): Variable = programEncoder.decode(v)

  protected def encode(e: Expr): programEncoder.t.Expr = programEncoder.encode(e)
  protected def decode(e: programEncoder.t.Expr): Expr = programEncoder.decode(e)

  protected def encode(tpe: Type): programEncoder.t.Type = programEncoder.encode(tpe)
  protected def decode(tpe: programEncoder.t.Type): Type = programEncoder.decode(tpe)
}
