package inox
package parser
package irs

trait Exprs { self: IRs =>

  object Exprs {
    sealed trait Expr extends IR {
      override def getHoles: Seq[Hole] = ???
    }

    type ExprSeq = HSeq[Expr]
  }
}