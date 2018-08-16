package inox
package parser
package irs

trait Programs { self: IRs =>

  import ADTs._
  import Functions._

  object Programs {
    case class Program(defs: Seq[Either[Sort, Function]]) extends IR {
      override def getHoles =
        defs.flatMap {
          case Left(s) => s.getHoles
          case Right(f) => f.getHoles
        }
    }
  }
}