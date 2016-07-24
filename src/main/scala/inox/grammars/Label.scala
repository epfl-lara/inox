/* Copyright 2009-2015 EPFL, Lausanne */

package inox
package grammars

import ast.Trees

trait Labels { self: GrammarsUniverse =>
  import program.{printerOpts => _, _}
  import trees._

  case class Label(tpe: Type, aspects: List[Aspect] = Nil) extends Typed {
    def getType(implicit s: Symbols) = tpe

    def asString(implicit opts: PrinterOptions): String = {
      val ts = tpe.asString

      ts + aspects.map(_.asString).mkString
    }

    def withAspect(a: Aspect) = Label(tpe, aspects :+ a)
  }
}
