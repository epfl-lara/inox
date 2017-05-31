/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

trait TypeConvertors extends TypeElaborators with TypeExtractors { self: Interpolator => 

  class TypeConvertor(implicit val symbols: trees.Symbols) extends TypeElaborator with TypeExtractor {

  }
}