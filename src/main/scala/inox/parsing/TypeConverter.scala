/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

trait TypeConverters extends TypeElaborators with TypeExtractors { self: Interpolator => 

  trait TypeConverter extends TypeElaborator with TypeExtractor { self: Elaborator => }
}
