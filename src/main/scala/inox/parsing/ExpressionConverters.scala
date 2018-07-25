/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

trait ExpressionConverters extends ExpressionElaborators 
                              with ExpressionExtractors
                              with ExpressionDeconstructors { self: Interpolator =>

  trait ExpressionConverter extends TypeConverter
                               with ExpressionElaborator
                               with ExpressionExtractor
                               with ExpressionDeconstructor { self: Elaborator => }
}
