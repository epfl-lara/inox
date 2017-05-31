/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

trait ExpressionConvertors extends ExpressionElaborators 
                              with ExpressionExtractors
                              with ExpressionDeconstructors { self: Interpolator =>

  class ExpressionConvertor(symbols: trees.Symbols) extends TypeConvertor()(symbols)
                                                       with ExpressionElaborator
                                                       with ExpressionExtractor
                                                       with ExpressionDeconstructor {

  }
}