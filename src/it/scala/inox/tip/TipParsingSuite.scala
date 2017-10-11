/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package tip

class TipParsingSuite extends TestSuite with ResourceUtils {
  for (file <- resourceFiles("regression/tip/PARSING", _.endsWith(".tip"))) {
    test(s"PARSING - ${file.getName}") { ctx =>
      new Parser(file).parseScript
    }
  }
}

