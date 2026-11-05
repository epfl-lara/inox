/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package utils

import java.io.{File, FileOutputStream}

/** Writes each problem of the given TIP files in Inox's binary format, as
  * `<out>/<file>-<index>.inoxb`. The goal becomes the body of a function
  * named `goal` (its free variables become parameters), so that
  * `inox --format=binary:goal` solves it.
  *
  * scripts/record-native-image-metadata.sh uses these files to exercise the
  * binary deserializer.
  *
  * Usage: Test/runMain inox.utils.WriteBinaryInputs <out> <file.tip>...
  */
object WriteBinaryInputs {
  import inox.trees._

  def main(args: Array[String]): Unit = {
    val out = new File(args(0))
    out.mkdirs()
    for (path <- args.toSeq.drop(1)) {
      val file = new File(path)
      for (((program, expr), i) <- tip.Parser(file).parseScript.zipWithIndex) {
        val params = exprOps.variablesOf(expr).toSeq.sortBy(_.id).map(_.toVal)
        val goal = new FunDef(FreshIdentifier("goal"), Seq(), params, BooleanType(), expr, Seq())
        val symbols = program.symbols.withFunctions(Seq(goal))
        val serializer = Serializer(inox.trees)
        import serializer.{given, _}
        val os = new FileOutputStream(new File(out, s"${file.getName}-$i.inoxb"))
        try serializer.serialize(symbols, os) finally os.close()
      }
    }
  }
}
