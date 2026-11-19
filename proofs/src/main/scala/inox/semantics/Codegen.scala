/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package semantics

import java.nio.file.{Files, Path}

/** Generates the embeddings of the semantics file:
  * `Codegen [<semantics.md> [<scala-output>]]`, from the `proofs` directory by default. */
object Codegen {
  val source = "semantics.md"
  val scalaOutput = "src/test/scala/inox/semantics/generated/Semantics.scala"
  val scalaPackage = "inox.semantics.generated"

  /** The generated Scala source of the semantics file at `path`. */
  def scala(path: Path): String = ScalaBackend(Spec.parse(Files.readString(path)), source, scalaPackage)

  def main(args: Array[String]): Unit = {
    val in = Path.of(args.lift(0).getOrElse(source))
    val out = Path.of(args.lift(1).getOrElse(scalaOutput))
    Files.createDirectories(out.getParent)
    Files.writeString(out, scala(in))
    println(s"Wrote $out")
  }
}
