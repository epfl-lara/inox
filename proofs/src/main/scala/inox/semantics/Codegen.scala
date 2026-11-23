/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package semantics

import java.nio.file.{Files, Path}

/** Generates the embeddings of a semantics file:
  * `Codegen [<semantics.md> [<scala-output> [<package>]]]`, from the `proofs` directory by default.
  * A file that extends Inox's semantics, such as Stainless's, imports it and is generated the same
  * way, with its own output and package. */
object Codegen {
  val source = "semantics.md"
  val scalaOutput = "src/test/scala/inox/semantics/generated/Semantics.scala"
  val scalaPackage = "inox.semantics.generated"

  /** The generated Scala source of the semantics file at `path`. */
  def scala(path: Path, pkg: String = scalaPackage): String =
    ScalaBackend(Spec.load(path), path.getFileName.toString, pkg)

  def main(args: Array[String]): Unit = {
    val in = Path.of(args.lift(0).getOrElse(source))
    val out = Path.of(args.lift(1).getOrElse(scalaOutput))
    Files.createDirectories(out.getParent)
    Files.writeString(out, scala(in, args.lift(2).getOrElse(scalaPackage)))
    println(s"Wrote $out")
  }
}
