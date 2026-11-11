// Scala Native build of the Inox command line.
//
// Compiles the JVM sources in ../src/main/scala together with Scala-SMTLIB,
// leaving out the solver back ends that need JVM-only libraries (Princess,
// Eldarica, the Z3 JNI bindings, registered in solvers/PlatformSolvers.scala)
// and the reflective binary serializer. native/src/main/scala holds their
// native replacements and stand-ins for two JDK/Java library classes.
//
//   cd native && sbt nativeLink   # produces target/scala-*/inox-native

import scala.scalanative.build._

name := "inox-native"
scalaVersion := "3.10.0"
enablePlugins(ScalaNativePlugin)

scalacOptions ++= Seq("-deprecation", "-feature")

val smtlibRepo = "https://github.com/epfl-lara/scala-smtlib.git"
val smtlibCommit = "139c1986a27d635e0bc82328e06d2eb7dac8cb0b"

lazy val smtlibSources = taskKey[File]("checkout of Scala-SMTLIB at the commit Inox uses")
smtlibSources := {
  val dir = target.value / "scala-smtlib"
  if (!(dir / ".git").exists) {
    IO.delete(dir)
    scala.sys.process.Process(Seq("git", "clone", "-q", smtlibRepo, dir.getAbsolutePath)).!
  }
  scala.sys.process.Process(Seq("git", "-C", dir.getAbsolutePath, "checkout", "-q", smtlibCommit)).!
  dir / "src" / "main" / "scala"
}

// files replaced by an overlay in native/src/main/scala, or depending on JVM-only libraries
val excluded = Set(
  "solvers/princess", "solvers/z3", "solvers/smtlib/EldaricaSolver.scala",
  "solvers/smtlib/EldaricaInterpreter.scala", "solvers/PlatformSolvers.scala",
  "utils/Serialization.scala", "utils/SerializationMacro.scala",
)

Compile / unmanagedSourceDirectories := Seq((Compile / scalaSource).value)
Compile / sourceGenerators += Def.task {
  val inox = (baseDirectory.value / ".." / "src" / "main" / "scala").getCanonicalFile
  val inoxFiles = (inox ** "*.scala").get.filterNot { f =>
    val rel = IO.relativize(inox / "inox", f).getOrElse("")
    excluded.exists(rel.startsWith)
  }
  val smtlib = smtlibSources.value
  inoxFiles ++ (smtlib ** "*.scala").get
}.taskValue

Compile / sourceGenerators += Def.task {
  val file = (Compile / sourceManaged).value / "inox" / "Build.scala"
  IO.write(file, "package inox\n\nobject Build {\n  val version = \"native-SNAPSHOT\"\n}\n")
  Seq(file)
}.taskValue

libraryDependencies += "org.scala-lang.modules" %%% "scala-parser-combinators" % "2.4.0"

nativeConfig ~= {
  _.withMode(Mode.releaseFast)
    .withGC(GC.immix)
    .withMultithreading(true)
}
Compile / mainClass := Some("inox.Main")
