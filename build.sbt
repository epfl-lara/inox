name := "inox"

enablePlugins(GitVersioning)

git.useGitDescribe := true

organization := "ch.epfl.lara"

val inoxScalaVersion = "3.9.0"
val laraOrganization = "ch.epfl.lara"

scalaVersion := inoxScalaVersion

scalacOptions ++= Seq(
  "-deprecation",
  "-unchecked",
  "-feature"
)

// Inox runs on Java 21 and later, whatever the JDK it is built with.
scalacOptions ++= Seq("-release", "21")
javacOptions ++= Seq("--release", "21")

// The native Z3 interface: ScalaZ3 (https://github.com/epfl-lara/ScalaZ3), which bundles the Z3
// Java bindings and the native libraries of Z3 for all supported platforms. It is versioned after
// the Z3 release it wraps.
val z3Version = "5.4.1"

resolvers ++= Seq(
  "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots",
  "Sonatype OSS Releases" at "https://oss.sonatype.org/content/repositories/releases",
  "uuverifiers" at "https://eldarica.org/maven"
)

// 2.13 dependencies coming from Eldarica and Princess that we also use as their
// Scala 3 versions, causing conflicts; they are expected to be binary
// compatible and we simply pick the Scala 3 versions
val doubleDependencies = Seq(
  "org.scala-lang.modules" % "scala-parser-combinators_2.13",
  "org.scala-lang.modules" % "scala-xml_2.13",
  "org.scalactic" % "scalactic_2.13",
).map(artifact => artifact: ExclusionRule) // invoke the implicit conversion

libraryDependencies ++= Seq(
  "org.scalatest" %% "scalatest" % "3.2.9" % "test;it",
  "org.apache.commons" % "commons-lang3" % "3.4",
  "ch.epfl.lara" %% "scalaz3" % z3Version,
  // Scala-SMTLIB (https://github.com/epfl-lara/scala-smtlib). To try local changes to it, run
  // `sbt publishLocal` in its repository, and use the version it prints here.
  "ch.epfl.lara" %% "scala-smtlib" % "0.2.5",
  ("uuverifiers" %% "eldarica" % "2.2")
    .cross(CrossVersion.for3Use2_13)
    .excludeAll(doubleDependencies: _*),
  ("uuverifiers" %% "princess" % "2025-04-01")
    .cross(CrossVersion.for3Use2_13)
    .excludeAll(doubleDependencies: _*),
  "org.scala-lang.modules" %% "scala-parser-combinators" % "2.3.0"
)

lazy val nTestParallelism = {
  val p = System.getProperty("test-parallelism")
  if (p ne null) {
    try {
      p.toInt
    } catch {
      case nfe: NumberFormatException => 1
    }
  } else {
    1
  }
}


lazy val scriptName = settingKey[String]("Name of the generated 'inox' script")

scriptName := "inox"

lazy val scriptFile = taskKey[File]("Location of the generated 'inox' script (computed from 'scriptName')")

scriptFile := file(".") / scriptName.value

clean := {
  clean.value
  val file = scriptFile.value
  if (file.exists && file.isFile) file.delete
}

lazy val script = taskKey[Unit]("Generate the inox Bash script")

script := {
  val s = streams.value
  val file = scriptFile.value
  try {
    val cps = (Compile / dependencyClasspath).value
    val out = (Compile / classDirectory).value
    val res = (Compile / resourceDirectory).value

    if (file.exists) {
      s.log.info("Regenerating '" + file.getName + "' script")
      file.delete
    } else {
      s.log.info("Generating '" + file.getName + "' script")
    }

    val paths = res.getAbsolutePath +: out.getAbsolutePath +: cps.map(_.data.absolutePath)
    val cp = paths.mkString(System.getProperty("path.separator"))
    IO.write(file, s"""|#!/usr/bin/env bash
                       |set -o posix
                       |
                       |SCALACLASSPATH=$cp
                       |
                       |java -Xmx2G -Xms512M -Xss64M -classpath "$${SCALACLASSPATH}" -Dscala.usejavacp=true inox.Main "$$@" 2>&1
                       |""".stripMargin)
    file.setExecutable(true)
  } catch {
    case e: Throwable =>
      s.log.error("There was an error while generating the script file: " + e.getLocalizedMessage)
  }
}

Compile / sourceGenerators += Def.task {
  val file = (Compile / sourceManaged).value / "inox" / "Build.scala"
  IO.write(file, s"""|package inox
                     |
                     |object Build {
                     |  val version = \"\"\"${version.value}\"\"\"
                     |}""".stripMargin)
  Seq(file)
}.taskValue

lazy val docs = project
  .in(file("inox-docs"))
  .dependsOn(root)
  .settings(
    mdocIn  := file("src/main/doc"),
    mdocOut := file("doc"),
    mdocExtraArguments := Seq("--no-link-hygiene"),
    scalaVersion := inoxScalaVersion,
  )
  .enablePlugins(MdocPlugin)

/** The proofs of Inox's answers, in `proofs`: `semantics.md`, the definition of Inox's semantics,
 *  and the generator of its embeddings, `sbt proofs/run`. Its tests compare the generated Scala
 *  evaluator with Inox's. It is a build-time tool, so it is not published; `sbt test` runs its
 *  tests along with Inox's.
 */
lazy val proofs = project
  .in(file("proofs"))
  .dependsOn(root % "compile->compile;test->test")
  .settings(
    scalaVersion := inoxScalaVersion,
    scalacOptions ++= Seq("-deprecation", "-unchecked", "-feature"),
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.9" % "test",
    // Paths are relative to `proofs`. Both evaluators recurse deeply.
    fork := true,
    javaOptions += "-Xss64M",
    // `-Dfuzz-count=N -Dfuzz-seed=S` set the expressions that the fuzzing test generates
    javaOptions ++= sys.props.toSeq.collect { case (k, v) if k.startsWith("fuzz-") => s"-D$k=$v" },
    Compile / run / mainClass := Some("inox.semantics.Codegen"),
    publish / skip := true,
  )

run / Keys.fork := true

Test / testOptions := Seq(Tests.Argument("-oDF"))

/** The configuration of the integration tests, in `src/it`. It replaces the one of sbt, which is deprecated
 *  (sbt recommends a separate subproject instead), with the same name and id, so that `it:test` and
 *  `IntegrationTest/test` run the tests. It cannot be called `IntegrationTest` itself, as the settings below
 *  would then refer to it ambiguously.
 */
lazy val ItTest = Configuration.of("IntegrationTest", "it") extend (Test)

ItTest / testOptions := Seq(Tests.Argument("-oDF"))

lazy val root = (project in file("."))
  .settings(
    // The serialization macro only runs at compile time, so tests can never cover it.
    coverageExcludedFiles := ".*SerializationMacro.*",
  )
  .configs(ItTest)
  .settings(inConfig(ItTest)(Defaults.testSettings) : _*)
  .settings(inConfig(Test)(Defaults.testTasks ++ Seq(
    logBuffered := (nTestParallelism > 1),
    parallelExecution := (nTestParallelism > 1)
  )) : _*)
  .settings(inConfig(ItTest)(Defaults.testTasks ++ Seq(
    logBuffered := (nTestParallelism > 1),
    parallelExecution := (nTestParallelism > 1)
  )) : _*)
  .settings(compile := ((Compile / compile) dependsOn script).value)
  .settings(Compile / packageDoc / mappings := Seq())
  .settings(
    // The tests of `proofs` run with Inox's. (Aggregating it would also assemble and publish it.)
    Test / test := (Test / test).dependsOn(LocalProject("proofs") / Test / test).value,
  )

Global / concurrentRestrictions := Seq(
  Tags.limit(Tags.Test, nTestParallelism)
)

Compile / run / mainClass := Some("inox.Main")

publishMavenStyle := true

assembly / test := {} // Skip the test during assembly

publishTo := {
  val nexus = "https://oss.sonatype.org/"
  // @nv: we can't use `isSnapshot` here as it is not compatible with sbt-git versioning
  if (version.value.trim.endsWith("SNAPSHOT")) Some("snapshots" at nexus + "content/repositories/snapshots")
  else                                         Some("releases"  at nexus + "service/local/staging/deploy/maven2")
}

Test / packageBin / publishArtifact := true

addArtifact(ItTest / packageBin / artifact, ItTest / packageBin)

pomIncludeRepository := { _ => false }

licenses := Seq("Apache License 2.0" -> url("https://www.apache.org/licenses/LICENSE-2.0"))

homepage := Some(url("https://github.com/epfl-lara/inox"))

pomExtra := (
  <developers>
    <developer>
      <id>epfl-lara</id>
      <name>EPFL Lab for Automated Reasoning and Analysis</name>
      <url>http://lara.epfl.ch</url>
    </developer>
    <developer>
      <id>samarion</id>
      <name>Nicolas Voirol</name>
      <url>https://github.com/samarion</url>
    </developer>
  </developers>)
