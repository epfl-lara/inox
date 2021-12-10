name := "inox"

enablePlugins(GitVersioning, MdocPlugin)

git.useGitDescribe := true

organization := "ch.epfl.lara"

scalaVersion := "2.13.6"

scalacOptions ++= Seq(
  "-deprecation",
  "-unchecked",
  "-feature"
)

val osInf = Option(System.getProperty("os.name")).getOrElse("")

val isUnix    = osInf.indexOf("nix") >= 0 || osInf.indexOf("nux") >= 0
val isWindows = osInf.indexOf("Win") >= 0
val isMac     = osInf.indexOf("Mac") >= 0

val osName = if (isWindows) "win" else if (isMac) "mac" else "unix"

val osArch = System.getProperty("sun.arch.data.model")

Compile / unmanagedJars += {
  baseDirectory.value / "unmanaged" / s"scalaz3-$osName-$osArch-${scalaBinaryVersion.value}.jar"
}

resolvers ++= Seq(
  "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots",
  "Sonatype OSS Releases" at "https://oss.sonatype.org/content/repositories/releases",
  ("uuverifiers" at "http://logicrunch.research.it.uu.se/maven").withAllowInsecureProtocol(true)
)

libraryDependencies ++= Seq(
  "org.scalatest" %% "scalatest" % "3.2.7" % "test;it",
  "org.apache.commons" % "commons-lang3" % "3.4",
  "org.scala-lang" % "scala-reflect" % scalaVersion.value,
  "uuverifiers" %% "princess" % "2020-03-12",
  "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2"
)

def ghProject(repo: String, version: String) = RootProject(uri(s"${repo}#${version}"))

lazy val smtlib = ghProject("https://github.com/epfl-lara/scala-smtlib.git", "ffb61e571aeb37b741d4bba47f8e56f88d7285b5")

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

lazy val genDoc = taskKey[Unit]("Typecheck and interpret the documentation")

mdocIn  := sourceDirectory.value / "main" / "doc"
mdocOut := baseDirectory.value / "doc"
mdocExtraArguments := Seq("--no-link-hygiene")

genDoc := { () }
genDoc := (genDoc dependsOn (Compile / compile)).value

run / Keys.fork := true

Test / testOptions := Seq(Tests.Argument("-oDF"))

// Note that we can't use IntegrationTest because it is already defined in sbt._
lazy val ItTest = config("it") extend (Test)

ItTest / testOptions := Seq(Tests.Argument("-oDF"))

lazy val root = (project in file("."))
  .configs(ItTest)
  .settings(Defaults.itSettings : _*)
  .settings(inConfig(ItTest)(Defaults.testTasks ++ Seq(
    logBuffered := false,
    parallelExecution := false
  )) : _*)
  .settings(compile := ((Compile / compile) dependsOn script dependsOn genDoc).value)
  .dependsOn(smtlib)


Compile / run / mainClass := Some("inox.Main")

publishMavenStyle := true

publishTo := {
  val nexus = "https://oss.sonatype.org/"
  // @nv: we can't use `isSnapshot` here as it is not compatible with sbt-git versioning
  if (version.value.trim.endsWith("SNAPSHOT")) Some("snapshots" at nexus + "content/repositories/snapshots")
  else                                         Some("releases"  at nexus + "service/local/staging/deploy/maven2")
}

Test / packageBin / publishArtifact := true

ItTest / packageBin / publishArtifact := true

addArtifact(ItTest / packageBin / artifact, ItTest / packageBin)

pomIncludeRepository := { _ => false }

licenses := Seq("GNU Affero General Public License, Version 3" -> url("http://www.gnu.org/licenses/agpl-3.0.html"))

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
