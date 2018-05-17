name := "inox"

enablePlugins(GitVersioning)

git.useGitDescribe := true

organization := "ch.epfl.lara"

val scalacVersion = "2.12.4"
val dottyVersion = "0.8.0-bin-SNAPSHOT"
// scalaVersion := scalacVersion
scalaVersion := dottyVersion
// crossScalaVersions := Seq("2.11.8", "2.12.1")
// crossScalaVersions := Seq(scalacVersion, dottyVersion)

scalacOptions ++= Seq(
  "-deprecation",
  "-unchecked",
  "-feature",
  "-language:Scala2"
  // "-nowarn"
)

val osInf = Option(System.getProperty("os.name")).getOrElse("")

val isUnix    = osInf.indexOf("nix") >= 0 || osInf.indexOf("nux") >= 0
val isWindows = osInf.indexOf("Win") >= 0
val isMac     = osInf.indexOf("Mac") >= 0

val osName = if (isWindows) "win" else if (isMac) "mac" else "unix"

val osArch = System.getProperty("sun.arch.data.model")

/* ... snip */

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
    val cps = (dependencyClasspath in Compile).value
    val out = (classDirectory      in Compile).value
    val res = (resourceDirectory   in Compile).value

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
                       |java -Xmx2G -Xms512M -Xss64M -classpath "$${SCALACLASSPATH}" -Dscala.usejavacp=true inox.Main $$@ 2>&1
                       |""".stripMargin)
    file.setExecutable(true)
  } catch {
    case e: Throwable =>
      s.log.error("There was an error while generating the script file: " + e.getLocalizedMessage)
  }
}

sourceGenerators in Compile += Def.task {
  val file = (sourceManaged in Compile).value / "inox" / "Build.scala"
  IO.write(file, s"""|package inox
                     |
                     |object Build {
                     |  val version = \"\"\"${version.value}\"\"\"
                     |}""".stripMargin)
  Seq(file)
}.taskValue

// lazy val genDoc = taskKey[Unit]("Typecheck and interpret the documentation")
// 
// enablePlugins(TutPlugin)
// 
// tutSourceDirectory := sourceDirectory.value / "main" / "doc"
// tutTargetDirectory := baseDirectory.value / "doc"

// genDoc := (tut dependsOn (compile in Compile)).value

Keys.fork in run := true

testOptions in Test := Seq(Tests.Argument("-oDF"))

// Note that we can't use IntegrationTest because it is already defined in sbt._
lazy val ItTest = config("it") extend (Test)

testOptions in ItTest := Seq(Tests.Argument("-oDF"))

lazy val root = (project in file("."))
  // .settings((scalaVersion in Compile) := dottyVersion)
  // .settings(scalaModuleInfo ~= (_.map(_.withOverrideScalaVersion(false))))
  .settings(
    scalaVersion := scalacVersion,

    unmanagedJars in Compile += {
      // baseDirectory.value / "unmanaged" / s"scalaz3-$osName-$osArch-${scalaBinaryVersion.value}.jar"
      baseDirectory.value / "unmanaged" / s"scalaz3-$osName-$osArch-2.12.jar"
    },

    resolvers ++= Seq(
      "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots",
      "Sonatype OSS Releases" at "https://oss.sonatype.org/content/repositories/releases",
      "uuverifiers" at "http://logicrunch.it.uu.se:4096/~wv/maven"
    ),

    libraryDependencies ++= Seq(
      ("org.scalatest" %% "scalatest" % "3.0.1" % "test;it").withDottyCompat(scalaVersion.value),
      ("org.apache.commons" % "commons-lang3" % "3.4").withDottyCompat(scalaVersion.value),
      ("org.scala-lang" % "scala-reflect" % scalacVersion).withDottyCompat(scalaVersion.value),
      ("com.regblanc" %% "scala-smtlib" % "0.2.2-7-g00a9686").withDottyCompat(scalaVersion.value),
      ("uuverifiers" %% "princess" % "2016-12-26").withDottyCompat(scalaVersion.value)
    // ).map(_.withDottyCompat(scalaVersion.value))
    // ).map { x => val res = x.withDottyCompat(scalaVersion.value); println(s"* $x  [${x.crossVersion}]  ->  $res"); res }
    )
  )
  .configs(ItTest)
  .settings(Defaults.itSettings : _*)
  .settings(inConfig(ItTest)(Defaults.testTasks ++ Seq(
    logBuffered := false,
    parallelExecution := false
  )) : _*)
  .settings(compile := ((compile in Compile) dependsOn script).value)

publishMavenStyle := true

publishTo := {
  val nexus = "https://oss.sonatype.org/"
  // @nv: we can't use `isSnapshot` here as it is not compatible with sbt-git versioning
  if (version.value.trim.endsWith("SNAPSHOT")) Some("snapshots" at nexus + "content/repositories/snapshots")
  else                                         Some("releases"  at nexus + "service/local/staging/deploy/maven2")
}

publishArtifact in (Test, packageBin) := true

publishArtifact in (ItTest, packageBin) := true

addArtifact(artifact in (ItTest, packageBin), packageBin in ItTest)

pomIncludeRepository := { _ => false }

licenses := Seq("GNU Affero General Public License, Version 3" -> url("http://www.gnu.org/licenses/agpl-3.0.html"))

homepage := Some(url("https://github.com/epfl-lara/inox"))

pomExtra := (
  <scm>
    <url>git@github.com:epfl-lara/inox.git</url>
    <connection>scm:git:git@github.com:epfl-lara/inox.git</connection>
  </scm>
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
