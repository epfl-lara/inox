name := "inox"

version := "1.0"

organization := "ch.epfl.lara"

scalaVersion := "2.11.8"

scalacOptions ++= Seq(
  "-deprecation",
  "-unchecked",
  "-feature"
)

scalacOptions in (Compile, doc) ++= Seq("-doc-root-content", baseDirectory.value+"/src/main/scala/root-doc.txt")

val osName = Option(System.getProperty("os.name")).getOrElse("").toLowerCase()

val osArch = System.getProperty("sun.arch.data.model")

if(osName.indexOf("win") != -1) {
  (unmanagedJars in Compile) += baseDirectory.value / "unmanaged" / s"scalaz3-win-$osArch.jar"
} else {
  (unmanagedJars in Compile) += baseDirectory.value / "unmanaged" / s"scalaz3-unix-$osArch.jar"
}

unmanagedBase <<= baseDirectory { base => base / "unmanaged" / osArch }

resolvers ++= Seq(
  "Typesafe Repository" at "http://repo.typesafe.com/typesafe/releases/",
  "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots",
  "Sonatype OSS Releases" at "https://oss.sonatype.org/content/repositories/releases"
)

libraryDependencies ++= Seq(
  "org.scalatest" %% "scalatest" % "2.2.4" % "test;it",
  "com.typesafe.akka" %% "akka-actor" % "2.3.4",
  "org.apache.commons" % "commons-lang3" % "3.4"
  //"com.regblanc" %% "scala-smtlib" % "0.2"
)

lazy val scriptName = "inox"

lazy val scriptFile = file(".") / scriptName

clean := {
  clean.value
  if (scriptFile.exists && scriptFile.isFile) {
    scriptFile.delete
  }
}

lazy val script = taskKey[Unit]("Generate the inox Bash script")

script := {
  val s = streams.value
  try {
    val cps = (dependencyClasspath in Compile).value
    val out = (classDirectory      in Compile).value
    val res = (resourceDirectory   in Compile).value

    if (scriptFile.exists) {
      s.log.info("Regenerating '" + scriptFile.getName + "' script")
      scriptFile.delete
    } else {
      s.log.info("Generating '" + scriptFile.getName + "' script")
    }

    val paths = res.getAbsolutePath +: out.getAbsolutePath +: cps.map(_.data.absolutePath)
    val cp = paths.mkString(System.getProperty("path.separator"))
    IO.write(scriptFile, s"""|#!/bin/bash --posix
                             |
                             |SCALACLASSPATH=$cp
                             |
                             |java -Xmx2G -Xms512M -Xss64M -classpath "$${SCALACLASSPATH}" -Dscala.usejavacp=true inox.Main $$@ 2>&1
                             |""".stripMargin)
    scriptFile.setExecutable(true)
  } catch {
    case e: Throwable =>
      s.log.error("There was an error while generating the script file: " + e.getLocalizedMessage)
  }
}

Keys.fork in run := true

testOptions in Test := Seq(Tests.Argument("-oDF"))

// Note that we can't use IntegrationTest because it is already defined in sbt._
lazy val ItTest = config("it") extend(Test)

testOptions in ItTest := Seq(Tests.Argument("-oDF"))

def ghProject(repo: String, version: String) = RootProject(uri(s"git://$repo#$version"))

def svnProject(repo: String, version: String, user: String, pass: String) =
  RootProject(uri(s"svn+credentials://$repo#username=$user&password=$pass&$version"))

lazy val bonsai      = ghProject("github.com/colder/bonsai.git",     "10eaaee4ea0ff6567f4f866922cb871bae2da0ac")
lazy val scalaSmtlib = ghProject("github.com/regb/scala-smtlib.git", "850580ae86e299a1baa0eaef9e24eed905fefe58")

lazy val princess    = svnProject("hal4.it.uu.se/princess/interpolation/trunk", "2703", "anonymous", "anonymous")

// XXX @nv: complex hack to make sure we don't have a name clash between
//          princess' smtlib parser and the scala-smtlib one.
lazy val classpathSettings = {
  def cleanClasspath(config: Configuration) =
    unmanagedClasspath in config := {
      val prev = (unmanagedClasspath in config).value
      val princessJars = (unmanagedJars in (princess, Compile)).value.toSet
      prev.filterNot(princessJars)
    }

  Seq(cleanClasspath(Compile), cleanClasspath(Test), cleanClasspath(ItTest))
}

lazy val root = (project in file("."))
  .configs(ItTest)
  .settings(Defaults.itSettings : _*)
  .settings(inConfig(ItTest)(Defaults.testTasks ++ Seq(
    logBuffered := false,
    parallelExecution := false
  )) : _*)
  .settings(compile <<= (compile in Compile) dependsOn script)
  .dependsOn(bonsai)
  .dependsOn(scalaSmtlib)
  .dependsOn(princess)
  .settings(classpathSettings : _*)
  .settings(
    // @nv: ignore warnings from projects that are out of our control
    logLevel in (scalaSmtlib, Compile) := Level.Error,
    logLevel in (princess, Compile) := Level.Error
  )

