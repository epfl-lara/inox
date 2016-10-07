name := "inox"

version := "0.1"

organization := "ch.epfl.lara"

scalaVersion := "2.11.8"

scalacOptions ++= Seq(
  "-deprecation",
  "-unchecked",
  "-feature"
)

scalacOptions in (Compile, doc) ++= Seq("-doc-root-content", baseDirectory.value+"/src/main/scala/root-doc.txt")

site.settings

site.sphinxSupport()

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

Keys.fork in run := true

testOptions in Test := Seq(Tests.Argument("-oDF"))

testOptions in IntegrationTest := Seq(Tests.Argument("-oDF"))

def ghProject(repo: String, version: String) = RootProject(uri(s"${repo}#${version}"))

lazy val bonsai      = ghProject("git://github.com/colder/bonsai.git",     "10eaaee4ea0ff6567f4f866922cb871bae2da0ac")
lazy val scalaSmtlib = ghProject("git://github.com/regb/scala-smtlib.git", "567ede66f8df3e5cfc3dbcd5d01b4e7a65fd0719")

lazy val root = (project in file("."))
  .configs(IntegrationTest)
  .settings(Defaults.itSettings : _*)
  .settings(inConfig(IntegrationTest)(Defaults.testTasks ++ Seq(
    logBuffered := false,
    parallelExecution := false
  )) : _*)
  .dependsOn(bonsai)
  .dependsOn(scalaSmtlib)

