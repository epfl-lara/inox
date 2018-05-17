
addSbtPlugin("org.tpolecat" % "tut-plugin" % "0.6.4")

addSbtPlugin("com.typesafe.sbt" % "sbt-git" % "0.9.3")

// avoids warning from sbt-git, see https://github.com/sbt/sbt-git#known-issues
libraryDependencies += "org.slf4j" % "slf4j-nop" % "1.7.21"

addSbtPlugin("ch.epfl.lamp" % "sbt-dotty" % "0.2.1")