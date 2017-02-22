
addSbtPlugin("org.tpolecat" % "tut-plugin" % "0.4.8")

addSbtPlugin("com.typesafe.sbt" % "sbt-git" % "0.8.5")

// avoids warning from sbt-git, see https://github.com/sbt/sbt-git#known-issues
libraryDependencies += "org.slf4j" % "slf4j-nop" % "1.7.21"
