
addSbtPlugin("org.scalameta" % "sbt-mdoc" % "2.6.3")

addSbtPlugin("com.typesafe.sbt" % "sbt-git" % "1.0.0")

// avoids warning from sbt-git, see https://github.com/sbt/sbt-git#known-issues
libraryDependencies += "org.slf4j" % "slf4j-nop" % "1.7.21"

addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "0.15.0")

// Test coverage: `sbt coverage test it:test coverageAggregate`
addSbtPlugin("org.scoverage" % "sbt-scoverage" % "2.4.4")
