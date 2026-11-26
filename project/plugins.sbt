
addSbtPlugin("org.scalameta" % "sbt-mdoc" % "2.6.3")

addSbtPlugin("com.github.sbt" % "sbt-git" % "3.0.0")

// sbt-git 3.0.0 still bundles JGit 5.13, which cannot resolve linked-worktree
// commondir metadata. JGit 7.8.1 supports that layout and requires Java 17+.
dependencyOverrides += "org.eclipse.jgit" % "org.eclipse.jgit" % "7.8.1.202611041320-r"

// avoids warning from sbt-git, see https://github.com/sbt/sbt-git#known-issues
libraryDependencies += "org.slf4j" % "slf4j-nop" % "1.7.21"

addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "0.15.0")

// Test coverage: `sbt coverage test it:test coverageAggregate`
addSbtPlugin("org.scoverage" % "sbt-scoverage" % "2.4.4")
