
# Inox: Solver for Higher-Order Functional Programs

[![Build Status](https://github.com/epfl-lara/inox/actions/workflows/inox-CI.yml/badge.svg?branch=main)](https://github.com/epfl-lara/inox/actions/workflows/inox-CI.yml/?branch=main)
[![Maven Central 2.11](https://img.shields.io/maven-central/v/ch.epfl.lara/inox_2.11.svg?label=latest%20release%20for%202.11)](https://search.maven.org/search?q=g:ch.epfl.lara%20AND%20a:inox_2.11)
[![Maven Central 2.12](https://img.shields.io/maven-central/v/ch.epfl.lara/inox_2.12.svg?label=latest%20release%20for%202.12)](https://search.maven.org/search?q=g:ch.epfl.lara%20AND%20a:inox_2.12)

Inox is a solver for higher-order functional programs, providing first-class support for features such as:

- Recursive and first-class functions
- ADTs, integers, bitvectors, strings, set-multiset-map abstractions
- Quantifiers
- ADT invariants
- Dependent types


Interfacing with the solver can be done through the Scala API by constructing the AST for your query and feeding it to one of the solvers. For more information, see:
- The usage [tutorial](doc/tutorial.md) for using Inox as a library.
- The tree [interpolators](doc/interpolations.md) for easy tree construction/extraction.
- The [API](doc/API.md) for available solver/evaluator calls.
- The [trees](doc/trees.md) API and how to extend them.


## Add Inox as a Dependency

To use Inox as a Scala 3 dependency, refer to a specific git commit in your
`build.sbt` file as follows: 

```scala
def remoteProject(repo: String, version: String) = RootProject(uri(s"${repo}#${version}"))

// Choose a commit hash to pin the Inox version (replace with the latest or chosen commit):
val inoxRepository = "https://github.com/epfl-lara/inox.git"
val inoxCommitHash = "467725efc4f7d7cf92017581ded04e257bee7368" // example commit

lazy val inox = remoteProject(inoxRepository, inoxCommitHash)

// And depend on it in your project
lazy val yourProject = (project in file("."))
  .settings(
    // ...
  )
  .dependsOn(inox) // <<<
```

## Command-line Interface

One can also use Inox through command-line by using the
[TIP](https://tip-org.github.io/) format to describe the relevant query. The
easiest way to use the Inox command line is to simply [build](#building-inox)
the project and use the generated `inox` script.

## Solver Backends

Inox relies on SMT solvers to solve the constraints it generates. Inox ships
with the JVM SMT solver [Princess](https://github.com/uuverifiers/princess) and
Horn solver [Eldarica](https://github.com/uuverifiers/eldarica) which should
work out of the box on any system.

You can also use the following external SMT solvers:

  * [Z3](https://github.com/Z3Prover/z3)
  * [cvc5](https://cvc5.github.io/)
  * [CVC4](https://cvc4.cs.stanford.edu)

Solver binaries you install should match your operating system and architecture.
We recommend installing these solvers as binaries and ensuring they are
available in your `$PATH` (as `z3` or `cvc5`). Once installed, you can instruct
Inox to use a sequence of solvers. The more solvers you have installed, the more
likely Inox is to succeed, as solver capabilities are often complementary.

### Native Z3 API

In addition to these external binaries, a native Z3 API for Linux is bundled
with Inox and should work out of the box (although having an external Z3 binary
is a good idea in any case). If you [build](#building-inox) yourself, the
generated script should put the native API onto your classpath. Otherwise, you
will have to make sure the relevant jar from [unmanaged](./unmanaged/) is on
your runtime classpath.

If a version for your platform is not shipped with Inox, you will have to
recompile the native Z3 communication layer yourself; see the
[ScalaZ3](https://github.com/epfl-lara/ScalaZ3) repository for information about
how to build and package the project. You will then need to copy the resulting
jar into the [unmanaged](./unmanaged/) directory, named
`scalaz3-$os-$arch-$scalaBinaryVersion.jar` (replace the variables with the
relevant values).

### Solver Defaults

Currently, the default solver is the native Z3 API. If that solver is
unavailable, a series of fallbacks occur, ending with the *princess* solver. You
can specify which solver to use by, for example, giving the option
`--solvers=smt-cvc5` to use cvc5. Check the `--solvers` line in Inox's help for
more details.

## Building Inox

Inox is easiest to build on Linux-like platforms, but see below for other platforms.

Due to the evolving nature of the project, this documentation may not always be up to date for all platforms; we welcome pull requests with carefully written and tested improvements to the information below.

**Requirements:**

* [Java Development Kit 17](https://openjdk.org/projects/jdk/17/) for your
  platform (and the corresponding runtime environment)
* sbt >= 1.6.0 (Available from http://www.scala-sbt.org/)
* The [git](https://git-scm.com/) command on your path


### Linux and macOS

Get the sources of Inox by cloning the official Inox repository:

```console
$ git clone https://github.com/epfl-lara/inox
Cloning into 'inox'...
// ...
$ cd inox
$ sbt clean compile
// takes about 1 minute
```
 

Inox compilation generates an `inox` bash script that runs Inox with all the appropriate settings. This script expects input files in the [TIP](https://tip-org.github.io/) format and will report SAT or UNSAT for the specified properties.

See ``./inox --help`` for more information about CLI usage.

### Windows

__Not well tested!__

We strongly recommend using [Windows Subsystem for Linux (WSL)](https://learn.microsoft.com/en-us/windows/wsl/install) to run Inox on Windows. However, if you wish to run Inox natively on Windows:

- You will need a Git shell for Windows, e.g. [Git for Windows](https://git-for-windows.github.io/). Building then proceeds as described [above](#linux-and-macos).
- You will need to either port the `inox` bash script to Windows, or run it under [Cygwin](https://cygwin.com/).

You may be able to obtain additional tips on getting Inox to work on Windows from [Mikael Mayer](https://people.epfl.ch/mikael.mayer) or on [his dedicated web page](https://lara.epfl.ch/~mayer/leon/).

### Running Tests


Inox comes with a test suite. You can run the following commands to invoke different test suites:

```console
$ sbt test
$ sbt it:test
```

## Contributing

Contributions are welcome! Please open issues or pull requests for bug fixes, improvements, or documentation updates.

## License

This project is licensed under the [Apache License 2.0](LICENSE).
