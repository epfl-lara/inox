[![Build
Status](https://github.com/epfl-lara/inox/actions/workflows/inox-CI.yml/badge.svg?branch=main)](https://github.com/epfl-lara/inox/actions/workflows/inox-CI.yml/?branch=main)
[<img
src="https://img.shields.io/maven-central/v/ch.epfl.lara/inox_2.11.svg?label=latest%20release%20for%202.11"/>](http://search.maven.org/#search%7Cga%7C1%7Cg%3Ach.epfl.lara%20a%3Ainox_2.11)
[<img
src="https://img.shields.io/maven-central/v/ch.epfl.lara/inox_2.12.svg?label=latest%20release%20for%202.12"/>](http://search.maven.org/#search%7Cga%7C1%7Cg%3Ach.epfl.lara%20a%3Ainox_2.12)
==========

Inox is a solver for higher-order functional programs which provides first-class
support for features such as:
- Recursive and first-class functions
- ADTs, integers, bitvectors, strings, set-multiset-map abstractions
- Quantifiers
- ADT invariants
- Dependent types

Interfacing with the solver can take place through the Scala API by constructing
the AST corresponding to the query of interest and then feeding it to one of the
solvers. For more information, see:
- The usage [tutorial](doc/tutorial.md) gives some insight on how to use Inox as
  a library.
- The tree [interpolators](doc/interpolations.md) provide easy tree
  construction/extraction for library use.
- A more detailed description of the available solver/evaluator
  [API](doc/API.md) calls.
- A description of the [trees](doc/trees.md) API and how to extend them.

### Add Inox as a dependency

To use Inox as a Scala 3 dependency, refer to a specific git commit in your
`build.sbt` file as follows: 

```scala
def remoteProject(repo: String, version: String) = RootProject(uri(s"${repo}#${version}"))

// choose a commit hash to pin Inox version
val inoxRepository = "https://github.com/epfl-lara/inox.git"
val inoxCommitHash = "467725efc4f7d7cf92017581ded04e257bee7368" // example commit

lazy val inox = remoteProject(inoxRepository, inoxCommitHash)

// and depend on it in your project
lazy val yourProject = (project in file("."))
  .settings(
    // ...
  )
  .dependsOn(inox) // <<<
```

Command-line Interface
----------------------

One can also use Inox through command-line by using the
[TIP](https://tip-org.github.io/) format to describe the relevant query. The
easiest way to use the Inox command line is to simply [build](#building-inox)
the project and use the generated `inox` script.

Solver Backends
---------------

Inox relies on SMT solvers to solve the constraints it generates. Inox ships
with the JVM SMT solver [Princess](https://github.com/uuverifiers/princess) and
Horn solver [Eldarica](https://github.com/uuverifiers/eldarica) which should
work out of the box on any system.

You can also use the following external SMT solvers:

  * Z3, https://github.com/Z3Prover/z3  
  * cvc5, https://cvc5.github.io/
  * CVC4, http://cvc4.cs.stanford.edu

Solver binaries that you install should match your operating system and your
architecture.  We recommend that you install these solvers as a binary and have
their binaries available in the ``$PATH`` (as `z3` or `cvc5`).  Once they are
installed, you can instruct Inox to use a given sequence of solvers. The more
solvers you have installed, the more successful Inox might be, because solver
capabilities are incomparable.

### Native Z3 API

In addition to these external binaries, a native Z3 API for Linux is bundled
with Inox and should work out of the box (although having an external Z3 binary
is a good idea in any case). If you [build](#building-inox) yourself, the
generated script should put the native API onto your classpath. Otherwise, you
will have to make sure the relevant jar from [unmanaged](./unmanaged/) is on
your runtime classpath.

For other platforms than Linux, you will have to recompile the native Z3
communication layer yourself; see
[ScalaZ3](https://github.com/epfl-lara/ScalaZ3) repository for information about
how to build and package the project. You will then need to copy the resulting
jar into the [unmanaged](./unmanaged/) directory named
"scalaz3-$os-$arch-$scalaBinaryVersion.jar" (replace the $ variables by the
relevant values).

### Solver Defaults

As of now, the default solver is the native Z3 API. If that solver is
unavailable, a series of fallbacks take place until the *princess* solver. You
can specify which solver to use by e.g. giving the option ``--solvers=smt-cvc5``
to use cvc5. Check the ``--solvers`` line in Inox' help.

Building Inox
-------------

Inox is probably easiest to build on Linux-like platforms, but read on regarding
other platforms.

Due to its nature, this documentation section may not always be up to date for
different platforms; we welcome pull requests with carefully written and tested
improvements to the information below.

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
// takes about 1 minutes
```
 
Inox compilation generates an ``inox`` bash script that runs Inox with all the
appropriate settings. This script expects argument files in the
[TIP](https://tip-org.github.io/) input format and will report SAT or UNSAT to
the specified properties.

See ``./inox --help`` for more information about script usage.

### Windows

__Not well tested!__

We generally recommend the use of [Windows Subsystem for Linux
(WSL)](https://learn.microsoft.com/en-us/windows/wsl/install) to run Inox on
Windows. Hoewever, if you really wish to run Inox natively on Windows:

You will need a Git shell for Windows, e.g. [Git for
Windows](https://git-for-windows.github.io/). Building then proceeds as
described [above](#linux--mac-os-x).

You will then need to either port the ``inox`` bash script to Windows, or run it
under [Cygwin](https://cygwin.com/).

You may be able to obtain additional tips on getting Inox to work on Windows
from [Mikael Mayer](http://people.epfl.ch/mikael.mayer) or on [his dedicated web
page](http://lara.epfl.ch/~mayer/leon/).

### Running Tests

Inox comes with a test suite. You can run the following commands to invoke
different test suites:

```console
$ sbt test
$ sbt it:test
```
