Inox [![Build Status](http://laraquad4.epfl.ch:9000/epfl-lara/inox/status/master)](http://laraquad4.epfl.ch:9000/epfl-lara/inox) [<img src="https://img.shields.io/maven-central/v/ch.epfl.lara/inox_2.11.svg?label=latest%20release%20for%202.11"/>](http://search.maven.org/#search%7Cga%7C1%7Cg%3Ach.epfl.lara%20a%3Ainox_2.11) [<img src="https://img.shields.io/maven-central/v/ch.epfl.lara/inox_2.12.svg?label=latest%20release%20for%202.12"/>](http://search.maven.org/#search%7Cga%7C1%7Cg%3Ach.epfl.lara%20a%3Ainox_2.12)
==========

Inox is a solver for higher-order functional programs which provides first-class support for
features such as:
- Recursive and first-class functions
- ADTs, integers, bitvectors, strings, set-multiset-map abstractions
- Quantifiers
- ADT invariants

Interfacing with the solver can take place through the Scala API by constructing the AST
corresponding to the query of interest and then feeding it to one of the solvers. For more
information, see:
- The usage [tutorial](doc/tutorial.md) gives some insight on how to use Inox as a library.
- A more detailed description of the available solver/evaluator [API](doc/API.md) calls.
- A description of the [trees](doc/trees.md) API and how to extend them.

To import Inox into your project, add the following lines to your `build.sbt`:
```scala
resolvers += "Sonatype OSS Releases" at "https://oss.sonatype.org/content/repositories/releases"
resolvers += "uuverifiers" at "http://logicrunch.it.uu.se:4096/~wv/maven"
libraryDependencies += "ch.epfl.lara" %% "inox" % "1.0.2"
```

Alternatively, one can use Inox through command-line by using the [TIP](https://tip-org.github.io/) format
to describe the relevant query. The easiest way to use the Inox command line is to simply
[build](#building-inox) the project and use the generated script.

Solver Backends
---------------

Inox relies on SMT solvers to solve the constraints it generates.
Inox ships with the JVM SMT solver
[Princess](http://www.philipp.ruemmer.org/princess.shtml)
which should work out of the box on any system.

You can also use the following external SMT solvers:

  * CVC4, http://cvc4.cs.stanford.edu
  * Z3, https://github.com/Z3Prover/z3

Solver binaries that you install should match your operating
system and your architecture.  We recommend that you install
these solvers as a binary and have their binaries available
in the ``$PATH`` (as `z3` or `cvc4`).  Once they are installed,
you can instruct Inox to use a given sequence of solvers. 
The more solvers you have installed, the more successful Inox might get,
because solver capabilities are incomparable.

### Native Z3 API

In addition to these external binaries, a native Z3 API for
Linux is bundled with Inox and should work out of the box
(although having an external Z3 binary is a good idea in any
case). If you [build](#building-inox) yourself, the generated
script should put the native API onto your classpath. Otherwise,
you will have to make sure the relevant jar from "unmanaged"
is on your runtime classpath.

For other platforms than Linux, you will have to recompile the
native Z3 communication layer yourself; see 
[ScalaZ3](https://github.com/epfl-lara/ScalaZ3) repository for
information about how to build and package the project. You will
then need to copy the resulting jar into the "unmanaged" directory
named "scalaz3-$os-$arch-$scalaBinaryVersion.jar" (replace the
$ variables by the relevant values).

### Solver Defaults

As of now the default solver is the native Z3 API. If that solver
is unavailable, a series of fallbacks take place until the
*princess* solver. You can specify which solver to use by
e.g. giving the option
``--solvers=smt-cvc4`` to use CVC4. Check the ``--solvers``
line in Inox' help.

Building Inox
-------------

Inox is probably easiest to build on Linux-like platforms, but read on regarding other platforms.

Due to its nature, this documentation section may not always
be up to date; we welcome pull requests with carefully
written and tested improvements to the information below.

**Requirements:**

* [Java SE Development Kit 8](http://www.oracle.com/technetwork/java/javase/downloads/jdk8-downloads-2133151.html) or [Java SE Development Kit 7](http://www.oracle.com/technetwork/java/javase/downloads/jdk7-downloads-1880260.html) for your platform
* SBT 0.13.x (Available from http://www.scala-sbt.org/)
* The [git](https://git-scm.com/) command on your path  
  **Note:** this is *only* required for version computation and
  you can avoid installing Git by using JGit (see the
  [related documentation](https://github.com/sbt/sbt-git#using-jgit)
  in `sbt-git`.

### Linux & Mac OS-X

Get the sources of Inox by cloning the official Inox repository:

```
$ git clone https://github.com/epfl-lara/inox.git
Cloning into 'inox'...
// ...
$ cd inox
$ sbt clean compile
// takes about 1 minutes
```
 
Inox compilation generates an ``inox`` bash script that runs Inox with all
the appropriate settings. This script expects argument files in the
[TIP](https://tip-org.github.io/) input format and will report SAT or UNSAT
to the specified properties.

See ``./inox --help`` for more information about script usage.

### Windows

__Not yet tested!__

You will need a Git shell for windows, e.g. 
[Git for Windows](https://git-for-windows.github.io/).
Building then proceeds as described [above](#linux--mac-os-x).

You will then need to either port the bash ``inox`` script to Windows, or run it
under Cygwin.

You may be able to obtain additional tips on getting Inox to work on Windows
from [Mikael Mayer](http://people.epfl.ch/mikael.mayer) or on
[his dedicated web page](http://lara.epfl.ch/~mayer/leon/).

### Running Tests

Inox comes with a test suite. Consider running the following commands to
invoke different test suites:

```
$ sbt test
$ sbt it:test
```
