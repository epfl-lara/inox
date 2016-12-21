Inox 1.0 [![Build Status](http://laraquad4.epfl.ch:9000/epfl-lara/inox/status/master)](http://laraquad4.epfl.ch:9000/epfl-lara/inox)
==========

Inox is a solver for higher-order functional programs which provides first-class support for
features such as:
- Recursive and first-class functions
- ADTs, integers, bitvectors, strings, set-multiset-map abstractions
- Quantifiers
- ADT invariants

Interfacing with the solver can take place through the Scala API by constructing the AST
corresponding to the query of interest and then feeding it to one of the solvers.
See the [tutorial](src/doc/tutorial.md) and [API](src/doc/API.md) for more information.

Alternatively, one can use Inox through command-line by using the [TIP](https://tip-org.github.io/) format
to describe the relevant query.

Building Inox
===============

Inox is probably easiest to build on Linux-like platforms, but read on regarding other platforms.

Due to its nature, this documentation section may not always
be up to date; we welcome pull requests with carefully
written and tested improvements to the information below.

**Requirements:**

* [Java SE Development Kit 8](http://www.oracle.com/technetwork/java/javase/downloads/jdk8-downloads-2133151.html) or [Java SE Development Kit 7](http://www.oracle.com/technetwork/java/javase/downloads/jdk7-downloads-1880260.html) for your platform
* SBT 0.13.x (Available from http://www.scala-sbt.org/)
* Git and svn executables

Linux & Mac OS-X
----------------

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

Windows
-------

__Not yet tested!__

Get the sources of Inox by cloning the official Inox
repository. You will need a Git shell for windows, e.g. 
[Git for Windows](https://git-for-windows.github.io/).

```
$ git clone https://github.com/epfl-lara/inox.git
Cloning into 'inox'...
// ...
$ cd inox
$ sbt clean compile
// takes about 1 minutes
```
 
You will now need to either port the bash ``inox`` script to Windows, or run it
under Cygwin.

**Known issues**

The default solver underlying Inox (nativez3) ships with a wrapped native library.
See the [ScalaZ3](https://github.com/epfl-lara/ScalaZ3) repository for tips on getting
the solver running on Windows. Alternatively, one can use the
[Princess](http://www.philipp.ruemmer.org/princess.shtml) solver
(command-line option ``--solvers=princess``) to get a full JVM stack experience that
should work out of the box.

You may be able to obtain additional tips on getting Inox to work on Windows 
from [Mikael Mayer](http://people.epfl.ch/mikael.mayer) or on [his dedicated web page](http://lara.epfl.ch/~mayer/leon/),

External Solvers
----------------

Inox typically relies on external (SMT) solvers to solve the constraints it generates. 

We currently support two major SMT solvers:

  * CVC4, http://cvc4.cs.nyu.edu/web/
  * Z3, https://github.com/Z3Prover/z3

Solver binaries that you install should match your operating
system and your architecture.  We recommend that you install
these solvers as a binary and have their binaries available
in the ``$PATH``.  Once they are installed, you can instruct
Inox to use a given sequence of solvers.  The more solvers
you have installed, the more successful Inox might get,
because solver capabilities are incomparable.

In addition to these external binaries, a native Z3 API for
Linux is bundled with Inox and should work out of the box
(although having an external Z3 binary is a good idea in any
case). For other platforms you will have to recompile the
native Z3 communication layer yourself; see the section
below. Inox also bundles a JVM SMT solver
[Princess](http://www.philipp.ruemmer.org/princess.shtml) which
should work out of the box on any system.

As of now the default solver is the native Z3 API, you will
have to explicitly specify another solver if this native
layer is not available to you, e.g., by giving the option
``--solvers=smt-cvc4`` to use CVC4. Check the ``--solvers``
line in Inox' help.

Building ScalaZ3 and Z3 API
---------------------------

The main reason for using the Z3 API is that it is currently
faster when there are many calls to the solver. See the
[ScalaZ3](https://github.com/epfl-lara/ScalaZ3) repository for
information about how to build and package the project. You will
then need to copy the resulting jar into the "unmanaged" directory.

Running Tests
-------------

Inox comes with a test suite. Consider running the following commands to
invoke different test suites:

```
$ sbt test
$ sbt it:test
```
