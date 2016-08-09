/* Copyright 2009-2016 EPFL, Lausanne */

/** Core package of the Inox solving interface
  *
  * ==Structure==
  * 
  * Leon is organized similarly to a compiler with a concept of [[leon.Pipeline]]
  * and [[leon.LeonPhase]]. The main phases of Leon are implemented in subpackages, with
  * an overview of the role of each of them below.
  * 
  * The definition of the Pure Scala AST is in [[leon.purescala]]. Most of the other packages
  * are articulated around the definitions of these ASTs. The [[leon.xlang]] provides extensions
  * to the Pure Scala AST, but most of the other packages will ignore these extensions and
  * assume a Pure Scala only AST.
  * 
  *   - [[leon.codegen]] provides bytecode generator for Leon programs. Enable the conversion of a [[leon.purescala.Definitions.Program]] to JVM bytecode.
  * 
  *   - [[leon.datagen]] provides a generator of expressions (trees), based on vanuatoo.
  * 
  *   - [[leon.evaluators]] implements different evaluators for Leon programs in Pure Scala. 
  * 
  *   - [[leon.frontends]] provides the different front-ends to Leon. Currently it only implements a scalac integration, but it could potentially support other language.
  * 
  *   - [[leon.purescala]] defines the core AST for Pure Scala. Also provides useful tree manipulation methods.
  * 
  *   - [[leon.repair]] implements the Repair module of Leon.
  * 
  *   - [[leon.solvers]] provides an interface and implementations to solvers for Pure Scala expressions. The solvers are typically wrappers around SMT solvers, with some additional algorithms to handle recursive function invocations.
  * 
  *   - [[leon.synthesis]] implements the Synthesis module of Leon.
  * 
  *   - [[leon.termination]] implements the termination checker of Leon.
  * 
  *   - [[leon.utils]]
  * 
  *   - [[leon.verification]] implements the verification module of Leon.
  * 
  *   - [[leon.xlang]] provides extensions to Pure Scala. In particular, it introduces some expressions to represent imperative programs. Also provides the code to map such programs to Pure Scala equivalent ones.
  *
  */
package object inox {
  implicit class BooleanToOption(cond: Boolean) {
    def option[A](v: => A) = if (cond) Some(v) else None
  }

  case class FatalError(msg: String) extends Exception(msg)

  type InoxProgram = Program { val trees: inox.trees.type }

  object InoxProgram {
    def apply(ictx: InoxContext,
      functions: Seq[inox.trees.FunDef],
      classes: Seq[inox.trees.ClassDef]) = new Program {
        val trees = inox.trees
        val ctx = ictx
        val symbols = new inox.trees.Symbols(
          functions.map(fd => fd.id -> fd).toMap,
          classes.map(cd => cd.id -> cd).toMap)
      }
  }

  object trees extends ast.Trees {

    class Symbols(
      val functions: Map[Identifier, FunDef],
      val classes: Map[Identifier, ClassDef]
    ) extends AbstractSymbols {

      def transform(t: TreeTransformer) = new Symbols(
        functions.mapValues(fd => new FunDef(
          fd.id,
          fd.tparams, // type parameters can't be transformed!
          fd.params.map(vd => t.transform(vd)),
          t.transform(fd.returnType),
          fd.body.map(t.transform),
          fd.flags)),
        classes.mapValues {
          case acd: AbstractClassDef => acd
          case ccd: CaseClassDef => new CaseClassDef(
            ccd.id,
            ccd.tparams,
            ccd.parent,
            ccd.fields.map(t.transform),
            ccd.flags)
        })

      def extend(functions: Seq[FunDef] = Seq.empty, classes: Seq[ClassDef] = Seq.empty) = new Symbols(
        this.functions ++ functions.map(fd => fd.id -> fd),
        this.classes ++ classes.map(cd => cd.id -> cd)
      )
    }
  }
}
