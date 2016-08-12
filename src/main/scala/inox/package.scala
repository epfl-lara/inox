/* Copyright 2009-2016 EPFL, Lausanne */

/** Core package of the Inox solving interface
  *
  * == Structure ==
  *
  * The package is organized in the following subpackages:
  *
  * [[inox.ast]]: Provides definitions for expressions, types and definitions,
  *   as well as operations on them
  * [[inox.datagen]]: Generators/enumerators for Inox expressions
  * [[inox.evaluators]]: Evaluators of Inox expressions
  * [[inox.solvers]]: Interfaces to SMT-solvers
  * [[inox.transformers]]: Tree transformations for Inox expressions
  * [[inox.utils]]: Utility methods
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
      classes: Seq[inox.trees.ClassDef]): InoxProgram = new Program {
        val trees = inox.trees
        val ctx = ictx
        val symbols = new inox.trees.Symbols(
          functions.map(fd => fd.id -> fd).toMap,
          classes.map(cd => cd.id -> cd).toMap)
      }

    def apply(ictx: InoxContext, sym: inox.trees.Symbols): InoxProgram = new Program {
      val trees = inox.trees
      val ctx = ictx
      val symbols = sym
    }
  }

  object trees extends ast.Trees {

    object deconstructor extends {
      protected val s: trees.type = trees
      protected val t: trees.type = trees
    } with ast.TreeDeconstructor

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
          t.transform(fd.fullBody),
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
