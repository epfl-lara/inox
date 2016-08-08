/* Copyright 2009-2016 EPFL, Lausanne */

/** Core package of the Inox solving interface */
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
