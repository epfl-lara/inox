/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

trait SimpleSymbols { self: Trees =>

  class Symbols(
    val functions: Map[Identifier, FunDef],
    val adts: Map[Identifier, ADTDefinition]
  ) extends AbstractSymbols {

    def transform(t: TreeTransformer) = new Symbols(
      functions.mapValues(fd => new FunDef(
        fd.id,
        fd.tparams, // type parameters can't be transformed!
        fd.params.map(vd => t.transform(vd)),
        t.transform(fd.returnType),
        t.transform(fd.fullBody),
        fd.flags)),
      adts.mapValues {
        case sort: ADTSort => sort
        case cons: ADTConstructor => new ADTConstructor(
          cons.id,
          cons.tparams,
          cons.sort,
          cons.fields.map(t.transform),
          cons.flags)
      })

    def extend(functions: Seq[FunDef] = Seq.empty, adts: Seq[ADTDefinition] = Seq.empty) = new Symbols(
      this.functions ++ functions.map(fd => fd.id -> fd),
      this.adts ++ adts.map(cd => cd.id -> cd)
    )
  }
}
