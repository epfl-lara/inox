package inox
package parser
package elaboration
package elaborators

trait FunctionElaborators { self: Elaborators =>

  import Functions._
  object FunctionE extends Elaborator[Function, Eventual[trees.FunDef]] {
    override def elaborate(function: Function)(implicit store: Store): Constrained[Eventual[trees.FunDef]] = ???
  }

  object SignatureE extends Elaborator[Function, SimpleFunctions.Function] {
    override def elaborate(function: Function)(implicit store: Store): Constrained[SimpleFunctions.Function] = for {
      (i, optName) <- DefIdE.elaborate(function.identifier)
      tpbs <- TypeVarDefSeqE.elaborate(function.typeParams)
      bs <- BindingSeqE.elaborate(function.params)(store.addTypeBindings(tpbs))
    } yield SimpleFunctions.Function(i, optName, tpbs, bs)
  }

}