package inox
package parser
package elaboration
package elaborators

trait FunctionElaborators { self: Elaborators =>

  import Functions._

  class SingleFunctionE extends Elaborator[Function, Eventual[trees.FunDef]] {
    override def elaborate(function: Function)(implicit store: Store): Constrained[Eventual[trees.FunDef]] = for {
      sf <- SignatureE.elaborate(function)
      (st, ev) <- ExprE.elaborate(function.body)(store
        .addFunction(sf)
        .addTypeBindings(sf.typeParams)
        .addBindings(sf.params))
      _ <- Constrained(Constraint.equal(st, sf.retTpe))
    } yield Eventual.withUnifier { implicit unifier =>
      new trees.FunDef(
        sf.id,
        sf.typeParams.map(binding => trees.TypeParameterDef(binding.id, Seq())),
        sf.params.map(_.evValDef.get),
        sf.evRetTpe.get,
        ev.get,
        Seq())
    }
  }
  val SingleFunctionE = new SingleFunctionE

  class SignatureE extends Elaborator[Function, SimpleFunctions.Function] {
    override def elaborate(function: Function)(implicit store: Store): Constrained[SimpleFunctions.Function] = for {
      (i, optName) <- DefIdE.elaborate(function.identifier)
      tpbs <- TypeVarDefSeqE.elaborate(function.typeParams)
      storeWithTypeParams = store.addTypeBindings(tpbs)
      bs <- BindingSeqE.elaborate(function.params)(storeWithTypeParams)
      (stRet, evRet) <- OptTypeE.elaborate(function.returnType match {
        case Some(tpe) => Right(tpe)
        case None => Left(function.pos)
      })(storeWithTypeParams)
    } yield SimpleFunctions.Function(i, optName, tpbs, bs, stRet, evRet)
  }
  val SignatureE = new SignatureE
}