package inox
package parser
package elaboration
package elaborators

trait ProgramElaborators { self: Elaborators =>

  import Programs._
  import ADTs._
  import Functions._

  class ProgramE extends Elaborator[Program, Seq[Eventual[trees.Definition]]] {
    override def elaborate(program: Program)(implicit store: Store): Constrained[Seq[Eventual[trees.Definition]]] = {
      val sorts = program.defs.filter(_.isLeft).map(_.left.get)
      val funs = program.defs.filter(_.isRight).map(_.right.get)

      def rebuild[A](defs: Seq[Either[Sort, Function]], xs: Seq[A], ys: Seq[A]): Seq[A] = defs.foldLeft((Seq[A](), xs, ys)) {
        case ((acc, x :: xs, ys), Left(_)) => (acc :+ x, xs, ys)
        case ((acc, xs, y :: ys), Right(_)) => (acc :+ y, xs, ys)
        case _ => throw new IllegalStateException("Unreachable.")
      }._1

      for {
        emptySimpleSorts <- Constrained.sequence(sorts.map(s => EmptySortE.elaborate(s)))
        storeWithEmptySorts = store.addSorts(emptySimpleSorts)
        (simpleSorts, evSorts) <- Constrained.sequence(sorts.zip(emptySimpleSorts).map {
          case (sort, ss) => for {
            (scs, ecs) <- new ConstructorSeqE(ss.id)
              .elaborate(sort.constructors)(storeWithEmptySorts.addTypeBindings(ss.typeParams)).map(_.unzip)
            fieldNames = scs.flatMap(_.params.flatMap(_.name))
            _ <- Constrained.checkImmediate(fieldNames.toSet.size == fieldNames.size, sort, fieldsNotDistincts)
          } yield (ss.copy(constructors=scs), Eventual.withUnifier { implicit unifier =>
            new trees.ADTSort(ss.id, ss.typeParams.map(tb => trees.TypeParameterDef(tb.id, Seq())), ecs.map(_.get), Seq()) })
        }).map(_.unzip)
        storeWithSorts = store.addSorts(simpleSorts)
        signatures <- Constrained.sequence(funs.map(f => SignatureE.elaborate(f)(storeWithSorts)))
        storeWithFunSignatures = storeWithSorts.addFunctions(signatures)
        evFunsDefs <- Constrained.sequence(funs.zip(signatures).map {
          case (function, sf) => for {
            (st, ev) <- ExprE.elaborate(function.body)(storeWithFunSignatures
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
        })
      } yield rebuild(program.defs, evSorts, evFunsDefs)
    }
  }
  val ProgramE = new ProgramE
}