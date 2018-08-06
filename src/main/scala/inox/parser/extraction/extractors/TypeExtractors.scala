package inox
package parser
package extraction
package extractors

trait TypeExtractors { self: Extractors =>
  import Types._
  implicit object TypeX extends Extractor[Type, trees.Type, Unit] {
    override def extract(template: Type, scrutinee: trees.Type): Matching[Unit] = template match {
      case TypeHole(index) => Matching(index -> scrutinee)
      case Primitive(tpe) => {
        import Primitives._
        (tpe, scrutinee) match {
          case (UnitType, trees.UnitType()) => Matching.success
          case (CharType, trees.CharType()) => Matching.success
          case (StringType, trees.StringType()) => Matching.success
          case (IntegerType, trees.IntegerType()) => Matching.success
          case (BVType(size1), trees.BVType(size2)) if size1 == size2 => Matching.success
          case (RealType, trees.RealType()) => Matching.success
          case (BooleanType, trees.BooleanType()) => Matching.success
          case _ => Matching.fail
        }
      }
      case FunctionType(froms, to) => scrutinee match {
        case trees.FunctionType(sFroms, sTo) =>
          TypeSeqX.extract(froms, sFroms) >> TypeX.extract(to, sTo)
        case _ => Matching.fail
      }
      case TupleType(elems) => scrutinee match {
        case trees.TupleType(sElems) =>
          TypeSeqX.extract(elems, sElems).withValue(())
        case _ =>
          Matching.fail
      }
      case Operation(operator, args) => {
        import Operators._

        (operator, scrutinee) match {
          case (Set, trees.SetType(sElem)) =>
            TypeSeqX.extract(args, Seq(sElem)).withValue(())
          case (Bag, trees.BagType(sElem)) =>
            TypeSeqX.extract(args, Seq(sElem)).withValue(())
          case (Map, trees.MapType(sFrom, sTo)) =>
            TypeSeqX.extract(args, Seq(sFrom, sTo)).withValue(())
          case _ =>
            Matching.fail
        }
      }
      case Invocation(id, args) => scrutinee match {
        case trees.ADTType(sId, sArgs) =>
          IdX.extract(id, sId) >> TypeSeqX.extract(args, sArgs).withValue(())
        case _ =>
          Matching.fail
      }
      case RefinementType(binding, pred) => scrutinee match {
        case trees.RefinementType(sBinding, sPred) => for {
          opt <- BindingX.extract(binding, sBinding)
          _ <- ExprX.extract(pred, sPred).extendLocal(opt.toSeq)
        } yield ()
        case _ =>
          Matching.fail
      }
      case Variable(id) => scrutinee match {
        case trees.TypeParameter(sId, _) =>
          IdX.extract(id, sId).withValue(())
        case _ =>
          Matching.fail
      }
      case PiType(bindings, to) => scrutinee match {
        case trees.PiType(sBindings, sTo) => for {
          opts <- BindingSeqX.extract(bindings, sBindings)
          _ <- TypeX.extract(to, sTo).extendLocal(opts.flatten)
        } yield ()
      }
    }
  }

  implicit object TypeSeqX extends HSeqX[Type, trees.Type, Unit](TypeX, ())
}