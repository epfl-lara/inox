package inox
package parser
package extraction
package extractors

trait TypeExtractors { self: Extractors =>

  import Types._

  class TypeX extends Extractor[Type, trees.Type, Unit] {
    override def extract(template: Type, scrutinee: trees.Type): Matching[Unit] = template match {
      case TypeHole(index) => Matching(index -> scrutinee)
      case Primitive(tpe) => {
        import Primitives._
        Matching.collect((tpe, scrutinee)) {
          case (UnitType, trees.UnitType()) => Matching.success
          case (CharType, trees.CharType()) => Matching.success
          case (StringType, trees.StringType()) => Matching.success
          case (IntegerType, trees.IntegerType()) => Matching.success
          case (BVType(signed1, size1), trees.BVType(signed2, size2)) if signed1 == signed2 && size1 == size2 => Matching.success
          case (RealType, trees.RealType()) => Matching.success
          case (BooleanType, trees.BooleanType()) => Matching.success
        }
      }
      case FunctionType(froms, to) => Matching.collect(scrutinee) {
        case trees.FunctionType(sFroms, sTo) =>
          TypeSeqX.extract(froms, sFroms) <> TypeX.extract(to, sTo)
      }
      case TupleType(elems) => Matching.collect(scrutinee) {
        case trees.TupleType(sElems) =>
          TypeSeqX.extract(elems, sElems).withValue(())
      }
      case Operation(operator, args) => {
        import Operators._

        Matching.collect((operator, scrutinee)) {
          case (Set, trees.SetType(sElem)) =>
            TypeSeqX.extract(args, Seq(sElem)).withValue(())
          case (Bag, trees.BagType(sElem)) =>
            TypeSeqX.extract(args, Seq(sElem)).withValue(())
          case (Map, trees.MapType(sFrom, sTo)) =>
            TypeSeqX.extract(args, Seq(sFrom, sTo)).withValue(())
        }
      }
      case Invocation(id, args) => Matching.collect(scrutinee) {
        case trees.ADTType(sId, sArgs) =>
          TypeUseIdX.extract(id, sId) <> TypeSeqX.extract(args, sArgs)
      }
      case RefinementType(binding, pred) => Matching.collect(scrutinee) {
        case trees.RefinementType(sBinding, sPred) =>
          BindingX.extract(binding, sBinding).flatMap { opt =>
            ExprX.extract(pred, sPred).extendLocal(opt.toSeq)
          }
      }
      case Variable(id) => Matching.collect(scrutinee) {
        case trees.ADTType(sId, Seq()) =>
          TypeUseIdX.extract(id, sId)
        case trees.TypeParameter(sId, _) =>
          TypeUseIdX.extract(id, sId)
      }
      case PiType(bindings, to) => Matching.collect(scrutinee) {
        case trees.PiType(sBindings, sTo) =>
          BindingSeqX.extract(bindings, sBindings).flatMap { opts =>
            TypeX.extract(to, sTo).extendLocal(opts.flatten)
          }
      }
      case SigmaType(bindings, to) => Matching.collect(scrutinee) {
        case trees.SigmaType(sBindings, sTo) =>
          BindingSeqX.extract(bindings, sBindings).flatMap { opts =>
            TypeX.extract(to, sTo).extendLocal(opts.flatten)
          }
      }
    }
  }
  val TypeX = new TypeX

  class TypeSeqX extends HSeqX[Type, trees.Type, Unit](TypeX, ())
  val TypeSeqX = new TypeSeqX
}