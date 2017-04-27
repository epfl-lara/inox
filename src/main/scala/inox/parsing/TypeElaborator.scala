package inox
package parsing

import scala.util.parsing.input._

import Utils.plural

trait TypeElaborators { self: Interpolator => 

  import Utils.{either, traverse, plural}

  trait TypeElaborator { self: TypeIR.type =>

    object BVType {
      def apply(size: Int): String = {
        require(size > 0)

        "Int" + size
      }

      def unapply(name: String): Option[Int] = {
        if (name.startsWith("Int")) {
          scala.util.Try(name.drop(3).toInt).toOption.filter(_ > 0)
        }
        else {
          None
        }
      }
    }

    lazy val basic: Map[Value, trees.Type] = Seq(
      "Boolean" -> trees.BooleanType,
      "BigInt"  -> trees.IntegerType,
      "Char"    -> trees.CharType,
      "Int"     -> trees.Int32Type,
      "Real"    -> trees.RealType,
      "String"  -> trees.StringType,
      "Unit"    -> trees.UnitType).map({ case (n, v) => Name(n) -> v }).toMap

    private lazy val basicInv = basic.map(_.swap)

    private lazy val parametric: Map[Value, (Int, Seq[trees.Type] => trees.Type)] =
      (primitives ++ adts).toMap

    private lazy val primitives = Seq(
      "Set" -> (1, (ts: Seq[trees.Type]) => trees.SetType(ts.head)),
      "Map" -> (2, (ts: Seq[trees.Type]) => trees.MapType(ts(0), ts(1))),
      "Bag" -> (1, (ts: Seq[trees.Type]) => trees.BagType(ts.head))).map({ case (n, v) => Name(n) -> v })

    private lazy val adts = symbols.adts.toSeq.flatMap({
      case (i, d) => {
        val f = (d.tparams.length, (ts: Seq[trees.Type]) => trees.ADTType(i, ts))

        Seq(
          Name(i.name) -> f,
          EmbeddedIdentifier(i) -> f)
      }
    })

    def getType(tpe: Expression): trees.Type = {
      toInoxType(tpe) match {
        case Right(inoxType) => inoxType
        case Left(errors) => throw new TypeElaborationException(errors)
      }
    }

    def toInoxType(expr: Expression): Either[Seq[ErrorLocation], trees.Type] = expr match {

      case Operation(Tuple, irs) if irs.size >= 2 =>
        traverse(irs.map(toInoxType(_))).left.map(_.flatten).right.map(trees.TupleType(_))

      case Operation(Arrow, Seq(Operation(Group, froms), to)) => 
        either(
          traverse(froms.map(toInoxType(_))).left.map(_.flatten),
          toInoxType(to)
        ){
          case (argTpes, retTpe) => trees.FunctionType(argTpes, retTpe)
        }

      case Operation(Arrow, Seq(from, to)) =>
        either(
          toInoxType(from),
          toInoxType(to)
        ){
          case (argTpe, retTpe) => trees.FunctionType(Seq(argTpe), retTpe)
        }

      case Application(l@Literal(value), irs) =>
        either(
          parametric.get(value) match {
            case None => Left(Seq(ErrorLocation("Unknown type constructor: " + value, l.pos)))
            case Some((n, cons)) => if (n == irs.length) {
              Right(cons)
            } else {
              Left(Seq(ErrorLocation("Type constructor " + value + " takes " +
                n + " " + plural(n, "argument", "arguments") + ", " +
                irs.length + " " + plural(irs.length, "was", "were") + " given.", l.pos)))
            }
          },
          traverse(irs.map(toInoxType(_))).left.map(_.flatten)
        ){
          case (cons, tpes) => cons(tpes)
        }
        
      case Literal(EmbeddedType(t)) => Right(t)

      case Literal(Name(BVType(size))) => Right(trees.BVType(size))

      case l@Literal(value) => basic.get(value) match {
        case None => Left(Seq(ErrorLocation("Unknown type: " + value, l.pos)))
        case Some(t) => Right(t)
      }

      case _ => Left(Seq(ErrorLocation("Invalid type.", expr.pos)))
    }
  }
}