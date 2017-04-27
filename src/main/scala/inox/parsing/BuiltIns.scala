/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

trait BuiltIns { self: Interpolator =>

  lazy val bi = new DefaultBuiltIns {}

  trait BuiltInNames { 

    sealed abstract class BuiltIn(val params: Option[Int], val tparams: Int) {
      val isConstructor = false
    }

    trait Constructor { self: BuiltIn =>
      override abstract val isConstructor = true
    }

    case object AsInstanceOf extends BuiltIn(Some(1), 1)
    case object IsInstanceOf extends BuiltIn(Some(1), 1)

    case object StringConcatenate extends BuiltIn(Some(2), 0)
    case object StringLength extends BuiltIn(Some(1), 0)
    case object StringSubstring extends BuiltIn(Some(3), 0)

    case object BooleanAnd extends BuiltIn(None, 0)
    case object BooleanOr extends BuiltIn(None, 0)

    case object SetConstructor extends BuiltIn(None, 1) with Constructor
    case object SetContains extends BuiltIn(Some(2), 1)
    case object SetAdd extends BuiltIn(Some(2), 1)
    case object SetUnion extends BuiltIn(Some(2), 1)
    case object SetIntersection extends BuiltIn(Some(2), 1)
    case object SetDifference extends BuiltIn(Some(2), 1)
    case object SetSubset extends BuiltIn(Some(2), 1)

    case object BagConstructor extends BuiltIn(None, 1) with Constructor
    case object BagMultiplicity extends BuiltIn(Some(2), 1)
    case object BagAdd extends BuiltIn(Some(2), 1)
    case object BagUnion extends BuiltIn(Some(2), 1)
    case object BagIntersection extends BuiltIn(Some(2), 1)
    case object BagDifference extends BuiltIn(Some(2), 1)

    case object MapConstructor extends BuiltIn(None, 2) with Constructor
    case object MapApply extends BuiltIn(Some(2), 2)
    case object MapUpdated extends BuiltIn(Some(3), 2)

    val names: Map[String, BuiltIn]

    object BuiltIn {
      def unapply(name: String): Option[BuiltIn] = {
        names.get(name)
      }
    }
  }

  trait DefaultBuiltIns extends BuiltInNames {
    override val names: Map[String, BuiltIn] = Map(
      AsInstanceOf -> "asInstanceOf",
      IsInstanceOf -> "isInstanceOf",

      BooleanAnd -> "and",
      BooleanOr -> "or",

      StringConcatenate -> "concatenate",
      StringLength -> "length",
      StringSubstring -> "substring",

      SetConstructor -> "Set",
      SetContains -> "contains",
      SetAdd -> "add",
      SetUnion -> "union",
      SetIntersection -> "intersection",
      SetDifference -> "difference",
      SetSubset -> "subset",

      BagConstructor -> "Bag",
      BagMultiplicity -> "multiplicity",
      BagAdd -> "bagAdd",
      BagUnion -> "bagUnion",
      BagIntersection -> "bagIntersection",
      BagDifference -> "bagDifference",

      MapConstructor -> "Map",
      MapApply -> "apply",
      MapUpdated -> "updated").map(_.swap)
  }

  trait EmptyBuiltIns extends BuiltInNames {
    override val names: Map[String, BuiltIn] = Map()
  }
}