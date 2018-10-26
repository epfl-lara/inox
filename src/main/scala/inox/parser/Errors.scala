package inox
package parser

import scala.util.parsing.input._

trait Errors {
  def withPosition(error: String): Position => String =
    (pos: Position) => error + "\n" + pos.longString

  def withPositions(error: String): Seq[Position] => String =
    (positions: Seq[Position]) => error + "\n" + positions.map(_.longString).mkString("\n")
}

trait ElaborationErrors extends Errors { self: Elaborators =>

  /* Elaboration errors: */

  import TypeClasses._
  import SimpleTypes._

  def invalidHoleType(tpe: String): Position => String =
    withPosition("Invalid argument passed to hole. Expected a value of type " + tpe + ".")

  def invalidInoxType(tpe: trees.Type): Position => String =
    withPosition("Invalid Type " + tpe + ".")

  def noTypeInScope(name: String): Position => String =
    withPosition("No type named " + name + " is available in scope.")

  def noExprInScope(name: String): Position => String =
    withPosition("No expression named " + name + " is available in scope.")

  def sortUsedAsTypeVariable(name: String): Position => String =
    withPosition(name + " is a sort, not a type variable.")

  def typeVariableUsedAsSort(name: String): Position => String =
    withPosition(name + " is a type variable, not a sort.")

  def wrongNumberOfArguments(callee: String, expected: Int, actual: Int): Position => String =
    withPosition("Wrong number of arguments for " + callee + ", expected " + expected + ", got " + actual + ".")

  def wrongNumberOfTypeArguments(callee: String, expected: Int, actual: Int): Position => String =
    withPosition("Wrong number of type arguments for " + callee + ", expected " + expected + ", got " + actual + ".")

  def invalidInoxValDef(vd: trees.ValDef): Position => String =
    withPosition("Invalid ValDef " + vd + ".")

  def functionUsedAsVariable(name: String): Position => String =
    withPosition(name + " is a function or a constructor, not a variable.")

  def identifierNotCallable(name: String): Position => String =
    withPosition(name + " is not callable.")

  def functionValuesCanNotHaveTypeParameters(name: String): Position => String =
    withPosition(name + " is a function value and therefore can not accept type parameters.")

  def identifierNotConstructor(name: String): Position => String =
    withPosition(name + " is not a constructor.")

  def invalidInoxExpr(expr: trees.Expr): Position => String =
    withPosition("Invalid Expr " + expr + ".")

  def noFieldNamed(name: String): Position => String =
    withPosition(name + " is not a known field.")

  def invalidADTConstructor(c: trees.ADTConstructor): Position => String =
    withPosition(c + " is not a valid ADTConstructor.")

  def unificationImpossible(tpe1: SimpleTypes.Type, tpe2: SimpleTypes.Type): Seq[Position] => String =
    withPositions("The type " + typeName(tpe1) + " can not be unified with the type " + typeName(tpe2) + ".")

  val ambiguousTypes: Seq[Position] => String =
    withPositions("The following positions have ambiguous types.")

  def incompatibleTypeClasses(tc1: TypeClass, tc2: TypeClass): Seq[Position] => String = (tc1, tc2) match {
    case (WithFields(fs1, _), WithFields(fs2, _)) => withPositions("No existing class has all the following fields: " + (fs1 union fs2).toSeq.mkString(", ") + ".")
    case (WithFields(_, _), _) => withPositions("Classes can not be " + typeClassName(tc2) + ".")
    case (_, WithFields(_, _)) => withPositions("Classes can not be " + typeClassName(tc1) + ".")
    case (WithIndices(_), _) => withPositions("Tuples can not be " + typeClassName(tc2) + ".")
    case (_, WithIndices(_)) => withPositions("Tuples can not be " + typeClassName(tc1) + ".")
    case (Bits(_), Bits(_)) => withPositions("Incompatible bit vector sizes.")
    case _ => withPositions("Incompatible kind of types: " + typeClassName(tc1) + " and " + typeClassName(tc2) + ".")
  }

  def notMemberOfTypeClasses(tpe: Type, tc: TypeClass): Seq[Position] => String =
    withPositions("Values of type " + typeName(tpe) + " are not " + typeClassName(tc) + ".")

  def typeClassName(tc: TypeClass): String = tc match {
    case WithFields(fs1, _) => "classes with fields " + fs1.toSeq.mkString(", ")
    case WithIndices(_) => "tuples"
    case Bits(_) => "bit vectors"
    case Integral => "integral"
    case Numeric => "numeric"
    case Comparable => "comparable"
  }

  def typeName(tpe: Type): String = tpe match {
    case UnitType() => "Unit"
    case BooleanType() => "Boolean"
    case BitVectorType(s) => "Int" + s.toString
    case IntegerType() => "BigInt"
    case StringType() => "String"
    case CharType() => "Char"
    case RealType() => "Real"
    case MapType(f, t) => "Map[" + typeName(f) + ", " + typeName(t) + "]"
    case SetType(t) => "Set[" + typeName(t) + "]"
    case BagType(t) => "Bag[" + typeName(t) + "]"
    case ADTType(i, tpes) => i.name + "[" + tpes.map(typeName(_)).mkString(", ") + "]"
    case TypeParameter(i) => i.name
    case _ => "Unknown"
  }

  /* Misc: */

  val filterError: String =
    "Filter error."
}

trait ParsingErrors extends Errors { self: IRs =>

  /* Parsing errors: */

  def expected(string: String): Position => String =
    withPosition("Expected " + string + ".")

  def expectedString(string: String): Position => String =
    expected("\"" + string + "\"")

  def expectedOneOf(strings: String*): Position => String = {
    assert(strings.size >= 1)

    if (strings.size == 1) {
      expectedString(strings.head)
    }
    else {
      withPosition("Expected either " + strings.init.mkString(", ") + " or " + strings.last + ".")
    }
  }

  def expectedOneOfStrings(strings: String*): Position => String =
    expectedOneOf(strings.map(x => "\"" + x + "\""): _*)
}