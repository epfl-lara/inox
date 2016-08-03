/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

import scala.collection.BitSet

/** Expression definitions for Pure Scala.
  *
  * If you are looking for things such as function or class definitions,
  * please have a look in [[purescala.Definitions]].
  *
  * Every expression in Leon inherits from [[Expr]]. The AST definitions are simple
  * case classes, with no behaviour. In particular, they do not perform smart
  * rewriting. What you build is what you get. For example,
  * {{{
  * And(BooleanLiteral(true), Variable(id, BooleanType)) != Variable(id, BooleanType)
  * }}}
  * because the ``And`` constructor will simply build a tree without checking for
  * optimization opportunities. Unless you need exact control on the structure
  * of the trees, you should use constructors in [[purescala.Constructors]], that
  * simplify the trees they produce.
  *
  * @define encodingof Encoding of
  * @define noteBitvector (32-bit vector)
  * @define noteReal (Real)
  */
trait Expressions { self: Trees =>

  private def checkParamTypes(real: Seq[Type], formal: Seq[Type], result: Type)(implicit s: Symbols): Type = {
    if (real zip formal forall { case (real, formal) => s.isSubtypeOf(real, formal)} ) {
      result.unveilUntyped
    } else {
      //println(s"Failed to type as $result")
      //println(real map { r => s"$r: ${r.getType}"} mkString ", " )
      //println(formal map { r => s"$r: ${r.getType}" } mkString ", " )
      Untyped
    }
  }

  /** Represents an expression in Leon. */
  abstract class Expr extends Tree with Typed

  /** Trait which gets mixed-in to expressions without subexpressions */
  trait Terminal {
    self: Expr =>
  }


  /** Local assumption
    *
    * @param pred The predicate to be assumed
    * @param body The expression following `assume(pred)`
    */
  case class Assume(pred: Expr, body: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      if (pred.getType == BooleanType) body.getType
      else Untyped
    }
  }


  /** Variable
    * @param id The identifier of this variable
    */
  case class Variable(id: Identifier, tpe: Type) extends Expr with Terminal with VariableSymbol {
    /** Transforms this [[Variable]] into a [[Definitions.ValDef ValDef]] */
    def toVal = to[ValDef]
    def freshen = Variable(id.freshen, tpe)
  }


  /** $encodingof `val ... = ...; ...`
    *
    * @param vd The ValDef used in body, defined just after '''val'''
    * @param value The value assigned to the identifier, after the '''=''' sign
    * @param body The expression following the ``val ... = ... ;`` construct
    * @see [[purescala.Constructors#let purescala's constructor let]]
    */
  case class Let(vd: ValDef, value: Expr, body: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      if (s.isSubtypeOf(value.getType, vd.tpe))
        body.getType
      else {
        Untyped
      }
    }
  }

  /* Higher-order Functions */

  /** $encodingof `callee(args...)`, where [[callee]] is an expression of a function type (not a method) */
  case class Application(callee: Expr, args: Seq[Expr]) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = callee.getType match {
      case FunctionType(from, to) =>
        checkParamTypes(args.map(_.getType), from, to)
      case _ =>
        Untyped
    }
  }

  /** $encodingof `(args) => body` */
  case class Lambda(args: Seq[ValDef], body: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type =
      FunctionType(args.map(_.getType), body.getType).unveilUntyped

    def paramSubst(realArgs: Seq[Expr]) = {
      require(realArgs.size == args.size)
      (args zip realArgs).toMap
    }

    def withParamSubst(realArgs: Seq[Expr], e: Expr) = {
      exprOps.replaceFromSymbols(paramSubst(realArgs), e)
    }
  }

  /* Universal Quantification */

  case class Forall(args: Seq[ValDef], body: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = body.getType
  }

  /* Control flow */

  /** $encodingof  `function(...)` (function invocation) */
  case class FunctionInvocation(id: Identifier, tps: Seq[Type], args: Seq[Expr]) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = s.lookupFunction(id) match {
      case Some(fd) =>
        val tfd = fd.typed(tps)
        require(args.size == tfd.params.size)
        checkParamTypes(args.map(_.getType), tfd.params.map(_.getType), tfd.returnType)
      case _ => Untyped
    }
  }

  /** $encodingof `if(...) ... else ...` */
  case class IfExpr(cond: Expr, thenn: Expr, elze: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = 
      s.leastUpperBound(thenn.getType, elze.getType).getOrElse(Untyped).unveilUntyped
  }


  /** Literals */

  sealed abstract class Literal[+T] extends Expr with Terminal {
    val value: T
  }

  /** $encodingof a character literal */
  case class CharLiteral(value: Char) extends Literal[Char] {
    def getType(implicit s: Symbols): Type = CharType
  }

  /** $encodingof a n-bit bitvector literal */
  case class BVLiteral(value: BitSet, size: Int) extends Literal[BitSet] {
    def getType(implicit s: Symbols): Type = BVType(size)
    def toBigInt: BigInt = {
      val res = value.foldLeft(BigInt(0))((res, i) => res + BigInt(2).pow(i))
      if (value(size)) BigInt(2).pow(size) - res else res
    }
  }

  object BVLiteral {
    def apply(bi: BigInt, size: Int): BVLiteral = BVLiteral(
      (1 to size).foldLeft(BitSet.empty) { case (res, i) =>
        if ((bi & BigInt(2).pow(i)) > 0) res + i else res
      }, size)
  }

  object IntLiteral {
    def apply(i: Int): BVLiteral = BVLiteral(BigInt(i), 32)
    def unapply(e: Expr): Option[Int] = e match {
      case b @ BVLiteral(_, 32) => Some(b.toBigInt.toInt)
      case _ => None
    }
  }

  /** $encodingof an infinite precision integer literal */
  case class IntegerLiteral(value: BigInt) extends Literal[BigInt] {
    def getType(implicit s: Symbols): Type = IntegerType
  }

  /** $encodingof a fraction literal */
  case class FractionLiteral(numerator: BigInt, denominator: BigInt) extends Literal[(BigInt, BigInt)] {
    val value = (numerator, denominator)
    def getType(implicit s: Symbols): Type = RealType
  }

  /** $encodingof a boolean literal '''true''' or '''false''' */
  case class BooleanLiteral(value: Boolean) extends Literal[Boolean] {
    def getType(implicit s: Symbols): Type = BooleanType
  }

  /** $encodingof the unit literal `()` */
  case class UnitLiteral() extends Literal[Unit] {
    val value = ()
    def getType(implicit s: Symbols): Type = UnitType
  }

  /** $encodingof a string literal */
  case class StringLiteral(value: String) extends Literal[String] {
    def getType(implicit s: Symbols): Type = StringType
  }


  /** Generic values. Represent values of the generic type `tp`.
    * This is useful e.g. to present counterexamples of generic types.
    */
  case class GenericValue(tp: TypeParameter, id: Int) extends Expr with Terminal {
    def getType(implicit s: Symbols): Type = tp
  }


  /** $encodingof `ct(args...)`
    *
    * @param ct The case class name and inherited attributes
    * @param args The arguments of the case class
    */
  case class CaseClass(ct: ClassType, args: Seq[Expr]) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = ct.lookupClass match {
      case Some(tcd: TypedCaseClassDef) => checkParamTypes(args.map(_.getType), tcd.fieldsTypes, ct)
      case _ => Untyped
    }
  }

  /** $encodingof `.isInstanceOf[...]` */
  case class IsInstanceOf(expr: Expr, classType: ClassType) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type =
      if (s.isSubtypeOf(expr.getType, classType)) BooleanType else Untyped
  }

  /** $encodingof `expr.asInstanceOf[tpe]`
    *
    * Introduced by matchToIfThenElse to transform match-cases to type-correct
    * if bodies.
    */
  case class AsInstanceOf(expr: Expr, tpe: ClassType) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type =
      if (s.typesCompatible(tpe, expr.getType)) tpe else Untyped
  }

  /** $encodingof `value.selector` where value is of a case class type
    *
    * If you are not sure about the requirement you should use
    * [[purescala.Constructors#caseClassSelector purescala's constructor caseClassSelector]]
    */
  case class CaseClassSelector(caseClass: Expr, selector: Identifier) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = caseClass.getType match {
      case ct: ClassType => ct.lookupClass match {
        case Some(tcd: TypedCaseClassDef) =>
          val index = tcd.cd.selectorID2Index(selector)
          tcd.fieldsTypes(index)
        case _ => Untyped
      }
      case _ => Untyped
    }
  }

  /** $encodingof `... == ...` */
  case class Equals(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      if (s.typesCompatible(lhs.getType, rhs.getType)) BooleanType
      else {
        //println(s"Incompatible argument types: arguments: ($lhs, $rhs) types: ${lhs.getType}, ${rhs.getType}")
        Untyped
      }
    }
  }


  /* Propositional logic */

  /** $encodingof `... && ...`
    *
    * [[exprs]] must contain at least two elements; if you are not sure about this,
    * you should use [[purescala.Constructors#and purescala's constructor and]]
    * or [[purescala.Constructors#andJoin purescala's constructor andJoin]]
    */
  case class And(exprs: Seq[Expr]) extends Expr with CachingTyped {
    require(exprs.size >= 2)
    protected def computeType(implicit s: Symbols): Type = {
      if (exprs forall (_.getType == BooleanType)) BooleanType
      else bitVectorType(exprs.head.getType, exprs.tail.map(_.getType) : _*)
    }
  }

  object And {
    def apply(a: Expr, b: Expr): Expr = And(Seq(a, b))
  }

  /** $encodingof `... || ...`
    *
    * [[exprs]] must contain at least two elements; if you are not sure about this,
    * you should use [[purescala.Constructors#or purescala's constructor or]] or
    * [[purescala.Constructors#orJoin purescala's constructor orJoin]]
    */
  case class Or(exprs: Seq[Expr]) extends Expr with CachingTyped {
    require(exprs.size >= 2)
    protected def computeType(implicit s: Symbols): Type = {
      if (exprs forall (_.getType == BooleanType)) BooleanType
      else bitVectorType(exprs.head.getType, exprs.tail.map(_.getType) : _*)
    }
  }

  object Or {
    def apply(a: Expr, b: Expr): Expr = Or(Seq(a, b))
  }

  /** $encodingof `... ==> ...` (logical implication).
    *
    * This is not a standard Scala operator, but it results from an implicit
    * conversion in the Leon library.
    *
    * @see [[leon.purescala.Constructors.implies]]
    */
  case class Implies(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      if(lhs.getType == BooleanType && rhs.getType == BooleanType) BooleanType
      else Untyped
    }
  }

  /** $encodingof `!...`
    *
    * @see [[leon.purescala.Constructors.not]]
    */
  case class Not(expr: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      if (expr.getType == BooleanType) BooleanType
      else bitVectorType(expr.getType)
    }
  }


  /* String Theory */

  /** $encodingof `lhs + rhs` for strings */
  case class StringConcat(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      if (lhs.getType == StringType && rhs.getType == StringType) StringType
      else Untyped
    }
  }

  /** $encodingof `lhs.subString(start, end)` for strings */
  case class SubString(expr: Expr, start: Expr, end: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      val ext = expr.getType
      val st = start.getType
      val et = end.getType
      if (ext == StringType && st == IntegerType && et == IntegerType) StringType
      else Untyped
    }
  }

  /** $encodingof `lhs.length` for strings */
  case class StringLength(expr: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      if (expr.getType == StringType) IntegerType
      else Untyped
    }
  }

  /* General arithmetic */

  def numericType(tpe: Type, tpes: Type*)(implicit s: Symbols): Type = {
    lazy val intType = integerType(tpe, tpes : _*)
    lazy val bvType = bitVectorType(tpe, tpes : _*)
    lazy val rlType = realType(tpe, tpes : _*)
    if (intType.isTyped) intType else if (bvType.isTyped) bvType else rlType
  }

  def integerType(tpe: Type, tpes: Type*)(implicit s: Symbols): Type = tpe match {
    case IntegerType if s.typesCompatible(tpe, tpes : _*) => tpe
    case _ => Untyped
  }

  def bitVectorType(tpe: Type, tpes: Type*)(implicit s: Symbols): Type = tpe match {
    case _: BVType if s.typesCompatible(tpe, tpes: _*) => tpe
    case _ => Untyped
  }

  def realType(tpe: Type, tpes: Type*)(implicit s: Symbols): Type = tpe match {
    case RealType if s.typesCompatible(tpe, tpes : _*) => tpe
    case _ => Untyped
  }

  /** $encodingof `... +  ...` for BigInts */
  case class Plus(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = numericType(lhs.getType, rhs.getType)
  }

  /** $encodingof `... -  ...` */
  case class Minus(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = numericType(lhs.getType, rhs.getType)
  }

  /** $encodingof `- ... for BigInts`*/
  case class UMinus(expr: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = numericType(expr.getType)
  }

  /** $encodingof `... * ...` */
  case class Times(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = numericType(lhs.getType, rhs.getType)
  }

  /** $encodingof `... /  ...`
    *
    * Division and Remainder follows Java/Scala semantics. Division corresponds
    * to / operator on BigInt and Remainder corresponds to %. Note that in
    * Java/Scala % is called remainder and the "mod" operator (Modulo in Leon) is also
    * defined on BigInteger and differs from Remainder. The "mod" operator
    * returns an always positive remainder, while Remainder could return
    * a negative remainder. The following must hold:
    *
    *    Division(x, y) * y + Remainder(x, y) == x
    */
  case class Division(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = numericType(lhs.getType, rhs.getType)
  }

  /** $encodingof `... %  ...` (can return negative numbers)
    *
    * @see [[Expressions.Division]]
    */
  case class Remainder(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = integerType(lhs.getType, rhs.getType) match {
      case Untyped => bitVectorType(lhs.getType, rhs.getType)
      case tpe => tpe
    }
  }

  /** $encodingof `... mod  ...` (cannot return negative numbers)
    *
    * @see [[Expressions.Division]]
    */
  case class Modulo(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = integerType(lhs.getType, rhs.getType) match {
      case Untyped => bitVectorType(lhs.getType, rhs.getType)
      case tpe => tpe
    }
  }

  /** $encodingof `... < ...`*/
  case class LessThan(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type =
      if (numericType(lhs.getType, rhs.getType) != Untyped) BooleanType else Untyped
  }

  /** $encodingof `... > ...`*/
  case class GreaterThan(lhs: Expr, rhs: Expr) extends Expr with CachingTyped{
    protected def computeType(implicit s: Symbols): Type =
      if (numericType(lhs.getType, rhs.getType) != Untyped) BooleanType else Untyped
  }

  /** $encodingof `... <= ...`*/
  case class LessEquals(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type =
      if (numericType(lhs.getType, rhs.getType) != Untyped) BooleanType else Untyped
  }

  /** $encodingof `... >= ...`*/
  case class GreaterEquals(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type =
      if (numericType(lhs.getType, rhs.getType) != Untyped) BooleanType else Untyped
  }


  /* Bit-vector operations */

  /** $encodingof `... ^ ...` $noteBitvector */
  case class BVXOr(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = bitVectorType(lhs.getType, rhs.getType)
  }

  /** $encodingof `... << ...` $noteBitvector */
  case class BVShiftLeft(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = bitVectorType(lhs.getType, rhs.getType)
  }

  /** $encodingof `... >> ...` $noteBitvector (arithmetic shift, sign-preserving) */
  case class BVAShiftRight(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = bitVectorType(lhs.getType, rhs.getType)
  }

  /** $encodingof `... >>> ...` $noteBitvector (logical shift) */
  case class BVLShiftRight(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = bitVectorType(lhs.getType, rhs.getType)
  }


  /* Tuple operations */

  /** $encodingof `(..., ....)` (tuple)
    *
    * [[exprs]] should always contain at least 2 elements.
    * If you are not sure about this requirement, you should use
    * [[leon.purescala.Constructors.tupleWrap purescala's constructor tupleWrap]]
    *
    * @param exprs The expressions in the tuple
    */
  case class Tuple(exprs: Seq[Expr]) extends Expr with CachingTyped {
    require(exprs.size >= 2)
    protected def computeType(implicit s: Symbols): Type = TupleType(exprs.map(_.getType)).unveilUntyped
  }

  /** $encodingof `(tuple)._i`
    *
    * Index is 1-based, first element of tuple is 1.
    * If you are not sure that [[tuple]] is indeed of a TupleType,
    * you should use [[leon.purescala.Constructors.tupleSelect(t:leon\.purescala\.Expressions\.Expr,index:Int,isTuple:Boolean):leon\.purescala\.Expressions\.Expr* purescala's constructor tupleSelect]]
    */
  case class TupleSelect(tuple: Expr, index: Int) extends Expr with CachingTyped {
    require(index >= 1)

    protected def computeType(implicit s: Symbols): Type = tuple.getType match {
      case tp @ TupleType(ts) =>
        require(index <= ts.size, s"Got index $index for '$tuple' of type '$tp")
        ts(index - 1)
      case _ => Untyped
    }
  }


  /* Set operations */

  /** $encodingof `Set[base](elements)` */
  case class FiniteSet(elements: Seq[Expr], base: Type) extends Expr {
    private lazy val tpe = SetType(base).unveilUntyped
    def getType(implicit s: Symbols): Type = tpe
  }

  /** $encodingof `set + elem` */
  case class SetAdd(set: Expr, elem: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      val base = set.getType match {
        case SetType(base) => base
        case _ => Untyped
      }
      checkParamTypes(Seq(elem.getType), Seq(base), SetType(base).unveilUntyped)
    }
  }

  /** $encodingof `set.contains(element)` or `set(element)` */
  case class ElementOfSet(element: Expr, set: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols) = checkParamTypes(Seq(element.getType), Seq(set.getType match {
      case SetType(base) => base
      case _ => Untyped
    }), BooleanType)
  }

  /** $encodingof `set.length` */
  case class SetCardinality(set: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = set.getType match {
      case SetType(_) => IntegerType
      case _ => Untyped
    }
  }

  /** $encodingof `set.subsetOf(set2)` */
  case class SubsetOf(set1: Expr, set2: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = (set1.getType, set2.getType) match {
      case (SetType(b1), SetType(b2)) if b1 == b2 => BooleanType
      case _ => Untyped
    }
  }

  /** $encodingof `set & set2` */
  case class SetIntersection(set1: Expr, set2: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type =
      s.leastUpperBound(Seq(set1, set2).map(_.getType)).getOrElse(Untyped).unveilUntyped
  }

  /** $encodingof `set ++ set2` */
  case class SetUnion(set1: Expr, set2: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type =
      s.leastUpperBound(Seq(set1, set2).map(_.getType)).getOrElse(Untyped).unveilUntyped
  }

  /** $encodingof `set -- set2` */
  case class SetDifference(set1: Expr, set2: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type =
      s.leastUpperBound(Seq(set1, set2).map(_.getType)).getOrElse(Untyped).unveilUntyped
  }


  /* Bag operations */

  /** $encodingof `Bag[base](elements)` */
  case class FiniteBag(elements: Seq[(Expr, Expr)], base: Type) extends Expr {
    lazy val tpe = BagType(base).unveilUntyped
    def getType(implicit s: Symbols): Type = tpe
  }

  /** $encodingof `bag + elem` */
  case class BagAdd(bag: Expr, elem: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      val base = bag.getType match {
        case BagType(base) => base
        case _ => Untyped
      }
      checkParamTypes(Seq(base), Seq(elem.getType), BagType(base).unveilUntyped)
    }
  }

  /** $encodingof `bag.get(element)` or `bag(element)` */
  case class MultiplicityInBag(element: Expr, bag: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = checkParamTypes(Seq(element.getType), Seq(bag.getType match {
      case BagType(base) => base
      case _ => Untyped
    }), IntegerType)
  }

  /** $encodingof `bag1 & bag2` */
  case class BagIntersection(bag1: Expr, bag2: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type =
      s.leastUpperBound(Seq(bag1, bag2).map(_.getType)).getOrElse(Untyped).unveilUntyped
  }

  /** $encodingof `bag1 ++ bag2` */
  case class BagUnion(bag1: Expr, bag2: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type =
      s.leastUpperBound(Seq(bag1, bag2).map(_.getType)).getOrElse(Untyped).unveilUntyped
  }

  /** $encodingof `bag1 -- bag2` */
  case class BagDifference(bag1: Expr, bag2: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type =
      s.leastUpperBound(Seq(bag1, bag2).map(_.getType)).getOrElse(Untyped).unveilUntyped
  }


  /* Total map operations */

  /** $encodingof `Map[keyType, valueType](key1 -> value1, key2 -> value2 ...)` */
  case class FiniteMap(pairs: Seq[(Expr, Expr)], default: Expr, keyType: Type) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type =
      MapType(keyType, default.getType).unveilUntyped
  }

  /** $encodingof `map.apply(key)` (or `map(key)`)*/
  case class MapApply(map: Expr, key: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = map.getType match {
      case MapType(from, to) => checkParamTypes(Seq(key.getType), Seq(from), to)
      case _ => Untyped
    }
  }
}
