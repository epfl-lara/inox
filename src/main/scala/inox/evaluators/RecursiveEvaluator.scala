/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package evaluators

import scala.collection.BitSet

trait RecursiveEvaluator
  extends ContextualEvaluator
     with DeterministicEvaluator
     with SolvingEvaluator {

  import context._
  import program._
  import program.trees._
  import program.symbols._
  import program.trees.exprOps._

  val name = "Recursive Evaluator"

  lazy val ignoreContracts = options.findOptionOrDefault(optIgnoreContracts)

  private def shift(b: BitSet, size: Int, i: Int): BitSet =
    b.map(_ + i).filter(bit => bit >= 1 && bit <= size)

  protected def finiteSet(els: Iterable[Expr], tpe: Type): FiniteSet = {
    FiniteSet(els.toSeq.distinct.sortBy(_.toString), tpe)
  }

  protected def finiteBag(els: Iterable[(Expr, Expr)], tpe: Type): FiniteBag = {
    FiniteBag(els.toMap.toSeq.filter { case (_, IntegerLiteral(i)) => i > 0 case _ => false }.sortBy(_._1.toString), tpe)
  }

  protected def finiteMap(els: Iterable[(Expr, Expr)], default: Expr, from: Type, to: Type): FiniteMap = {
    FiniteMap(els.toMap.toSeq.filter { case (_, value) => value != default }.sortBy(_._1.toString), default, from, to)
  }

  protected[evaluators] def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
    case v: Variable =>
      rctx.mappings.get(v.toVal) match {
        case Some(v) => v
        case None => throw EvalError("No value for variable " + v + " in mapping " + rctx.mappings)
      }

    case Application(caller, args) =>
      e(caller) match {
        case l @ Lambda(params, body) =>
          val newArgs = args.map(e)
          val mapping = l.paramSubst(newArgs)
          e(body)(rctx.withNewVars(mapping), gctx)
        case f =>
          throw EvalError("Cannot apply non-lambda function " + f.asString)
      }

    case Tuple(ts) =>
      val tsRec = ts.map(e)
      Tuple(tsRec)

    case TupleSelect(t, i) =>
      val Tuple(rs) = e(t)
      rs(i-1)

    case Let(i,ex,b) =>
      val first = e(ex)
      e(b)(rctx.withNewVar(i, first), gctx)

    case Assume(cond, body) =>
      if (!ignoreContracts && e(cond) != BooleanLiteral(true))
        throw RuntimeError("Assumption did not hold @" + expr.getPos) 
      e(body)

    case IfExpr(cond, thenn, elze) =>
      val first = e(cond)
      first match {
        case BooleanLiteral(true) => e(thenn)
        case BooleanLiteral(false) => e(elze)
        case _ => throw EvalError(typeErrorMsg(first, BooleanType()))
      }

    case FunctionInvocation(id, tps, args) =>
      if (gctx.stepsLeft < 0) {
        throw RuntimeError("Exceeded number of allocated methods calls ("+gctx.maxSteps+")")
      }
      gctx.stepsLeft -= 1

      val tfd = getFunction(id, tps)
      val evArgs = args map e

      // build a mapping for the function...
      val frame = rctx.withNewVars(tfd.paramSubst(evArgs)).newTypes(tps)

      e(tfd.fullBody)(frame, gctx)

    case And(Seq(e1, e2)) => e(e1) match {
      case BooleanLiteral(false) => BooleanLiteral(false)
      case BooleanLiteral(true) => e(e2)
      case le => throw EvalError("Unexpected operation (" + le.asString + ") && (" + e2.asString + ")")
    }

    case And(args) =>
      e(And(args.head, And(args.tail)))

    case Or(Seq(e1, e2)) => e(e1) match {
      case BooleanLiteral(true) => BooleanLiteral(true)
      case BooleanLiteral(false) => e(e2)
      case le => throw EvalError("Unexpected operation (" + le.asString + ") || (" + e2.asString + ")")
    }

    case Or(args) =>
      e(Or(args.head, Or(args.tail)))

    case Not(arg) =>
      e(arg) match {
        case BooleanLiteral(v) => BooleanLiteral(!v)
        case other => throw EvalError(typeErrorMsg(other, BooleanType()))
      }

    case Implies(l,r) =>
      e(l) match {
        case BooleanLiteral(false) => BooleanLiteral(true)
        case BooleanLiteral(true) => e(r)
        case le => throw EvalError(typeErrorMsg(le, BooleanType()))
      }

    case Equals(le,re) =>
      BooleanLiteral(e(le) == e(re))

    case ADT(id, tps, args) =>
      val cc = ADT(id, tps.map(_.getType), args.map(e))
      if (!ignoreContracts) {
        val sort = cc.getConstructor.sort
        sort.invariant.foreach { tfd =>
          val v = Variable.fresh("x", ADTType(sort.id, sort.tps), true)
          e(tfd.applied(Seq(v)))(rctx.withNewVar(v.toVal, cc), gctx) match {
            case BooleanLiteral(true) =>
            case BooleanLiteral(false) =>
              throw RuntimeError("ADT invariant violation for " + cc.asString)
            case other =>
              throw RuntimeError("Invariant type error: " + typeErrorMsg(other, BooleanType()))
          }
        }
      }
      cc

    case IsConstructor(expr, id) => e(expr) match {
      case ADT(`id`, _, _) => BooleanLiteral(true)
      case _ => BooleanLiteral(false)
    }

    case ADTSelector(expr, sel) =>
      e(expr) match {
        case adt @ ADT(id, tps, args) =>
          if (adt.getConstructor.fields.exists(_.id == sel))
            args(adt.getConstructor.definition.selectorID2Index(sel))
          else throw EvalError(s"Constructor ${id.asString} has no field ${sel.asString}")
        case le =>
          throw EvalError(typeErrorMsg(le, expr.getType))
      }

    case Plus(l,r) =>
      (e(l), e(r)) match {
        case (BVLiteral(sig1, i1, s1), BVLiteral(sig2, i2, s2)) if sig1 == sig2 && s1 == s2 =>
          BVLiteral(sig1, (1 to s1).foldLeft((BitSet.empty, false)) { case ((res, carry), i) =>
            val (b1, b2) = (i1(i), i2(i))
            val nextCarry = (b1 && b2) || (b1 && carry) || (b2 && carry)
            val ri = b1 ^ b2 ^ carry
            (if (ri) res + i else res, nextCarry)
          }._1, s1)
        case (IntegerLiteral(i1), IntegerLiteral(i2)) => IntegerLiteral(i1 + i2)
        case (FractionLiteral(ln, ld), FractionLiteral(rn, rd)) =>
          normalizeFraction(FractionLiteral(ln * rd + rn * ld, ld * rd))
        case (le,re) => throw EvalError("Unexpected operation: (" + le.asString + ") + (" + re.asString + ")")
      }

    case Minus(l,r) =>
      (e(l), e(r)) match {
        case (b1: BVLiteral, b2: BVLiteral) => e(Plus(b1, UMinus(b2)))
        case (IntegerLiteral(i1), IntegerLiteral(i2)) => IntegerLiteral(i1 - i2)
        case (FractionLiteral(ln, ld), FractionLiteral(rn, rd)) =>
          normalizeFraction(FractionLiteral(ln * rd - rn * ld, ld * rd))
        case (le,re) => throw EvalError("Unexpected operation: (" + le.asString + ") - (" + re.asString + ")")
      }

    case StringConcat(l, r) =>
      (e(l), e(r)) match {
        case (StringLiteral(i1), StringLiteral(i2)) => StringLiteral(i1 + i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, StringType()))
      }

    case StringLength(a) => e(a) match {
      case StringLiteral(a) => IntegerLiteral(a.length)
      case res => throw EvalError(typeErrorMsg(res, Int32Type()))
    }

    case SubString(a, start, end) => (e(a), e(start), e(end)) match {
      case (StringLiteral(a), IntegerLiteral(b), IntegerLiteral(c))  =>
        StringLiteral(a.substring(b.toInt, c.toInt))
      case res => throw EvalError(typeErrorMsg(res._1, StringType()))
    }

    case UMinus(ex) =>
      e(ex) match {
        case b @ BVLiteral(sig, _, s) =>
          BVLiteral(sig, if (sig) -b.toBigInt else BigInt(2).pow(s) - b.toBigInt, s)
        case IntegerLiteral(i) => IntegerLiteral(-i)
        case FractionLiteral(n, d) => FractionLiteral(-n, d)
        case re => throw EvalError("Unexpected operation: -(" + re.asString + ")")
      }

    case Times(l,r) =>
      (e(l), e(r)) match {
        case (BVLiteral(sig1, i1, s1), BVLiteral(sig2, i2, s2)) if sig1 == sig2 && s1 == s2 =>
          i1.foldLeft(BVLiteral(sig1, 0, s1): Expr) { case (res, i) =>
            e(Plus(res, BVLiteral(sig1, shift(i2, s2, i-1), s1)))
          }
        case (IntegerLiteral(i1), IntegerLiteral(i2)) => IntegerLiteral(i1 * i2)
        case (FractionLiteral(ln, ld), FractionLiteral(rn, rd)) =>
          normalizeFraction(FractionLiteral((ln * rn), (ld * rd)))
        case (le,re) => throw EvalError("Unexpected operation: (" + le.asString + ") * (" + re.asString + ")")
      }

    case Division(l,r) =>
      (e(l), e(r)) match {
        case (b1 @ BVLiteral(sig1, _, s1), b2 @ BVLiteral(sig2, _, s2)) if sig1 == sig2 && s1 == s2 =>
          val bi2 = b2.toBigInt
          if (bi2 != 0) BVLiteral(sig1, b1.toBigInt / bi2, s1) else throw RuntimeError("Division by 0.")
        case (IntegerLiteral(i1), IntegerLiteral(i2)) =>
          if(i2 != BigInt(0)) IntegerLiteral(i1 / i2) else throw RuntimeError("Division by 0.")
        case (FractionLiteral(ln, ld), FractionLiteral(rn, rd)) =>
          if (rn != 0)
            normalizeFraction(FractionLiteral(ln * rd, ld * rn))
          else throw RuntimeError("Division by 0.")
        case (le,re) => throw EvalError("Unexpected operation: (" + le.asString + ") / (" + re.asString + ")")
      }

    case Remainder(l,r) =>
      (e(l), e(r)) match {
        case (b1 @ BVLiteral(sig1, _, s1), b2 @ BVLiteral(sig2, _, s2)) if sig1 == sig2 && s1 == s2 =>
          val bi2 = b2.toBigInt
          if (bi2 != 0) BVLiteral(sig1, b1.toBigInt % bi2, s1) else throw RuntimeError("Division by 0.")
        case (IntegerLiteral(i1), IntegerLiteral(i2)) =>
          if(i2 != BigInt(0)) IntegerLiteral(i1 % i2) else throw RuntimeError("Remainder of division by 0.")
        case (le,re) => throw EvalError("Unexpected operation: (" + le.asString + ") rem (" + re.asString + ")")
      }

    case Modulo(l,r) =>
      (e(l), e(r)) match {
        case (b1 @ BVLiteral(sig1, _, s1), b2 @ BVLiteral(sig2, _, s2)) if sig1 == sig2 && s1 == s2 =>
          val bi2 = b2.toBigInt
          if (bi2 < 0) {
            assert(sig1, "Only signed bitvectors can contain negative values.")
            BVLiteral(true, b1.toBigInt mod (-bi2), s1)
          } else if (bi2 != 0) {
            BVLiteral(sig1, b1.toBigInt mod bi2, s1)
          } else {
            throw RuntimeError("Modulo of division by 0.")
          }
        case (IntegerLiteral(i1), IntegerLiteral(i2)) =>
          if(i2 < 0)
            IntegerLiteral(i1 mod (-i2))
          else if(i2 != BigInt(0))
            IntegerLiteral(i1 mod i2)
          else
            throw RuntimeError("Modulo of division by 0.")
        case (le,re) => throw EvalError("Unexpected operation: (" + le.asString + ") % (" + re.asString + ")")
      }

    case BVNot(b) =>
      e(b) match {
        case BVLiteral(signed, bs, s) =>
          BVLiteral(signed, BitSet.empty ++ (1 to s).flatMap(i => if (bs(i)) None else Some(i)), s)
        case other => throw EvalError("Unexpected operation: ~(" + other.asString + ")")
      }

    case BVAnd(l, r) =>
      (e(l), e(r)) match {
        case (BVLiteral(sig1, i1, s1), BVLiteral(sig2, i2, s2)) if sig1 == sig2 && s1 == s2 => BVLiteral(sig1, i1 & i2, s1)
        case (le, re) => throw EvalError("Unexpected operation: (" + le.asString + ") & (" + re.asString + ")")
      }

    case BVOr(l, r) =>
      (e(l), e(r)) match {
        case (BVLiteral(sig1, i1, s1), BVLiteral(sig2, i2, s2)) if sig1 == sig2 && s1 == s2 => BVLiteral(sig1, i1 | i2, s1)
        case (le, re) => throw EvalError("Unexpected operation: (" + le.asString + ") | (" + re.asString + ")")
      }

    case BVXor(l,r) =>
      (e(l), e(r)) match {
        case (BVLiteral(sig1, i1, s1), BVLiteral(sig2, i2, s2)) if sig1 == sig2 && s1 == s2 => BVLiteral(sig1, i1 ^ i2, s1)
        case (le,re) => throw EvalError("Unexpected operation: (" + le.asString + ") ^ (" + re.asString + ")")
      }

    case BVShiftLeft(l,r) =>
      (e(l), e(r)) match {
        case (BVLiteral(sig1, i1, s1), b2 @ BVLiteral(sig2, _, s2)) if sig1 == sig2 && s1 == s2 =>
          BVLiteral(sig1, shift(i1, s1, b2.toBigInt.toInt), s1)
        case (le,re) => throw EvalError("Unexpected operation: (" + le.asString + ") << (" + re.asString + ")")
      }

    case BVAShiftRight(l,r) =>
      (e(l), e(r)) match {
        case (BVLiteral(sig1, i1, s1), b2 @ BVLiteral(sig2, _, s2)) if sig1 == sig2 && s1 == s2 =>
          val shiftCount = b2.toBigInt.toInt
          val shifted = shift(i1, s1, -shiftCount)
          BVLiteral(sig1, if (i1(s1)) shifted ++ ((s1 - shiftCount) to s1) else shifted, s1)
        case (le,re) => throw EvalError("Unexpected operation: (" + le.asString + ") >> (" + re.asString + ")")
      }

    case BVLShiftRight(l,r) =>
      (e(l), e(r)) match {
        case (BVLiteral(sig1, i1, s1), b2 @ BVLiteral(sig2, _, s2)) if s1 == s2 && sig1 == sig2 =>
          BVLiteral(sig1, shift(i1, s1, -b2.toBigInt.toInt), s1)
        case (le,re) => throw EvalError("Unexpected operation: (" + le.asString + ") >>> (" + re.asString + ")")
      }

    case BVNarrowingCast(expr, bvt) =>
      e(expr) match {
        case bv @ BVLiteral(signed, _, _) => BVLiteral(signed, bv.toBigInt, bvt.size)
        case x => throw EvalError(typeErrorMsg(x, BVType(bvt.signed, bvt.size + 1))) // or any larger BVType
      }

    case BVWideningCast(expr, bvt) =>
      e(expr) match {
        case bv @ BVLiteral(signed, _, _) => BVLiteral(signed, bv.toBigInt, bvt.size)
        case x => throw EvalError(typeErrorMsg(x, BVType(bvt.signed, bvt.size - 1))) // or any smaller BVType
      }

    case BVUnsignedToSigned(expr) =>
      e(expr) match {
        case BVLiteral(false, bits, size) => BVLiteral(true, bits, size)
        case x => throw EvalError("Expected unsigned bitvector type")
      }

    case BVSignedToUnsigned(expr) =>
      e(expr) match {
        case BVLiteral(true, bits, size) => BVLiteral(false, bits, size)
        case x => throw EvalError("Expected signed bitvector type")
      }

    case LessThan(l,r) =>
      (e(l), e(r)) match {
        case (b1 @ BVLiteral(sig1, _, s1), b2 @ BVLiteral(sig2, _, s2)) if sig1 == sig2 && s1 == s2 =>
          BooleanLiteral(b1.toBigInt < b2.toBigInt)
        case (IntegerLiteral(i1), IntegerLiteral(i2)) => BooleanLiteral(i1 < i2)
        case (a @ FractionLiteral(_, _), b @ FractionLiteral(_, _)) =>
          val FractionLiteral(n, _) = e(Minus(a, b))
          BooleanLiteral(n < 0)
        case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 < c2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type()))
      }

    case GreaterThan(l,r) =>
      (e(l), e(r)) match {
        case (b1 @ BVLiteral(sig1, _, s1), b2 @ BVLiteral(sig2, _, s2)) if sig1 == sig2 && s1 == s2 =>
          BooleanLiteral(b1.toBigInt > b2.toBigInt)
        case (IntegerLiteral(i1), IntegerLiteral(i2)) => BooleanLiteral(i1 > i2)
        case (a @ FractionLiteral(_, _), b @ FractionLiteral(_, _)) =>
          val FractionLiteral(n, _) = e(Minus(a, b))
          BooleanLiteral(n > 0)
        case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 > c2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type()))
      }

    case LessEquals(l,r) =>
      (e(l), e(r)) match {
        case (b1 @ BVLiteral(sig1, _, s1), b2 @ BVLiteral(sig2, _, s2)) if sig1 == sig2 && s1 == s2 =>
          BooleanLiteral(b1.toBigInt <= b2.toBigInt)
        case (IntegerLiteral(i1), IntegerLiteral(i2)) => BooleanLiteral(i1 <= i2)
        case (a @ FractionLiteral(_, _), b @ FractionLiteral(_, _)) =>
          val FractionLiteral(n, _) = e(Minus(a, b))
          BooleanLiteral(n <= 0)
        case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 <= c2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type()))
      }

    case GreaterEquals(l,r) =>
      (e(l), e(r)) match {
        case (b1 @ BVLiteral(sig1, _, s1), b2 @ BVLiteral(sig2, _, s2)) if sig1 == sig2 && s1 == s2 =>
          BooleanLiteral(b1.toBigInt >= b2.toBigInt)
        case (IntegerLiteral(i1), IntegerLiteral(i2)) => BooleanLiteral(i1 >= i2)
        case (a @ FractionLiteral(_, _), b @ FractionLiteral(_, _)) =>
          val FractionLiteral(n, _) = e(Minus(a, b))
          BooleanLiteral(n >= 0)
        case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 >= c2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type()))
      }

    case SetAdd(s1, elem) =>
      (e(s1), e(elem)) match {
        case (FiniteSet(els1, tpe), evElem) => finiteSet(els1 :+ evElem, tpe)
        case (le, re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case SetUnion(s1,s2) =>
      (e(s1), e(s2)) match {
        case (FiniteSet(els1, tpe), FiniteSet(els2, _)) => finiteSet(els1 ++ els2, tpe)
        case (le, re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case SetIntersection(s1,s2) =>
      (e(s1), e(s2)) match {
        case (FiniteSet(els1, tpe), FiniteSet(els2, _)) => finiteSet(els1 intersect els2, tpe)
        case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case SetDifference(s1,s2) =>
      (e(s1), e(s2)) match {
        case (FiniteSet(els1, tpe), FiniteSet(els2, _)) => finiteSet(els1.toSet -- els2, tpe)
        case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case MapMerge(cond, map1, map2) =>
      (e(cond), e(map1), e(map2)) match {
        case (FiniteSet(keys, kT), FiniteMap(kvs1, dflt1, _, vT), FiniteMap(kvs2, dflt2, _, _)) =>
          val fromFstMap = keys.map((_ -> dflt1)).toMap ++ (kvs1.toMap.filterKeys(keys.contains(_)))
          val fromSndMap = kvs2.toMap -- keys
          finiteMap((fromFstMap ++ fromSndMap).toSeq, dflt2, kT, vT)
        case (c, m1, m2) =>
          throw EvalError(typeErrorMsg(c, cond.getType))
      }

    case ElementOfSet(el,s) => (e(el), e(s)) match {
      case (e, FiniteSet(els, _)) => BooleanLiteral(els.contains(e))
      case (l,r) => throw EvalError(typeErrorMsg(r, SetType(l.getType)))
    }

    case SubsetOf(s1,s2) => (e(s1), e(s2)) match {
      case (FiniteSet(els1, _),FiniteSet(els2, _)) => BooleanLiteral(els1.toSet.subsetOf(els2.toSet))
      case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
    }

    case f @ FiniteSet(els, base) =>
      finiteSet(els.map(e), base.getType)

    case BagAdd(bag, elem) => (e(bag), e(elem)) match {
      case (FiniteBag(els, tpe), evElem) =>
        val (matching, rest) = els.partition(_._1 == evElem)
        finiteBag(rest :+ (evElem -> matching.lastOption.map {
          case (_, IntegerLiteral(i)) => IntegerLiteral(i + 1)
          case (_, e) => throw EvalError(typeErrorMsg(e, IntegerType()))
        }.getOrElse(IntegerLiteral(1))), tpe)

      case (le, re) => throw EvalError(typeErrorMsg(le, bag.getType))
    }

    case MultiplicityInBag(elem, bag) => (e(elem), e(bag)) match {
      case (evElem, FiniteBag(els, tpe)) =>
        els.collect { case (k,v) if k == evElem => v }.lastOption.getOrElse(IntegerLiteral(0))
      case (le, re) => throw EvalError(typeErrorMsg(re, bag.getType))
    }

    case BagIntersection(b1, b2) => (e(b1), e(b2)) match {
      case (FiniteBag(els1, tpe), FiniteBag(els2, _)) =>
        val map2 = els2.toMap
        finiteBag(els1.flatMap { case (k, v) =>
          val i = (v, map2.getOrElse(k, IntegerLiteral(0))) match {
            case (IntegerLiteral(i1), IntegerLiteral(i2)) => i1 min i2
            case (le, re) => throw EvalError(typeErrorMsg(le, IntegerType()))
          }

          if (i <= 0) None else Some(k -> IntegerLiteral(i))
        }, tpe)

      case (le, re) => throw EvalError(typeErrorMsg(le, b1.getType))
    }

    case BagUnion(b1, b2) => (e(b1), e(b2)) match {
      case (FiniteBag(els1, tpe), FiniteBag(els2, _)) =>
        val (map1, map2) = (els1.toMap, els2.toMap)
        finiteBag((map1.keys ++ map2.keys).toSet.map { (k: Expr) =>
          k -> ((map1.getOrElse(k, IntegerLiteral(0)), map2.getOrElse(k, IntegerLiteral(0))) match {
            case (IntegerLiteral(i1), IntegerLiteral(i2)) => IntegerLiteral(i1 + i2)
            case (le, re) => throw EvalError(typeErrorMsg(le, IntegerType()))
          })
        }.toSeq, tpe)

      case (le, re) => throw EvalError(typeErrorMsg(le, b1.getType))
    }

    case BagDifference(b1, b2) => (e(b1), e(b2)) match {
      case (FiniteBag(els1, tpe), FiniteBag(els2, _)) =>
        val map2 = els2.toMap
        finiteBag(els1.flatMap { case (k, v) =>
          val i = (v, map2.getOrElse(k, IntegerLiteral(0))) match {
            case (IntegerLiteral(i1), IntegerLiteral(i2)) => i1 - i2
            case (le, re) => throw EvalError(typeErrorMsg(le, IntegerType()))
          }

          if (i <= 0) None else Some(k -> IntegerLiteral(i))
        }, tpe)

      case (le, re) => throw EvalError(typeErrorMsg(le, b1.getType))
    }

    case FiniteBag(els, base) =>
      finiteBag(els.map { case (k, v) => (e(k), e(v)) }, base.getType)

    case l @ Lambda(_, _) =>
      def normalizeLambda(l: Lambda, onlySimple: Boolean = false): Lambda = {
        val (nl, deps) = normalizeStructure(l, onlySimple = onlySimple)
        val newCtx = deps.foldLeft(rctx) {
          case (rctx, (v, dep, conds)) =>
            if (conds.forall(e(_)(rctx, gctx) == BooleanLiteral(true))) rctx.withNewVar(v.toVal, e(dep)(rctx, gctx))
            else rctx
        }
        val mapping = variablesOf(nl).map(v => v -> newCtx.mappings(v.toVal)).toMap
        replaceFromSymbols(mapping, nl).asInstanceOf[Lambda]
      }

      // We start by normalizing the structure of the lambda as in the solver to
      // evaluate all normalizable ground expressions within its body.
      val ground = normalizeLambda(l)

      // Then, in order for nested lambdas to have fresh variables in their argument
      // lists and let bindings, we re-normalize the identifiers by passing
      // `onlySimple = true` to the call to `normalizeStructure` (this avoids lifting
      // ground lambdas out in the deps).
      normalizeLambda(ground, onlySimple = true)

    case f: Forall => onForallInvocation {
      replaceFromSymbols(variablesOf(f).map(v => v -> e(v)).toMap, f).asInstanceOf[Forall]
    }

    case c: Choose =>
      rctx.getChoose(c.res.id) match {
        case Some(expr) => e(expr)
        case None => onChooseInvocation {
          replaceFromSymbols(variablesOf(c).map(v => v -> e(v)).toMap, c).asInstanceOf[Choose]
        }
      }

    case f @ FiniteMap(ss, dflt, kT, vT) =>
      finiteMap(ss.map{ case (k, v) => (e(k), e(v)) }, e(dflt), kT.getType, vT.getType)

    case g @ MapApply(m,k) => (e(m), e(k)) match {
      case (FiniteMap(ss, dflt, _, _), e) =>
        ss.toMap.getOrElse(e, dflt)
      case (l,r) =>
        throw EvalError(typeErrorMsg(l, MapType(r.getType, g.getType)))
    }

    case g @ MapUpdated(m, k, v) => (e(m), e(k), e(v)) match {
      case (FiniteMap(ss, dflt, kT, vT), ek, ev) =>
        finiteMap((ss.toMap + (ek -> ev)).toSeq, dflt, kT, vT)
      case (m,l,r) =>
        throw EvalError("Unexpected operation: " + m.asString +
          ".updated(" + l.asString + ", " + r.asString + ")")
    }

    case StringLiteral(str) =>
      StringLiteral(utils.StringUtils.decode(str))

    case gl: GenericValue => gl
    case fl : FractionLiteral => normalizeFraction(fl)
    case l : Literal[_] => l

    case other =>
      throw EvalError("Unhandled case in Evaluator : [" + other.getClass + "] " + other.asString)
  }
}

object RecursiveEvaluator {
  def apply(p: InoxProgram, ctx: Context): RecursiveEvaluator { val program: p.type } = {
    new {
      val program: p.type = p
      val context = ctx
    } with RecursiveEvaluator with HasDefaultGlobalContext with HasDefaultRecContext {
      val semantics: p.Semantics = p.getSemantics
    }
  }
}
