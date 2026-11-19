/* Copyright 2009-2026 EPFL, Lausanne */

// Generated from semantics.md by inox.semantics.Codegen. Do not edit: change semantics.md
// and regenerate (see proofs/README.md).

package inox.semantics.generated

import scala.language.unsafeNulls

object Semantics {
  type Id = inox.Identifier

  /** The euclidean quotient and remainder, as `div` and `mod` in the semantics; 0 and `a` for a
    * zero `b`, where the semantics leaves them unused. */
  def ediv(a: BigInt, b: BigInt): BigInt = if (b == 0) BigInt(0) else (a - emod(a, b)) / b
  def emod(a: BigInt, b: BigInt): BigInt = if (b == 0) a else a.mod(b.abs)

  sealed abstract class List[+T]
  final case class Nil() extends List[Nothing]
  final case class Cons[+T](head: T, tail: List[T]) extends List[T]

  sealed abstract class Option[+T]
  final case class None() extends Option[Nothing]
  final case class Some[+T](value: T) extends Option[T]

  sealed abstract class Result[+T]
  final case class Ok[+T](value: T) extends Result[T]
  final case class Stuck() extends Result[Nothing]
  final case class OutOfFuel() extends Result[Nothing]

  sealed abstract class Value
  final case class IntV(value: BigInt) extends Value
  final case class BoolV(value: Boolean) extends Value
  final case class UnitV() extends Value
  final case class CharV(code: BigInt) extends Value
  final case class RealV(num: BigInt, den: BigInt) extends Value
  final case class StringV(chars: List[BigInt]) extends Value
  final case class BVV(signed: Boolean, width: BigInt, bits: BigInt) extends Value
  final case class TupleV(elems: List[Value]) extends Value
  final case class ClosureV(params: List[Id], body: Expr, env: List[Binding]) extends Value
  final case class SetV(elems: List[Value]) extends Value
  final case class BagV(entries: List[BagEntry]) extends Value
  final case class MapV(entries: List[MapEntry], default: Value) extends Value
  final case class ADTV(ctor: Id, args: List[Value]) extends Value

  final case class BagEntry(elem: Value, count: BigInt)

  final case class MapEntry(key: Value, value: Value)

  sealed abstract class Expr
  final case class Assume(pred: Expr, body: Expr) extends Expr
  final case class Variable(id: Id) extends Expr
  final case class Let(id: Id, value: Expr, body: Expr) extends Expr
  final case class Application(callee: Expr, args: List[Expr]) extends Expr
  final case class Lambda(params: List[Id], body: Expr) extends Expr
  final case class Error() extends Expr
  final case class FunctionInvocation(id: Id, args: List[Expr]) extends Expr
  final case class IfExpr(cond: Expr, thenn: Expr, elze: Expr) extends Expr
  final case class CharLiteral(code: BigInt) extends Expr
  final case class BVLiteral(signed: Boolean, width: BigInt, bits: BigInt) extends Expr
  final case class IntegerLiteral(value: BigInt) extends Expr
  final case class FractionLiteral(num: BigInt, den: BigInt) extends Expr
  final case class BooleanLiteral(value: Boolean) extends Expr
  final case class StringLiteral(chars: List[BigInt]) extends Expr
  final case class UnitLiteral() extends Expr
  final case class ADT(id: Id, args: List[Expr]) extends Expr
  final case class IsConstructor(expr: Expr, id: Id) extends Expr
  final case class ADTSelector(adt: Expr, selector: Id) extends Expr
  final case class Equals(lhs: Expr, rhs: Expr) extends Expr
  final case class And(exprs: List[Expr]) extends Expr
  final case class Or(exprs: List[Expr]) extends Expr
  final case class Implies(lhs: Expr, rhs: Expr) extends Expr
  final case class Not(expr: Expr) extends Expr
  final case class StringConcat(lhs: Expr, rhs: Expr) extends Expr
  final case class SubString(expr: Expr, start: Expr, end: Expr) extends Expr
  final case class StringLength(expr: Expr) extends Expr
  final case class Plus(lhs: Expr, rhs: Expr) extends Expr
  final case class Minus(lhs: Expr, rhs: Expr) extends Expr
  final case class UMinus(expr: Expr) extends Expr
  final case class Times(lhs: Expr, rhs: Expr) extends Expr
  final case class Division(lhs: Expr, rhs: Expr) extends Expr
  final case class Remainder(lhs: Expr, rhs: Expr) extends Expr
  final case class Modulo(lhs: Expr, rhs: Expr) extends Expr
  final case class LessThan(lhs: Expr, rhs: Expr) extends Expr
  final case class GreaterThan(lhs: Expr, rhs: Expr) extends Expr
  final case class LessEquals(lhs: Expr, rhs: Expr) extends Expr
  final case class GreaterEquals(lhs: Expr, rhs: Expr) extends Expr
  final case class BVNot(expr: Expr) extends Expr
  final case class BVAnd(lhs: Expr, rhs: Expr) extends Expr
  final case class BVOr(lhs: Expr, rhs: Expr) extends Expr
  final case class BVXor(lhs: Expr, rhs: Expr) extends Expr
  final case class BVShiftLeft(lhs: Expr, rhs: Expr) extends Expr
  final case class BVAShiftRight(lhs: Expr, rhs: Expr) extends Expr
  final case class BVLShiftRight(lhs: Expr, rhs: Expr) extends Expr
  final case class BVNarrowingCast(expr: Expr, width: BigInt) extends Expr
  final case class BVWideningCast(expr: Expr, width: BigInt) extends Expr
  final case class BVUnsignedToSigned(expr: Expr) extends Expr
  final case class BVSignedToUnsigned(expr: Expr) extends Expr
  final case class BVToInt(expr: Expr) extends Expr
  final case class IntToBV(width: BigInt, signed: Boolean, expr: Expr) extends Expr
  final case class Tuple(exprs: List[Expr]) extends Expr
  final case class TupleSelect(tuple: Expr, index: BigInt) extends Expr
  final case class FiniteSet(elems: List[Expr]) extends Expr
  final case class SetAdd(set: Expr, elem: Expr) extends Expr
  final case class ElementOfSet(elem: Expr, set: Expr) extends Expr
  final case class SubsetOf(lhs: Expr, rhs: Expr) extends Expr
  final case class SetIntersection(lhs: Expr, rhs: Expr) extends Expr
  final case class SetUnion(lhs: Expr, rhs: Expr) extends Expr
  final case class SetDifference(lhs: Expr, rhs: Expr) extends Expr
  final case class FiniteBag(elems: List[ExprPair]) extends Expr
  final case class BagAdd(bag: Expr, elem: Expr) extends Expr
  final case class MultiplicityInBag(elem: Expr, bag: Expr) extends Expr
  final case class BagIntersection(lhs: Expr, rhs: Expr) extends Expr
  final case class BagUnion(lhs: Expr, rhs: Expr) extends Expr
  final case class BagDifference(lhs: Expr, rhs: Expr) extends Expr
  final case class FiniteMap(pairs: List[ExprPair], default: Expr) extends Expr
  final case class MapApply(map: Expr, key: Expr) extends Expr
  final case class MapUpdated(map: Expr, key: Expr, value: Expr) extends Expr
  final case class MapMerge(mask: Expr, map1: Expr, map2: Expr) extends Expr

  final case class ExprPair(fst: Expr, snd: Expr)

  final case class FunDef(id: Id, params: List[Id], body: Expr)

  final case class Constructor(id: Id, sort: Id, fields: List[Id])

  final case class Sort(id: Id, invariant: Option[Id])

  final case class Program(functions: List[FunDef], constructors: List[Constructor], sorts: List[Sort])

  final case class Binding(id: Id, value: Value)

  sealed abstract class BitOp
  final case class AndOp() extends BitOp
  final case class OrOp() extends BitOp
  final case class XorOp() extends BitOp
  final case class ShiftLeftOp() extends BitOp
  final case class AShiftRightOp() extends BitOp
  final case class LShiftRightOp() extends BitOp

  sealed abstract class BagOp
  final case class IntersectionOp() extends BagOp
  final case class UnionOp() extends BagOp
  final case class DifferenceOp() extends BagOp

  def lookup_var(env: List[Binding], x: Id): Result[Value] =
    (env) match {
      case Nil() => Stuck()
      case Cons(Binding(y, v), rest) => if ((x == y)) {
          Ok(v)
        } else {
          lookup_var(rest, x)
        }
    }

  def bind_all(ids: List[Id], vs: List[Value]): Result[List[Binding]] =
    (ids) match {
      case Nil() => (vs) match {
          case Nil() => Ok(Nil())
          case _ => Stuck()
        }
      case Cons(x, xs) => (vs) match {
          case Nil() => Stuck()
          case Cons(v, rest) => bind_all(xs, rest) match {
              case Ok(bs) => Ok(Cons(Binding(x, v), bs))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
        }
    }

  def lookup_fun(fs: List[FunDef], f: Id): Result[FunDef] =
    (fs) match {
      case Nil() => Stuck()
      case Cons(fd, rest) => (fd) match {
          case FunDef(g, _, _) => if ((f == g)) {
              Ok(fd)
            } else {
              lookup_fun(rest, f)
            }
        }
    }

  def lookup_ctor(cs: List[Constructor], c: Id): Result[Constructor] =
    (cs) match {
      case Nil() => Stuck()
      case Cons(k, rest) => (k) match {
          case Constructor(d, _, _) => if ((c == d)) {
              Ok(k)
            } else {
              lookup_ctor(rest, c)
            }
        }
    }

  def lookup_sort(ss: List[Sort], s: Id): Result[Sort] =
    (ss) match {
      case Nil() => Stuck()
      case Cons(srt, rest) => (srt) match {
          case Sort(t, _) => if ((s == t)) {
              Ok(srt)
            } else {
              lookup_sort(rest, s)
            }
        }
    }

  def select_field(fields: List[Id], args: List[Value], sel: Id): Result[Value] =
    (fields) match {
      case Nil() => Stuck()
      case Cons(f, fs) => (args) match {
          case Nil() => Stuck()
          case Cons(v, vs) => if ((f == sel)) {
              Ok(v)
            } else {
              select_field(fs, vs, sel)
            }
        }
    }

  def call(v_P: Program, fuel: BigInt, f: Id, vs: List[Value]): Result[Value] =
    if ((fuel <= BigInt(0))) {
      OutOfFuel()
    } else {
      (v_P) match {
        case Program(fs, _, _) => lookup_fun(fs, f) match {
            case Ok(fd) => (fd) match {
              case FunDef(_, params, body) => bind_all(params, vs) match {
                  case Ok(env) => eval(v_P, (fuel - BigInt(1)), env, body)
                  case Stuck() => Stuck()
                  case OutOfFuel() => OutOfFuel()
                }
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      }
    }

  def eval(v_P: Program, fuel: BigInt, env: List[Binding], e: Expr): Result[Value] = e match {
    case Assume(pred, body) =>
      eval_bool(v_P, fuel, env, pred) match {
        case Ok(b) => if (b) {
          eval(v_P, fuel, env, body)
        } else {
          Stuck()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case Variable(x) =>
      lookup_var(env, x)
    case Let(x, value, body) =>
      eval(v_P, fuel, env, value) match {
        case Ok(v) => eval(v_P, fuel, Cons(Binding(x, v), env), body)
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case Application(callee, args) =>
      eval(v_P, fuel, env, callee) match {
        case Ok(f) => eval_list(v_P, fuel, env, args) match {
          case Ok(vs) => (f) match {
            case ClosureV(params, body, cenv) => if ((fuel <= BigInt(0))) {
                OutOfFuel()
              } else {
                bind_all(params, vs) match {
                  case Ok(bs) => eval(v_P, (fuel - BigInt(1)), append_env(bs, cenv), body)
                  case Stuck() => Stuck()
                  case OutOfFuel() => OutOfFuel()
                }
              }
            case _ => Stuck()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case Lambda(params, body) =>
      Ok(ClosureV(params, body, env))
    case Error() =>
      Stuck()
    case FunctionInvocation(f, args) =>
      eval_list(v_P, fuel, env, args) match {
        case Ok(vs) => call(v_P, fuel, f, vs)
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case IfExpr(cond, thenn, elze) =>
      eval_bool(v_P, fuel, env, cond) match {
        case Ok(b) => if (b) {
          eval(v_P, fuel, env, thenn)
        } else {
          eval(v_P, fuel, env, elze)
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case CharLiteral(c) =>
      Ok(CharV(c))
    case BVLiteral(s, w, x) =>
      Ok(BVV(s, w, x))
    case IntegerLiteral(i) =>
      Ok(IntV(i))
    case FractionLiteral(n, d) =>
      real(n, d)
    case BooleanLiteral(b) =>
      Ok(BoolV(b))
    case StringLiteral(cs) =>
      Ok(StringV(cs))
    case UnitLiteral() =>
      Ok(UnitV())
    case ADT(c, args) =>
      eval_list(v_P, fuel, env, args) match {
        case Ok(vs) => (v_P) match {
          case Program(_, cs, ss) => lookup_ctor(cs, c) match {
              case Ok(k) => (k) match {
                case Constructor(_, s, _) => lookup_sort(ss, s) match {
                    case Ok(srt) => (srt) match {
                      case Sort(_, None()) => Ok(ADTV(c, vs))
                      case Sort(_, Some(inv)) => call(v_P, fuel, inv, Cons(ADTV(c, vs), Nil())) match {
                          case Ok(holds) => (holds) match {
                            case BoolV(true) => Ok(ADTV(c, vs))
                            case _ => Stuck()
                          }
                          case Stuck() => Stuck()
                          case OutOfFuel() => OutOfFuel()
                        }
                    }
                    case Stuck() => Stuck()
                    case OutOfFuel() => OutOfFuel()
                  }
              }
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case IsConstructor(adt, c) =>
      eval(v_P, fuel, env, adt) match {
        case Ok(v) => (v) match {
          case ADTV(d, _) => Ok(BoolV((c == d)))
          case _ => Stuck()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case ADTSelector(adt, sel) =>
      eval(v_P, fuel, env, adt) match {
        case Ok(v) => (v) match {
          case ADTV(c, vs) => (v_P) match {
              case Program(_, cs, _) => lookup_ctor(cs, c) match {
                  case Ok(k) => (k) match {
                    case Constructor(_, _, fields) => select_field(fields, vs, sel)
                  }
                  case Stuck() => Stuck()
                  case OutOfFuel() => OutOfFuel()
                }
            }
          case _ => Stuck()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case Equals(lhs, rhs) =>
      eval(v_P, fuel, env, lhs) match {
        case Ok(a) => eval(v_P, fuel, env, rhs) match {
          case Ok(b) => value_eq(a, b) match {
            case Ok(same) => Ok(BoolV(same))
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case And(es) =>
      eval_and(v_P, fuel, env, es)
    case Or(es) =>
      eval_or(v_P, fuel, env, es)
    case Implies(lhs, rhs) =>
      eval_bool(v_P, fuel, env, lhs) match {
        case Ok(a) => if (a) {
          eval_bool(v_P, fuel, env, rhs) match {
            case Ok(b) => Ok(BoolV(b))
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
        } else {
          Ok(BoolV(true))
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case Not(expr) =>
      eval_bool(v_P, fuel, env, expr) match {
        case Ok(a) => Ok(BoolV(!(a)))
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case StringConcat(lhs, rhs) =>
      eval_string(v_P, fuel, env, lhs) match {
        case Ok(a) => eval_string(v_P, fuel, env, rhs) match {
          case Ok(b) => Ok(StringV(append_chars(a, b)))
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case SubString(expr, start, end) =>
      eval_string(v_P, fuel, env, expr) match {
        case Ok(cs) => eval_int(v_P, fuel, env, start) match {
          case Ok(b) => eval_int(v_P, fuel, env, end) match {
            case Ok(c) => if (((b < BigInt(0)) || (c <= b))) {
              Ok(StringV(Nil()))
            } else {
              Ok(StringV(take((c - b), drop(b, cs))))
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case StringLength(expr) =>
      eval_string(v_P, fuel, env, expr) match {
        case Ok(cs) => Ok(IntV(length(cs)))
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case Plus(lhs, rhs) =>
      eval(v_P, fuel, env, lhs) match {
        case Ok(a) => eval(v_P, fuel, env, rhs) match {
          case Ok(b) => arith_plus(a, b)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case Minus(lhs, rhs) =>
      eval(v_P, fuel, env, lhs) match {
        case Ok(a) => eval(v_P, fuel, env, rhs) match {
          case Ok(b) => arith_minus(a, b)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case UMinus(expr) =>
      eval(v_P, fuel, env, expr) match {
        case Ok(a) => arith_neg(a)
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case Times(lhs, rhs) =>
      eval(v_P, fuel, env, lhs) match {
        case Ok(a) => eval(v_P, fuel, env, rhs) match {
          case Ok(b) => arith_times(a, b)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case Division(lhs, rhs) =>
      eval(v_P, fuel, env, lhs) match {
        case Ok(a) => eval(v_P, fuel, env, rhs) match {
          case Ok(b) => arith_div(a, b)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case Remainder(lhs, rhs) =>
      eval(v_P, fuel, env, lhs) match {
        case Ok(a) => eval(v_P, fuel, env, rhs) match {
          case Ok(b) => arith_rem(a, b)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case Modulo(lhs, rhs) =>
      eval(v_P, fuel, env, lhs) match {
        case Ok(a) => eval(v_P, fuel, env, rhs) match {
          case Ok(b) => arith_mod(a, b)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case LessThan(lhs, rhs) =>
      eval(v_P, fuel, env, lhs) match {
        case Ok(a) => eval(v_P, fuel, env, rhs) match {
          case Ok(b) => arith_lt(a, b) match {
            case Ok(r) => Ok(BoolV(r))
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case GreaterThan(lhs, rhs) =>
      eval(v_P, fuel, env, lhs) match {
        case Ok(a) => eval(v_P, fuel, env, rhs) match {
          case Ok(b) => arith_lt(b, a) match {
            case Ok(r) => Ok(BoolV(r))
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case LessEquals(lhs, rhs) =>
      eval(v_P, fuel, env, lhs) match {
        case Ok(a) => eval(v_P, fuel, env, rhs) match {
          case Ok(b) => arith_le(a, b) match {
            case Ok(r) => Ok(BoolV(r))
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case GreaterEquals(lhs, rhs) =>
      eval(v_P, fuel, env, lhs) match {
        case Ok(a) => eval(v_P, fuel, env, rhs) match {
          case Ok(b) => arith_le(b, a) match {
            case Ok(r) => Ok(BoolV(r))
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case BVNot(expr) =>
      eval(v_P, fuel, env, expr) match {
        case Ok(a) => (a) match {
          case BVV(s, w, x) => Ok(BVV(s, w, ((pow2(w) - BigInt(1)) - x)))
          case _ => Stuck()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case BVAnd(lhs, rhs) =>
      eval(v_P, fuel, env, lhs) match {
        case Ok(a) => eval(v_P, fuel, env, rhs) match {
          case Ok(b) => bv_binary(AndOp(), a, b)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case BVOr(lhs, rhs) =>
      eval(v_P, fuel, env, lhs) match {
        case Ok(a) => eval(v_P, fuel, env, rhs) match {
          case Ok(b) => bv_binary(OrOp(), a, b)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case BVXor(lhs, rhs) =>
      eval(v_P, fuel, env, lhs) match {
        case Ok(a) => eval(v_P, fuel, env, rhs) match {
          case Ok(b) => bv_binary(XorOp(), a, b)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case BVShiftLeft(lhs, rhs) =>
      eval(v_P, fuel, env, lhs) match {
        case Ok(a) => eval(v_P, fuel, env, rhs) match {
          case Ok(b) => bv_binary(ShiftLeftOp(), a, b)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case BVAShiftRight(lhs, rhs) =>
      eval(v_P, fuel, env, lhs) match {
        case Ok(a) => eval(v_P, fuel, env, rhs) match {
          case Ok(b) => bv_binary(AShiftRightOp(), a, b)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case BVLShiftRight(lhs, rhs) =>
      eval(v_P, fuel, env, lhs) match {
        case Ok(a) => eval(v_P, fuel, env, rhs) match {
          case Ok(b) => bv_binary(LShiftRightOp(), a, b)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case BVNarrowingCast(expr, w) =>
      eval(v_P, fuel, env, expr) match {
        case Ok(a) => bv_cast(a, w)
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case BVWideningCast(expr, w) =>
      eval(v_P, fuel, env, expr) match {
        case Ok(a) => bv_cast(a, w)
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case BVUnsignedToSigned(expr) =>
      eval(v_P, fuel, env, expr) match {
        case Ok(a) => (a) match {
          case BVV(false, w, x) => Ok(BVV(true, w, x))
          case _ => Stuck()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case BVSignedToUnsigned(expr) =>
      eval(v_P, fuel, env, expr) match {
        case Ok(a) => (a) match {
          case BVV(true, w, x) => Ok(BVV(false, w, x))
          case _ => Stuck()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case BVToInt(expr) =>
      eval(v_P, fuel, env, expr) match {
        case Ok(a) => (a) match {
          case BVV(s, w, x) => Ok(IntV(bv_int(s, w, x)))
          case _ => Stuck()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case IntToBV(w, s, expr) =>
      eval_int(v_P, fuel, env, expr) match {
        case Ok(i) => Ok(bv(s, w, i))
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case Tuple(es) =>
      eval_list(v_P, fuel, env, es) match {
        case Ok(vs) => Ok(TupleV(vs))
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case TupleSelect(tuple, i) =>
      eval(v_P, fuel, env, tuple) match {
        case Ok(t) => (t) match {
          case TupleV(vs) => nth(vs, i)
          case _ => Stuck()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case FiniteSet(es) =>
      eval_list(v_P, fuel, env, es) match {
        case Ok(vs) => set_insert_all(Nil(), vs) match {
          case Ok(xs) => Ok(SetV(xs))
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case SetAdd(set, elem) =>
      eval_set(v_P, fuel, env, set) match {
        case Ok(xs) => eval(v_P, fuel, env, elem) match {
          case Ok(v) => set_insert(xs, v) match {
            case Ok(ys) => Ok(SetV(ys))
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case ElementOfSet(elem, set) =>
      eval(v_P, fuel, env, elem) match {
        case Ok(v) => eval_set(v_P, fuel, env, set) match {
          case Ok(xs) => set_contains(xs, v) match {
            case Ok(in) => Ok(BoolV(in))
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case SubsetOf(lhs, rhs) =>
      eval_set(v_P, fuel, env, lhs) match {
        case Ok(xs) => eval_set(v_P, fuel, env, rhs) match {
          case Ok(ys) => subset(xs, ys) match {
            case Ok(sub) => Ok(BoolV(sub))
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case SetIntersection(lhs, rhs) =>
      eval_set(v_P, fuel, env, lhs) match {
        case Ok(xs) => eval_set(v_P, fuel, env, rhs) match {
          case Ok(ys) => set_filter(xs, ys, true) match {
            case Ok(zs) => Ok(SetV(zs))
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case SetUnion(lhs, rhs) =>
      eval_set(v_P, fuel, env, lhs) match {
        case Ok(xs) => eval_set(v_P, fuel, env, rhs) match {
          case Ok(ys) => set_insert_all(xs, ys) match {
            case Ok(zs) => Ok(SetV(zs))
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case SetDifference(lhs, rhs) =>
      eval_set(v_P, fuel, env, lhs) match {
        case Ok(xs) => eval_set(v_P, fuel, env, rhs) match {
          case Ok(ys) => set_filter(xs, ys, false) match {
            case Ok(zs) => Ok(SetV(zs))
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case FiniteBag(es) =>
      eval_bag_entries(v_P, fuel, env, Nil(), es) match {
        case Ok(xs) => Ok(BagV(xs))
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case BagAdd(bag, elem) =>
      eval_bag(v_P, fuel, env, bag) match {
        case Ok(xs) => eval(v_P, fuel, env, elem) match {
          case Ok(v) => bag_get(xs, v) match {
            case Ok(n) => bag_set(xs, v, (n + BigInt(1))) match {
              case Ok(ys) => Ok(BagV(ys))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case MultiplicityInBag(elem, bag) =>
      eval(v_P, fuel, env, elem) match {
        case Ok(v) => eval_bag(v_P, fuel, env, bag) match {
          case Ok(xs) => bag_get(xs, v) match {
            case Ok(n) => Ok(IntV(n))
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case BagIntersection(lhs, rhs) =>
      eval_bag(v_P, fuel, env, lhs) match {
        case Ok(xs) => eval_bag(v_P, fuel, env, rhs) match {
          case Ok(ys) => bag_merge(IntersectionOp(), Nil(), xs, ys) match {
            case Ok(zs) => Ok(BagV(zs))
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case BagUnion(lhs, rhs) =>
      eval_bag(v_P, fuel, env, lhs) match {
        case Ok(xs) => eval_bag(v_P, fuel, env, rhs) match {
          case Ok(ys) => bag_add_all(xs, ys) match {
            case Ok(zs) => Ok(BagV(zs))
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case BagDifference(lhs, rhs) =>
      eval_bag(v_P, fuel, env, lhs) match {
        case Ok(xs) => eval_bag(v_P, fuel, env, rhs) match {
          case Ok(ys) => bag_merge(DifferenceOp(), Nil(), xs, ys) match {
            case Ok(zs) => Ok(BagV(zs))
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case FiniteMap(pairs, default) =>
      eval_map_entries(v_P, fuel, env, Nil(), pairs) match {
        case Ok(xs) => eval(v_P, fuel, env, default) match {
          case Ok(d) => Ok(MapV(xs, d))
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case MapApply(map, key) =>
      eval(v_P, fuel, env, map) match {
        case Ok(m) => eval(v_P, fuel, env, key) match {
          case Ok(k) => (m) match {
            case MapV(xs, d) => map_get(xs, k, d)
            case _ => Stuck()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case MapUpdated(map, key, value) =>
      eval(v_P, fuel, env, map) match {
        case Ok(m) => eval(v_P, fuel, env, key) match {
          case Ok(k) => eval(v_P, fuel, env, value) match {
            case Ok(v) => (m) match {
              case MapV(xs, d) => map_put(xs, k, v) match {
                  case Ok(ys) => Ok(MapV(ys, d))
                  case Stuck() => Stuck()
                  case OutOfFuel() => OutOfFuel()
                }
              case _ => Stuck()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case MapMerge(mask, map1, map2) =>
      eval_set(v_P, fuel, env, mask) match {
        case Ok(ks) => eval(v_P, fuel, env, map1) match {
          case Ok(m1) => eval(v_P, fuel, env, map2) match {
            case Ok(m2) => (m1) match {
              case MapV(xs, d1) => (m2) match {
                  case MapV(ys, d2) => map_without(ys, ks) match {
                      case Ok(rest) => map_take(rest, ks, xs, d1) match {
                        case Ok(zs) => Ok(MapV(zs, d2))
                        case Stuck() => Stuck()
                        case OutOfFuel() => OutOfFuel()
                      }
                      case Stuck() => Stuck()
                      case OutOfFuel() => OutOfFuel()
                    }
                  case _ => Stuck()
                }
              case _ => Stuck()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
  }

  def eval_list(v_P: Program, fuel: BigInt, env: List[Binding], es: List[Expr]): Result[List[Value]] =
    (es) match {
      case Nil() => Ok(Nil())
      case Cons(e, rest) => eval(v_P, fuel, env, e) match {
          case Ok(v) => eval_list(v_P, fuel, env, rest) match {
            case Ok(vs) => Ok(Cons(v, vs))
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
    }

  def eval_int(v_P: Program, fuel: BigInt, env: List[Binding], e: Expr): Result[BigInt] =
    eval(v_P, fuel, env, e) match {
      case Ok(v) => (v) match {
        case IntV(i) => Ok(i)
        case _ => Stuck()
      }
      case Stuck() => Stuck()
      case OutOfFuel() => OutOfFuel()
    }

  def eval_bool(v_P: Program, fuel: BigInt, env: List[Binding], e: Expr): Result[Boolean] =
    eval(v_P, fuel, env, e) match {
      case Ok(v) => (v) match {
        case BoolV(b) => Ok(b)
        case _ => Stuck()
      }
      case Stuck() => Stuck()
      case OutOfFuel() => OutOfFuel()
    }

  def value_eq(a: Value, b: Value): Result[Boolean] =
    (a) match {
      case ClosureV(_, _, _) => Stuck()
      case ADTV(c, xs) => (b) match {
          case ADTV(d, ys) => if ((c == d)) {
              values_eq(xs, ys)
            } else {
              Ok(false)
            }
          case _ => Ok(false)
        }
      case TupleV(xs) => (b) match {
          case TupleV(ys) => values_eq(xs, ys)
          case _ => Ok(false)
        }
      case SetV(xs) => (b) match {
          case SetV(ys) => subset(xs, ys) match {
              case Ok(sub) => if (sub) {
                subset(ys, xs)
              } else {
                Ok(false)
              }
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
          case _ => Ok(false)
        }
      case BagV(xs) => (b) match {
          case BagV(ys) => sub_bag(xs, ys) match {
              case Ok(sub) => if (sub) {
                sub_bag(ys, xs)
              } else {
                Ok(false)
              }
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
          case _ => Ok(false)
        }
      case MapV(xs, d) => (b) match {
          case MapV(ys, e) => value_eq(d, e) match {
              case Ok(same) => if (same) {
                same_entries(xs, xs, d, ys, e) match {
                  case Ok(l) => if (l) {
                    same_entries(ys, xs, d, ys, e)
                  } else {
                    Ok(false)
                  }
                  case Stuck() => Stuck()
                  case OutOfFuel() => OutOfFuel()
                }
              } else {
                Ok(false)
              }
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
          case _ => Ok(false)
        }
      case _ => Ok((a == b))
    }

  def values_eq(xs: List[Value], ys: List[Value]): Result[Boolean] =
    (xs) match {
      case Nil() => (ys) match {
          case Nil() => Ok(true)
          case _ => Ok(false)
        }
      case Cons(x, xr) => (ys) match {
          case Nil() => Ok(false)
          case Cons(y, yr) => value_eq(x, y) match {
              case Ok(same) => if (same) {
                values_eq(xr, yr)
              } else {
                Ok(false)
              }
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
        }
    }

  def eval_and(v_P: Program, fuel: BigInt, env: List[Binding], es: List[Expr]): Result[Value] =
    (es) match {
      case Nil() => Ok(BoolV(true))
      case Cons(e, rest) => eval_bool(v_P, fuel, env, e) match {
          case Ok(b) => if (b) {
            eval_and(v_P, fuel, env, rest)
          } else {
            Ok(BoolV(false))
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
    }

  def eval_or(v_P: Program, fuel: BigInt, env: List[Binding], es: List[Expr]): Result[Value] =
    (es) match {
      case Nil() => Ok(BoolV(false))
      case Cons(e, rest) => eval_bool(v_P, fuel, env, e) match {
          case Ok(b) => if (b) {
            Ok(BoolV(true))
          } else {
            eval_or(v_P, fuel, env, rest)
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
    }

  def append_env(bs: List[Binding], env: List[Binding]): List[Binding] =
    (bs) match {
      case Nil() => env
      case Cons(b, rest) => Cons(b, append_env(rest, env))
    }

  def nth(vs: List[Value], i: BigInt): Result[Value] =
    (vs) match {
      case Nil() => Stuck()
      case Cons(v, rest) => if ((i == BigInt(1))) {
          Ok(v)
        } else {
          nth(rest, (i - BigInt(1)))
        }
    }

  def abs(a: BigInt): BigInt =
    if ((a < BigInt(0))) {
      (BigInt(0) - a)
    } else {
      a
    }

  def gcd(a: BigInt, b: BigInt): BigInt =
    if ((b == BigInt(0))) {
      a
    } else {
      gcd(b, emod(a, b))
    }

  def pow2(n: BigInt): BigInt =
    if ((n <= BigInt(0))) {
      BigInt(1)
    } else {
      (BigInt(2) * pow2((n - BigInt(1))))
    }

  def bit(a: BigInt): BigInt =
    emod(a, BigInt(2))

  def bit_and(a: BigInt, b: BigInt): BigInt =
    if (((a == BigInt(0)) || (b == BigInt(0)))) {
      BigInt(0)
    } else {
      ((BigInt(2) * bit_and(ediv(a, BigInt(2)), ediv(b, BigInt(2)))) + (bit(a) * bit(b)))
    }

  def bit_or(a: BigInt, b: BigInt): BigInt =
    if ((a == BigInt(0))) {
      b
    } else {
      if ((b == BigInt(0))) {
        a
      } else {
        ((BigInt(2) * bit_or(ediv(a, BigInt(2)), ediv(b, BigInt(2)))) + ((bit(a) + bit(b)) - (bit(a) * bit(b))))
      }
    }

  def bit_xor(a: BigInt, b: BigInt): BigInt =
    if ((a == BigInt(0))) {
      b
    } else {
      if ((b == BigInt(0))) {
        a
      } else {
        ((BigInt(2) * bit_xor(ediv(a, BigInt(2)), ediv(b, BigInt(2)))) + emod((bit(a) + bit(b)), BigInt(2)))
      }
    }

  def tdiv(a: BigInt, b: BigInt): BigInt =
    if ((BigInt(0) <= a)) {
      ediv(a, b)
    } else {
      (BigInt(0) - ediv((BigInt(0) - a), b))
    }

  def trem(a: BigInt, b: BigInt): BigInt =
    (a - (b * tdiv(a, b)))

  def real(n: BigInt, d: BigInt): Result[Value] =
    if ((d == BigInt(0))) {
      Stuck()
    } else {
      {
        val g = gcd(abs(n), abs(d))
        val s = if ((d < BigInt(0))) {
          (BigInt(0) - BigInt(1))
        } else {
          BigInt(1)
        }
        Ok(RealV((s * ediv(n, g)), (s * ediv(d, g))))
      }
    }

  def bv(s: Boolean, w: BigInt, x: BigInt): Value =
    BVV(s, w, emod(x, pow2(w)))

  def twos(w: BigInt, x: BigInt): BigInt =
    if ((pow2((w - BigInt(1))) <= x)) {
      (x - pow2(w))
    } else {
      x
    }

  def bv_int(s: Boolean, w: BigInt, x: BigInt): BigInt =
    if (s) {
      twos(w, x)
    } else {
      x
    }

  def same_bv(s: Boolean, w: BigInt, t: Boolean, v: BigInt): Boolean =
    ((s == t) && (w == v))

  def arith_plus(a: Value, b: Value): Result[Value] =
    (a) match {
      case IntV(x) => (b) match {
          case IntV(y) => Ok(IntV((x + y)))
          case _ => Stuck()
        }
      case RealV(n, d) => (b) match {
          case RealV(m, e) => real(((n * e) + (m * d)), (d * e))
          case _ => Stuck()
        }
      case BVV(s, w, x) => (b) match {
          case BVV(t, v, y) => if (same_bv(s, w, t, v)) {
              Ok(bv(s, w, (x + y)))
            } else {
              Stuck()
            }
          case _ => Stuck()
        }
      case _ => Stuck()
    }

  def arith_minus(a: Value, b: Value): Result[Value] =
    (a) match {
      case IntV(x) => (b) match {
          case IntV(y) => Ok(IntV((x - y)))
          case _ => Stuck()
        }
      case RealV(n, d) => (b) match {
          case RealV(m, e) => real(((n * e) - (m * d)), (d * e))
          case _ => Stuck()
        }
      case BVV(s, w, x) => (b) match {
          case BVV(t, v, y) => if (same_bv(s, w, t, v)) {
              Ok(bv(s, w, (x - y)))
            } else {
              Stuck()
            }
          case _ => Stuck()
        }
      case _ => Stuck()
    }

  def arith_times(a: Value, b: Value): Result[Value] =
    (a) match {
      case IntV(x) => (b) match {
          case IntV(y) => Ok(IntV((x * y)))
          case _ => Stuck()
        }
      case RealV(n, d) => (b) match {
          case RealV(m, e) => real((n * m), (d * e))
          case _ => Stuck()
        }
      case BVV(s, w, x) => (b) match {
          case BVV(t, v, y) => if (same_bv(s, w, t, v)) {
              Ok(bv(s, w, (x * y)))
            } else {
              Stuck()
            }
          case _ => Stuck()
        }
      case _ => Stuck()
    }

  def arith_div(a: Value, b: Value): Result[Value] =
    (a) match {
      case IntV(x) => (b) match {
          case IntV(y) => if ((y == BigInt(0))) {
              Stuck()
            } else {
              Ok(IntV(ediv(x, y)))
            }
          case _ => Stuck()
        }
      case RealV(n, d) => (b) match {
          case RealV(m, e) => if ((m == BigInt(0))) {
              Stuck()
            } else {
              real((n * e), (d * m))
            }
          case _ => Stuck()
        }
      case BVV(s, w, x) => (b) match {
          case BVV(t, v, y) => if (same_bv(s, w, t, v)) {
              {
                val i = bv_int(s, w, x)
                val j = bv_int(s, w, y)
                if ((j == BigInt(0))) {
                  if (s) {
                    Ok(bv(s, w, if ((BigInt(0) <= i)) {
                      (BigInt(0) - BigInt(1))
                    } else {
                      BigInt(1)
                    }))
                  } else {
                    Ok(bv(s, w, (pow2(w) - BigInt(1))))
                  }
                } else {
                  Ok(bv(s, w, tdiv(i, j)))
                }
              }
            } else {
              Stuck()
            }
          case _ => Stuck()
        }
      case _ => Stuck()
    }

  def arith_rem(a: Value, b: Value): Result[Value] =
    (a) match {
      case IntV(x) => (b) match {
          case IntV(y) => if ((y == BigInt(0))) {
              Stuck()
            } else {
              Ok(IntV(emod(x, y)))
            }
          case _ => Stuck()
        }
      case BVV(s, w, x) => (b) match {
          case BVV(t, v, y) => if (same_bv(s, w, t, v)) {
              {
                val i = bv_int(s, w, x)
                val j = bv_int(s, w, y)
                if ((j == BigInt(0))) {
                  Ok(a)
                } else {
                  Ok(bv(s, w, trem(i, j)))
                }
              }
            } else {
              Stuck()
            }
          case _ => Stuck()
        }
      case _ => Stuck()
    }

  def arith_mod(a: Value, b: Value): Result[Value] =
    (a) match {
      case IntV(x) => (b) match {
          case IntV(y) => if ((y == BigInt(0))) {
              Stuck()
            } else {
              Ok(IntV(emod(x, y)))
            }
          case _ => Stuck()
        }
      case BVV(s, w, x) => (b) match {
          case BVV(t, v, y) => if (same_bv(s, w, t, v)) {
              {
                val i = bv_int(s, w, x)
                val j = bv_int(s, w, y)
                if ((j == BigInt(0))) {
                  Ok(a)
                } else {
                  {
                    val r = emod(i, j)
                    Ok(bv(s, w, if (((j < BigInt(0)) && !((r == BigInt(0))))) {
                      (r + j)
                    } else {
                      r
                    }))
                  }
                }
              }
            } else {
              Stuck()
            }
          case _ => Stuck()
        }
      case _ => Stuck()
    }

  def arith_neg(a: Value): Result[Value] =
    (a) match {
      case IntV(x) => Ok(IntV((BigInt(0) - x)))
      case RealV(n, d) => Ok(RealV((BigInt(0) - n), d))
      case BVV(s, w, x) => Ok(bv(s, w, (BigInt(0) - x)))
      case _ => Stuck()
    }

  def arith_lt(a: Value, b: Value): Result[Boolean] =
    (a) match {
      case IntV(x) => (b) match {
          case IntV(y) => Ok((x < y))
          case _ => Stuck()
        }
      case RealV(n, d) => (b) match {
          case RealV(m, e) => Ok(((n * e) < (m * d)))
          case _ => Stuck()
        }
      case CharV(x) => (b) match {
          case CharV(y) => Ok((x < y))
          case _ => Stuck()
        }
      case BVV(s, w, x) => (b) match {
          case BVV(t, v, y) => if (same_bv(s, w, t, v)) {
              Ok((bv_int(s, w, x) < bv_int(s, w, y)))
            } else {
              Stuck()
            }
          case _ => Stuck()
        }
      case _ => Stuck()
    }

  def arith_le(a: Value, b: Value): Result[Boolean] =
    arith_lt(b, a) match {
      case Ok(lt) => Ok(!(lt))
      case Stuck() => Stuck()
      case OutOfFuel() => OutOfFuel()
    }

  def shift_amount(w: BigInt, y: BigInt): BigInt =
    if ((w <= y)) {
      w
    } else {
      y
    }

  def bit_op(op: BitOp, s: Boolean, w: BigInt, x: BigInt, y: BigInt): Value =
    {
      val k = pow2(shift_amount(w, y))
      (op) match {
        case AndOp() => BVV(s, w, bit_and(x, y))
        case OrOp() => BVV(s, w, bit_or(x, y))
        case XorOp() => BVV(s, w, bit_xor(x, y))
        case ShiftLeftOp() => bv(s, w, (x * k))
        case AShiftRightOp() => bv(s, w, ediv(twos(w, x), k))
        case LShiftRightOp() => BVV(s, w, ediv(x, k))
      }
    }

  def bv_binary(op: BitOp, a: Value, b: Value): Result[Value] =
    (a) match {
      case BVV(s, w, x) => (b) match {
          case BVV(t, v, y) => if (same_bv(s, w, t, v)) {
              Ok(bit_op(op, s, w, x, y))
            } else {
              Stuck()
            }
          case _ => Stuck()
        }
      case _ => Stuck()
    }

  def bv_cast(a: Value, v: BigInt): Result[Value] =
    (a) match {
      case BVV(s, w, x) => Ok(bv(s, v, bv_int(s, w, x)))
      case _ => Stuck()
    }

  def append_chars(xs: List[BigInt], ys: List[BigInt]): List[BigInt] =
    (xs) match {
      case Nil() => ys
      case Cons(x, rest) => Cons(x, append_chars(rest, ys))
    }

  def length(xs: List[BigInt]): BigInt =
    (xs) match {
      case Nil() => BigInt(0)
      case Cons(_, rest) => (BigInt(1) + length(rest))
    }

  def take(n: BigInt, xs: List[BigInt]): List[BigInt] =
    if ((n <= BigInt(0))) {
      Nil()
    } else {
      (xs) match {
        case Nil() => Nil()
        case Cons(x, rest) => Cons(x, take((n - BigInt(1)), rest))
      }
    }

  def drop(n: BigInt, xs: List[BigInt]): List[BigInt] =
    if ((n <= BigInt(0))) {
      xs
    } else {
      (xs) match {
        case Nil() => Nil()
        case Cons(_, rest) => drop((n - BigInt(1)), rest)
      }
    }

  def eval_string(v_P: Program, fuel: BigInt, env: List[Binding], e: Expr): Result[List[BigInt]] =
    eval(v_P, fuel, env, e) match {
      case Ok(v) => (v) match {
        case StringV(cs) => Ok(cs)
        case _ => Stuck()
      }
      case Stuck() => Stuck()
      case OutOfFuel() => OutOfFuel()
    }

  def set_contains(xs: List[Value], v: Value): Result[Boolean] =
    (xs) match {
      case Nil() => Ok(false)
      case Cons(x, rest) => value_eq(x, v) match {
          case Ok(same) => if (same) {
            Ok(true)
          } else {
            set_contains(rest, v)
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
    }

  def set_insert(xs: List[Value], v: Value): Result[List[Value]] =
    set_contains(xs, v) match {
      case Ok(in) => if (in) {
        Ok(xs)
      } else {
        Ok(Cons(v, xs))
      }
      case Stuck() => Stuck()
      case OutOfFuel() => OutOfFuel()
    }

  def set_insert_all(xs: List[Value], vs: List[Value]): Result[List[Value]] =
    (vs) match {
      case Nil() => Ok(xs)
      case Cons(v, rest) => set_insert(xs, v) match {
          case Ok(ys) => set_insert_all(ys, rest)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
    }

  def subset(xs: List[Value], ys: List[Value]): Result[Boolean] =
    (xs) match {
      case Nil() => Ok(true)
      case Cons(x, rest) => set_contains(ys, x) match {
          case Ok(in) => if (in) {
            subset(rest, ys)
          } else {
            Ok(false)
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
    }

  def set_filter(xs: List[Value], ys: List[Value], keep: Boolean): Result[List[Value]] =
    (xs) match {
      case Nil() => Ok(Nil())
      case Cons(x, rest) => set_contains(ys, x) match {
          case Ok(in) => set_filter(rest, ys, keep) match {
            case Ok(zs) => if ((in == keep)) {
              Ok(Cons(x, zs))
            } else {
              Ok(zs)
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
    }

  def eval_set(v_P: Program, fuel: BigInt, env: List[Binding], e: Expr): Result[List[Value]] =
    eval(v_P, fuel, env, e) match {
      case Ok(v) => (v) match {
        case SetV(xs) => Ok(xs)
        case _ => Stuck()
      }
      case Stuck() => Stuck()
      case OutOfFuel() => OutOfFuel()
    }

  def bag_get(xs: List[BagEntry], v: Value): Result[BigInt] =
    (xs) match {
      case Nil() => Ok(BigInt(0))
      case Cons(BagEntry(x, n), rest) => value_eq(x, v) match {
          case Ok(same) => if (same) {
            Ok(n)
          } else {
            bag_get(rest, v)
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
    }

  def bag_remove(xs: List[BagEntry], v: Value): Result[List[BagEntry]] =
    (xs) match {
      case Nil() => Ok(Nil())
      case Cons(BagEntry(x, n), rest) => value_eq(x, v) match {
          case Ok(same) => if (same) {
            Ok(rest)
          } else {
            bag_remove(rest, v) match {
              case Ok(ys) => Ok(Cons(BagEntry(x, n), ys))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
    }

  def bag_set(xs: List[BagEntry], v: Value, n: BigInt): Result[List[BagEntry]] =
    bag_remove(xs, v) match {
      case Ok(ys) => if ((BigInt(0) < n)) {
        Ok(Cons(BagEntry(v, n), ys))
      } else {
        Ok(ys)
      }
      case Stuck() => Stuck()
      case OutOfFuel() => OutOfFuel()
    }

  def min(a: BigInt, b: BigInt): BigInt =
    if ((a < b)) {
      a
    } else {
      b
    }

  def bag_combine(op: BagOp, a: BigInt, b: BigInt): BigInt =
    (op) match {
      case IntersectionOp() => min(a, b)
      case UnionOp() => (a + b)
      case DifferenceOp() => (a - b)
    }

  def bag_merge(op: BagOp, acc: List[BagEntry], xs: List[BagEntry], ys: List[BagEntry]): Result[List[BagEntry]] =
    (xs) match {
      case Nil() => Ok(acc)
      case Cons(BagEntry(x, n), rest) => bag_get(ys, x) match {
          case Ok(m) => bag_set(acc, x, bag_combine(op, n, m)) match {
            case Ok(acc2) => bag_merge(op, acc2, rest, ys)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
    }

  def bag_add_all(acc: List[BagEntry], xs: List[BagEntry]): Result[List[BagEntry]] =
    (xs) match {
      case Nil() => Ok(acc)
      case Cons(BagEntry(x, n), rest) => bag_get(acc, x) match {
          case Ok(m) => bag_set(acc, x, (m + n)) match {
            case Ok(acc2) => bag_add_all(acc2, rest)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
    }

  def sub_bag(xs: List[BagEntry], ys: List[BagEntry]): Result[Boolean] =
    (xs) match {
      case Nil() => Ok(true)
      case Cons(BagEntry(x, n), rest) => bag_get(ys, x) match {
          case Ok(m) => if ((n == m)) {
            sub_bag(rest, ys)
          } else {
            Ok(false)
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
    }

  def eval_bag(v_P: Program, fuel: BigInt, env: List[Binding], e: Expr): Result[List[BagEntry]] =
    eval(v_P, fuel, env, e) match {
      case Ok(v) => (v) match {
        case BagV(xs) => Ok(xs)
        case _ => Stuck()
      }
      case Stuck() => Stuck()
      case OutOfFuel() => OutOfFuel()
    }

  def eval_bag_entries(v_P: Program, fuel: BigInt, env: List[Binding], acc: List[BagEntry], es: List[ExprPair]): Result[List[BagEntry]] =
    (es) match {
      case Nil() => Ok(acc)
      case Cons(ExprPair(k, c), rest) => eval(v_P, fuel, env, k) match {
          case Ok(v) => eval_int(v_P, fuel, env, c) match {
            case Ok(n) => bag_set(acc, v, n) match {
              case Ok(acc2) => eval_bag_entries(v_P, fuel, env, acc2, rest)
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
    }

  def map_get(xs: List[MapEntry], k: Value, d: Value): Result[Value] =
    (xs) match {
      case Nil() => Ok(d)
      case Cons(MapEntry(x, v), rest) => value_eq(x, k) match {
          case Ok(same) => if (same) {
            Ok(v)
          } else {
            map_get(rest, k, d)
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
    }

  def map_remove(xs: List[MapEntry], k: Value): Result[List[MapEntry]] =
    (xs) match {
      case Nil() => Ok(Nil())
      case Cons(MapEntry(x, v), rest) => value_eq(x, k) match {
          case Ok(same) => if (same) {
            Ok(rest)
          } else {
            map_remove(rest, k) match {
              case Ok(ys) => Ok(Cons(MapEntry(x, v), ys))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
    }

  def map_put(xs: List[MapEntry], k: Value, v: Value): Result[List[MapEntry]] =
    map_remove(xs, k) match {
      case Ok(ys) => Ok(Cons(MapEntry(k, v), ys))
      case Stuck() => Stuck()
      case OutOfFuel() => OutOfFuel()
    }

  def same_entries(ks: List[MapEntry], xs: List[MapEntry], d: Value, ys: List[MapEntry], e: Value): Result[Boolean] =
    (ks) match {
      case Nil() => Ok(true)
      case Cons(MapEntry(k, _), rest) => map_get(xs, k, d) match {
          case Ok(a) => map_get(ys, k, e) match {
            case Ok(b) => value_eq(a, b) match {
              case Ok(same) => if (same) {
                same_entries(rest, xs, d, ys, e)
              } else {
                Ok(false)
              }
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
    }

  def map_without(xs: List[MapEntry], ks: List[Value]): Result[List[MapEntry]] =
    (xs) match {
      case Nil() => Ok(Nil())
      case Cons(MapEntry(k, v), rest) => set_contains(ks, k) match {
          case Ok(in) => map_without(rest, ks) match {
            case Ok(ys) => if (in) {
              Ok(ys)
            } else {
              Ok(Cons(MapEntry(k, v), ys))
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
    }

  def map_take(acc: List[MapEntry], ks: List[Value], xs: List[MapEntry], d: Value): Result[List[MapEntry]] =
    (ks) match {
      case Nil() => Ok(acc)
      case Cons(k, rest) => map_get(xs, k, d) match {
          case Ok(v) => map_put(acc, k, v) match {
            case Ok(acc2) => map_take(acc2, rest, xs, d)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
    }

  def eval_map_entries(v_P: Program, fuel: BigInt, env: List[Binding], acc: List[MapEntry], es: List[ExprPair]): Result[List[MapEntry]] =
    (es) match {
      case Nil() => Ok(acc)
      case Cons(ExprPair(k, v), rest) => eval(v_P, fuel, env, k) match {
          case Ok(kv) => eval(v_P, fuel, env, v) match {
            case Ok(vv) => map_put(acc, kv, vv) match {
              case Ok(acc2) => eval_map_entries(v_P, fuel, env, acc2, rest)
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
    }
}
