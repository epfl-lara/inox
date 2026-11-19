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
  final case class ADTV(ctor: Id, args: List[Value]) extends Value

  sealed abstract class Expr
  final case class Variable(id: Id) extends Expr
  final case class IntegerLiteral(value: BigInt) extends Expr
  final case class BooleanLiteral(value: Boolean) extends Expr
  final case class UnitLiteral() extends Expr
  final case class Let(id: Id, value: Expr, body: Expr) extends Expr
  final case class IfExpr(cond: Expr, thenn: Expr, elze: Expr) extends Expr
  final case class Assume(pred: Expr, body: Expr) extends Expr
  final case class Error() extends Expr
  final case class FunctionInvocation(id: Id, args: List[Expr]) extends Expr
  final case class ADT(id: Id, args: List[Expr]) extends Expr
  final case class IsConstructor(expr: Expr, id: Id) extends Expr
  final case class ADTSelector(adt: Expr, selector: Id) extends Expr
  final case class Equals(lhs: Expr, rhs: Expr) extends Expr
  final case class And(exprs: List[Expr]) extends Expr
  final case class Or(exprs: List[Expr]) extends Expr
  final case class Implies(lhs: Expr, rhs: Expr) extends Expr
  final case class Not(expr: Expr) extends Expr
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

  final case class FunDef(id: Id, params: List[Id], body: Expr)

  final case class Constructor(id: Id, sort: Id, fields: List[Id])

  final case class Sort(id: Id, invariant: Option[Id])

  final case class Program(functions: List[FunDef], constructors: List[Constructor], sorts: List[Sort])

  final case class Binding(id: Id, value: Value)

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
    case Variable(x) =>
      lookup_var(env, x)
    case IntegerLiteral(i) =>
      Ok(IntV(i))
    case BooleanLiteral(b) =>
      Ok(BoolV(b))
    case UnitLiteral() =>
      Ok(UnitV())
    case Let(x, value, body) =>
      eval(v_P, fuel, env, value) match {
        case Ok(v) => eval(v_P, fuel, Cons(Binding(x, v), env), body)
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
    case Error() =>
      Stuck()
    case FunctionInvocation(f, args) =>
      eval_list(v_P, fuel, env, args) match {
        case Ok(vs) => call(v_P, fuel, f, vs)
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
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
          case Ok(b) => Ok(BoolV((a == b)))
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
    case Plus(lhs, rhs) =>
      eval_int(v_P, fuel, env, lhs) match {
        case Ok(a) => eval_int(v_P, fuel, env, rhs) match {
          case Ok(b) => Ok(IntV((a + b)))
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case Minus(lhs, rhs) =>
      eval_int(v_P, fuel, env, lhs) match {
        case Ok(a) => eval_int(v_P, fuel, env, rhs) match {
          case Ok(b) => Ok(IntV((a - b)))
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case UMinus(expr) =>
      eval_int(v_P, fuel, env, expr) match {
        case Ok(a) => Ok(IntV((BigInt(0) - a)))
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case Times(lhs, rhs) =>
      eval_int(v_P, fuel, env, lhs) match {
        case Ok(a) => eval_int(v_P, fuel, env, rhs) match {
          case Ok(b) => Ok(IntV((a * b)))
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case Division(lhs, rhs) =>
      eval_int(v_P, fuel, env, lhs) match {
        case Ok(a) => eval_int(v_P, fuel, env, rhs) match {
          case Ok(b) => if ((b == BigInt(0))) {
            Stuck()
          } else {
            Ok(IntV(ediv(a, b)))
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case Remainder(lhs, rhs) =>
      eval_int(v_P, fuel, env, lhs) match {
        case Ok(a) => eval_int(v_P, fuel, env, rhs) match {
          case Ok(b) => if ((b == BigInt(0))) {
            Stuck()
          } else {
            Ok(IntV(emod(a, b)))
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case Modulo(lhs, rhs) =>
      eval_int(v_P, fuel, env, lhs) match {
        case Ok(a) => eval_int(v_P, fuel, env, rhs) match {
          case Ok(b) => if ((b == BigInt(0))) {
            Stuck()
          } else {
            Ok(IntV(emod(a, b)))
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case LessThan(lhs, rhs) =>
      eval_int(v_P, fuel, env, lhs) match {
        case Ok(a) => eval_int(v_P, fuel, env, rhs) match {
          case Ok(b) => Ok(BoolV((a < b)))
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case GreaterThan(lhs, rhs) =>
      eval_int(v_P, fuel, env, lhs) match {
        case Ok(a) => eval_int(v_P, fuel, env, rhs) match {
          case Ok(b) => Ok(BoolV((b < a)))
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case LessEquals(lhs, rhs) =>
      eval_int(v_P, fuel, env, lhs) match {
        case Ok(a) => eval_int(v_P, fuel, env, rhs) match {
          case Ok(b) => Ok(BoolV((a <= b)))
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }
    case GreaterEquals(lhs, rhs) =>
      eval_int(v_P, fuel, env, lhs) match {
        case Ok(a) => eval_int(v_P, fuel, env, rhs) match {
          case Ok(b) => Ok(BoolV((b <= a)))
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
}
