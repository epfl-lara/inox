/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package theories

import scala.collection.BitSet

trait BitvectorEncoder extends SimpleEncoder {
  import trees._
  import trees.dsl._

  private case class BitvectorEncoding(
    bv: ADTConstructor,
    blasted: ADTConstructor,
    toBV: FunDef,
    toBlasted: FunDef,
    invariant: FunDef
  ) {
    def adts = Seq(bv, blasted)
    def functions = Seq(toBV, toBlasted, invariant)
  }

  private def mkEncoding(size: Int): BitvectorEncoding = {
    val bvID = FreshIdentifier("bv" + size)
    val blastedID = FreshIdentifier("blasted" + size)

    val bvField = ValDef(FreshIdentifier("value"), IntegerType)
    val blastedFields = (1 to size).map(i => ValDef(FreshIdentifier("b" + i), BooleanType)).toSeq

    val invID = FreshIdentifier("bv_inv" + size)

    val bv = mkConstructor(bvID, HasADTInvariant(invID))()(None)(_ => Seq(bvField))
    val blasted = mkConstructor(blastedID)()(None)(_ => blastedFields)

    val toBV = mkFunDef(FreshIdentifier("toBV" + size))()(_ => (
      Seq("x" :: blasted()), bv(), { case Seq(x) =>
        let("r" :: IntegerType, (0 until size - 1).map(i => if_ (x.getField(blastedFields(i).id)) {
          E(BigInt(2).pow(i))
        } else_ {
          E(BigInt(0))
        }: Expr).reduce(_ + _)) { r =>
          bv()(if_ (x.getField(blastedFields(size - 1).id)) {
            E(BigInt(2).pow(size)) - r
          } else_ {
            r
          })
        }
      }))

    val toBlasted = mkFunDef(FreshIdentifier("toBlasted" + size))()(_ => (
      Seq("x" :: bv()), blasted(), { case Seq(x) =>
        def rec(i: Int, last: Expr, vs: Seq[Expr]): Expr = {
          if (i == 0) {
            ADT(blasted(), (last === E(BigInt(1))) +: vs)
          } else {
            let("tpl" :: T(IntegerType, BooleanType), if_ (last >= E(BigInt(2).pow(i))) {
              E(last - E(BigInt(2).pow(i)), E(true))
            } else_ {
              E(last, E(false))
            }) { tpl =>
              rec(i - 1, tpl._1, tpl._2 +: vs)
            }
          }
        }

        if_ (x >= E(BigInt(0))) {
          rec(size - 1, x, Seq.empty)
        } else_ {
          rec(size - 1, E(BigInt(2).pow(size)) + x, Seq.empty)
        }
      }))

    val invariant = mkFunDef(invID)()(_ => (
      Seq("bv" :: bv()), BooleanType, { case Seq(bv) =>
        E(BigInt(Int.MinValue)) <= bv.getField(bvField.id) && bv.getField(bvField.id) <= E(BigInt(Int.MaxValue))
      }))

    BitvectorEncoding(bv, blasted, toBV, toBlasted, invariant)
  }

  private val bitvectors: Map[Int, BitvectorEncoding] = {
    (for (i <- List(8, 16, 32, 64)) yield (i -> mkEncoding(i))).toMap
  }

  private val chars: BitvectorEncoding = mkEncoding(32)

  override val extraFunctions = (chars +: bitvectors.values.toSeq).flatMap(_.functions)
  override val extraADTs = (chars +: bitvectors.values.toSeq).flatMap(_.adts)

  protected object encoder extends SelfTreeTransformer {
    import sourceProgram._

    protected def simplifySum(sum: Expr, size: Int): Expr =
      if_ (sum > E(BigInt(Int.MaxValue))) {
        E(BigInt(2).pow(size)) - sum
      } else_ {
        if_ (sum < E(BigInt(Int.MinValue))) {
          E(BigInt(2).pow(size)) + sum
        } else_ {
          sum
        }
      }

    protected def simplifyBlasted(e: Expr, size: Int): Expr = {
      val encoding = bitvectors(size)
      import encoding._
      e match {
        case FunctionInvocation(id, Seq(), Seq(arg)) if id == toBV.id => arg
        case _ => toBlasted(e)
      }
    }

    protected def inLIA(i1: Expr, i2: Expr, size: Int, recons: (Expr, Expr) => Expr): Expr = {
      val encoding = bitvectors(size)
      import encoding._
      bv()(recons(transform(i1).getField(bv.fields(0).id),
        transform(i2).getField(bv.fields(0).id)))
    }

    protected def inBlasted(i1: Expr, i2: Expr, size: Int, recons: (Expr, Expr) => Expr): Expr = {
      val encoding = bitvectors(size)
      import encoding._
      let("bl" :: T(blasted(), blasted()),
        E(simplifyBlasted(transform(i1), size), simplifyBlasted(transform(i2), size))
      ) { bl =>
        toBV(blasted()((0 until size).map { i =>
          recons(bl._1.getField(blasted.fields(i).id), bl._2.getField(blasted.fields(i).id))
        }.toSeq : _*))
      }
    }

    override def transform(e: Expr): Expr = e match {
      case lit @ BVLiteral(_, size) => bitvectors(size).bv()(E(lit.toBigInt))
      case lit @ CharLiteral(c) => chars.bv()(E(BigInt(c.toInt)))
      case Plus(IsTyped(i1, BVType(size)), i2) =>
        val encoding = bitvectors(size)
        import encoding._
        let("sum" :: IntegerType,
          transform(i1).getField(bv.fields(0).id) +
          transform(i2).getField(bv.fields(0).id)) {
            sum => bv()(simplifySum(sum, size))
          }

      case Minus(IsTyped(i1, _: BVType), i2) =>
        transform(Plus(i1, UMinus(i2)))

      case UMinus(IsTyped(i, BVType(size))) =>
        val encoding = bitvectors(size)
        import encoding._
        bv()(simplifySum(- transform(i).getField(bv.fields(0).id), size))

      case Times(IsTyped(i1, BVType(size)), i2) =>
        val encoding = bitvectors(size)
        import encoding._
        let("prod" :: IntegerType,
          transform(i1).getField(bv.fields(0).id) *
          transform(i2).getField(bv.fields(0).id)) { prod =>
            bv()(if_ (prod > E(BigInt(Int.MaxValue))) {
              simplifySum(Modulo(prod, E(BigInt(2).pow(size))), size)
            } else_ {
              if_ (prod < E(BigInt(Int.MinValue))) {
                simplifySum(E(BigInt(2).pow(size)) - Modulo(-prod, E(BigInt(2).pow(size))), size)
              } else_ {
                prod
              }
            })
          }

      case Division(IsTyped(i1, BVType(size)), i2) => inLIA(i1, i2, size, Division(_, _))
      case Remainder(IsTyped(i1, BVType(size)), i2) => inLIA(i1, i2, size, Remainder(_, _))
      case Modulo(IsTyped(i1, BVType(size)), i2) => inLIA(i1, i2, size, Modulo(_, _))
      case LessThan(IsTyped(i1, BVType(size)), i2) => inLIA(i1, i2, size, LessThan)
      case LessEquals(IsTyped(i1, BVType(size)), i2) => inLIA(i1, i2, size, LessEquals)
      case GreaterThan(IsTyped(i1, BVType(size)), i2) => inLIA(i1, i2, size, GreaterThan)
      case GreaterEquals(IsTyped(i1, BVType(size)), i2) => inLIA(i1, i2, size, GreaterEquals)

      case BVNot(IsTyped(i, BVType(size))) =>
        val encoding = bitvectors(size)
        import encoding._
        let("bl" :: blasted(), simplifyBlasted(transform(i), size)) { bl =>
          toBV(blasted()((0 until size).map(i => !bl.getField(blasted.fields(i).id)) : _*))
        }

      case BVOr(IsTyped(i1, BVType(size)), i2) => inBlasted(i1, i2, size, Or(_, _))
      case BVAnd(IsTyped(i1, BVType(size)), i2) => inBlasted(i1, i2, size, And(_, _))
      case BVXor(IsTyped(i1, BVType(size)), i2) => inBlasted(i1, i2, size, (b1,b2) => (b1 && !b2) || (!b1 && b2))

      case BVShiftLeft(IsTyped(i1, BVType(size)), i2) =>
        val encoding = bitvectors(size)
        import encoding._
        let("bl" :: blasted(), simplifyBlasted(transform(i1), size)) { bl =>
          let("count" :: IntegerType, transform(i2).getField(bv.fields(0).id)) { count =>
            toBV((0 until size).foldRight(blasted()(List.fill(size)(E(false)) : _*): Expr) { (i, elze) =>
              IfExpr(count === E(BigInt(i)), blasted()(
                (size - i to 0 by -1).map(j => bl.getField(blasted.fields(j).id)) ++
                List.fill(i)(E(false)) : _*
              ), elze)
            })
          }
        }

      case BVAShiftRight(IsTyped(i1, BVType(size)), i2) =>
        val encoding = bitvectors(size)
        import encoding._
        let("bl" :: blasted(), simplifyBlasted(transform(i1), size)) { bl =>
          let("count" :: IntegerType, transform(i2).getField(bv.fields(0).id)) { count =>
            val default = bl.getField(blasted.fields(size - 1).id)
            toBV((0 until size).foldRight(blasted()(List.fill(size)(default) : _*): Expr) { (i, elze) =>
              IfExpr(count === E(BigInt(i)), blasted()(
                List.fill(i)(default) ++
                (size - 1 to i by -1).map(j => bl.getField(blasted.fields(j).id)) : _*
              ), elze)
            })
          }
        }

      case BVLShiftRight(IsTyped(i1, BVType(size)), i2) =>
        val encoding = bitvectors(size)
        import encoding._
        let("bl" :: blasted(), simplifyBlasted(transform(i1), size)) { bl =>
          let("count" :: IntegerType, transform(i2).getField(bv.fields(0).id)) { count =>
            toBV((0 until size).foldRight(blasted()(List.fill(size)(E(false)) : _*): Expr) { (i, elze) =>
              IfExpr(count === E(BigInt(i)), blasted()(
                List.fill(i)(E(false)) ++
                (size - 1 to i by -1).map(j => bl.getField(blasted.fields(j).id)) : _*
              ), elze)
            })
          }
        }

      case _ => super.transform(e)
    }

    override def transform(tpe: Type): Type = tpe match {
      case BVType(size) => bitvectors(size).bv()
      case CharType => chars.bv()
      case _ => super.transform(tpe)
    }
  }

  private val tpeMap: Map[Type, (Int, BitvectorEncoding)] = {
    ((32 -> chars) +: bitvectors.toSeq).flatMap { case (size, e) =>
      Seq(e.bv(), e.bv(), e.blasted()).map(_ -> ((size, e)))
    }.toMap
  }

  protected object decoder extends SelfTreeTransformer {
    override def transform(e: Expr): Expr = e match {
      case ADT(tpe @ ADTType(id, _), args) => tpeMap.get(tpe) match {
        case Some((size, e)) =>
          val bi = if (id == e.bv.id) {
            val IntegerLiteral(i) = transform(args(0))
            i
          } else {
            BVLiteral(args.zipWithIndex.foldLeft(BitSet.empty) {
              case (bits, (v, i)) => if (v == E(true)) bits + (i + 1) else bits
            }, size).toBigInt
          }

          if (e == chars) CharLiteral(bi.toChar) else BVLiteral(bi, size)

        case None => super.transform(e)
      }

      case _ => super.transform(e)
    }

    override def transform(tpe: Type): Type = tpe match {
      case tpe: ADTType => tpeMap.get(tpe) match {
        case Some((size, e)) => if (e == chars) CharType else BVType(size)
        case None => super.transform(tpe)
      }

      case _ => super.transform(tpe)
    }
  }
}

object BitvectorEncoder {
  def apply(p: Program): BitvectorEncoder { val sourceProgram: p.type } = new {
    val sourceProgram: p.type = p
  } with BitvectorEncoder
}
