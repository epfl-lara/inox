/* Copyright 2009-2018 EPFL, Lausanne */

package inox.utils

import scala.collection.SeqView
import scala.collection.mutable.ArrayBuffer

object SeqUtils {
  type Tuple[T] = Seq[T]

  def cartesianProduct[T](seqs: Tuple[Seq[T]]): Seq[Tuple[T]] = {
    val sizes = seqs.map(_.size)
    val max = sizes.product

    val result = new ArrayBuffer[Tuple[T]](max)
    var i = 0

    while (i < max) {
      var c = i
      var sel = -1
      val elem = for (s <- sizes) yield {
        val index = c % s
        c = c / s
        sel += 1
        seqs(sel)(index)
      }

      i+=1
      result += elem
    }

    result.toSeq
  }

  def sumTo(sum: Int, arity: Int): Seq[Seq[Int]] = {
    require(arity >= 1)
    if (sum < arity) {
      Nil
    } else if (arity == 1) {
      Seq(Seq(sum))
    } else {
      (1 until sum).flatMap{ n => 
        sumTo(sum-n, arity-1).map( r => n +: r)
      }
    }
  }

  def sumToOrdered(sum: Int, arity: Int): Seq[Seq[Int]] = {
    def rec(sum: Int, arity: Int): Seq[Seq[Int]] = {
      require(arity > 0)
      if (sum < 0) Nil
      else if (arity == 1) Seq(Seq(sum))
      else for {
        n <- 0 to sum / arity
        rest <- rec(sum - arity * n, arity - 1)
      } yield n +: rest.map(n + _)
    }

    rec(sum, arity) filterNot (_.head == 0)
  }

  def groupWhile[T](es: Seq[T])(p: T => Boolean): Seq[Seq[T]] = {
    var res: Seq[Seq[T]] = Nil

    var c = es
    while (c.nonEmpty) {
      val (span, rest) = c.span(p)

      if (span.isEmpty) {
        res :+= Seq(rest.head)
        c = rest.tail
      } else {
        res :+= span
        c = rest
      }
    }

    res
  }
}
