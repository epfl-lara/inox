/* Copyright 2009-2015 EPFL, Lausanne */

package inox
package grammars
package aspects

import inox.utils.SeqUtils._

trait SimilarToAspects { self: GrammarsUniverse =>
  import program._
  import trees.{Minus => EMinus, Plus => EPlus, Times => ETimes, _}
  import symbols._

  /** Generates expressions similar to a [[Seq]] of given expressions
    * @param es The expressions for which similar ones will be generated
    */
  case class SimilarTo(es: Seq[Expr]) extends Aspect {
    type Prods = Seq[ProductionRule[Label, Expr]]

    def asString(implicit opts: PrinterOptions) = es.map(_.asString(opts)).mkString("~", "~", "~")

    def term(e: Expr, tag: Tag = Top, cost: Int = 1): ProductionRule[Label, Expr] = {
      ProductionRule(Nil, { case Seq() => e }, tag, cost)
    }

    /**
     * ~f(a,b)~  ::=  f(~a~, b)
     *                f(a, ~b~)
     *                f(b, a)   // if non-commut
     */
    def applyTo(lab: Label, ps: Seq[Production]) = {
      def isCommutative(e: Expr) = e match {
        case _: EPlus | _: ETimes => true
        case _ => false
      }

      val similarProds: Prods = es.filter(e => isSubtypeOf(e.getType, lab.getType)).flatMap { e =>
        val swaps: Prods = e match {
          case Operator(as, b) if as.nonEmpty && !isCommutative(e) =>
            val ast = as.zipWithIndex.groupBy(_._1.getType).mapValues(_.map(_._2).toList)

            val perms = ast.values.map { is =>
              is.permutations.toList.filter(p => p != is).map(ps => (is zip ps).toMap)
            }.filter(_.nonEmpty).toList

            //println("Perms:")
            //for (ps <- perms) {
            //  println(" - "+ps.mkString(", "))
            //}

            for (ps <- cartesianProduct(perms)) yield {
              val perm = ps.foldLeft(Map[Int, Int]())( _ ++ _ )

              //println("Trying permutation "+perm+": "+
              //    b(as.indices.map { i =>
              //      as(perm.getOrElse(i, i))
              //    }))

              term(b(as.indices.map { i => as(perm.getOrElse(i, i)) }))
            }
          case _ =>
            Nil
        }

        val subs: Prods = e match {
          case Operator(as, b) if as.nonEmpty =>
            for ((a, i) <- as.zipWithIndex) yield {
              ProductionRule[Label, Expr](
                List(Label(a.getType).withAspect(SimilarTo(Seq(a)))),
                { case Seq(e) =>
                  b(as.updated(i, e))
                },
                Top,
                1
              )
            }
          case _ =>
            Nil
        }

        val typeVariations: Prods = e match {
          case IntegerLiteral(v) =>
            List(
              term(IntegerLiteral(v + 1)),
              term(IntegerLiteral(v - 1))
            )

          case IntLiteral(v) =>
            List(
              term(IntLiteral(v + 1)),
              term(IntLiteral(v - 1))
            )

          case BooleanLiteral(v) =>
            List(
              term(BooleanLiteral(!v))
            )

          case IsTyped(e, IntegerType) =>
            List(
              term(EPlus(e, IntegerLiteral(1))),
              term(EMinus(e, IntegerLiteral(1)))
            )
          case IsTyped(e, Int32Type) =>
            List(
              term(EPlus(e, IntLiteral(1))),
              term(EMinus(e, IntLiteral(1)))
            )
          case IsTyped(e, BooleanType) =>
            List(
              term(not(e))
            )

          case _ =>
            Nil
        }

        val ccVariations: Prods = e match {
          case CaseClass(cct, args) =>
            val resType = cct.tcd.toCase
            val neighbors = resType.root match {
              case acd: TypedAbstractClassDef =>
                acd.descendants diff Seq(resType)
              case ccd: TypedCaseClassDef =>
                Nil
            }

            for (scct <- neighbors if scct.fieldsTypes == resType.fieldsTypes) yield {
              term(CaseClass(scct.toType, args))
            }
          case _ =>
            Nil
        }

        swaps ++ subs ++ typeVariations ++ ccVariations
      }

      ps ++ similarProds
    }
  }
}

