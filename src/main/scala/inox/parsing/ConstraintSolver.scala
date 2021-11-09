/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

import scala.util.parsing.input._

trait ConstraintSolvers { self: Elaborators =>

  case class ConstraintException(error: String, position: Position)
    extends ElaborationException(Seq(ErrorLocation(error, position)))

  class Solver {

    import trees._

    object UnknownCollector {
      var unknowns = Set[Unknown]()

      private val traverser = new ConcreteSelfTreeTraverser {
        override def traverse(t: Type): Unit = {
          t match {
            case u: Unknown => unknowns += u
            case _ => super.traverse(t)
          }
        }
      }

      def apply(tpe: Type): Set[Unknown] = {
        unknowns = Set()
        traverser.traverse(tpe)
        unknowns
      }
    }

    class OccurChecker(u: Unknown) {
      var exists = false

      val traverser = new ConcreteSelfTreeTraverser {
        override def traverse(t: Type): Unit = {
          t match {
            case u2: Unknown => {
              if (u == u2) exists = true
            }
            case _ => {
              super.traverse(t)
            }
          }
        }
      }

      def apply(t: Type): Boolean = {
        exists = false
        traverser.traverse(t)
        exists
      }
    }

    def solveConstraints(constraints: Seq[Constraint]): Unifier = {

      var unknowns: Set[Unknown] = constraints.flatMap({
        case cs => cs.types.flatMap(UnknownCollector(_))
      }).toSet
      var remaining: Seq[Constraint] = constraints
      var substitutions: Map[Unknown, Type] = Map()
      var typeClasses: Map[Unknown, TypeClass] = Map()
      var tupleConstraints: Map[Unknown, Set[Constraint]] = Map()
      var sortConstraints: Map[Unknown, Map[ADTSort, Type => Seq[Constraint]]] = Map()

      def substitute(u: Unknown, t: Type): Unit = {
        val subst = new Unifier(Map(u -> t))
        unknowns -= u
        remaining = remaining.map(subst(_))
        substitutions = substitutions.view.mapValues(subst(_)).toMap
        substitutions += (u -> t)
        tupleConstraints = tupleConstraints.view.mapValues(_.map(subst(_))).toMap
        sortConstraints = sortConstraints.view.mapValues(_.view.mapValues(
          _.andThen(_.map(subst(_)))
        ).toMap).toMap

        // If the variable we are substituting has "tuple" constraints...
        tupleConstraints.get(u).foreach { (cs: Set[Constraint]) =>

          // We reintroduce those constraints.
          remaining ++= cs

          // Remove the entry for the variable.
          tupleConstraints -= u
        }

        // If the variable we are substituting has a class constraint...
        typeClasses.get(u).foreach { (c: TypeClass) =>

          // We reintroduce this constraints.
          remaining +:= HasClass(t, c).setPos(u.pos)

          // Remove the entry for the variable.
          typeClasses -= u
        }

        // If the variable we are substituting has a sort constraint...
        sortConstraints.get(u).foreach { (sorts: Map[ADTSort, Type => Seq[Constraint]]) =>
          remaining +:= HasSortIn(t, sorts).setPos(u.pos)

          sortConstraints -= u
        }
      }

      def className(c: TypeClass) = c match {
        case Comparable => "comparable"
        case Numeric => "numeric"
        case Integral => "integral"
        case Bits => "a bit vector"
      }

      def handle(constraint: Constraint): Unit = {

        constraint match {
          case Equal(a, b) => (a, b) match {
            case _ if (a == b) => ()
            case (u1: Unknown, u2: Unknown) => {
              substitute(u1, u2)
            }
            case (u: Unknown, t) => {
              val checker = new OccurChecker(u)
              if (checker(t)) {
                throw new ConstraintException("Occur check.", constraint.pos)
              }

              substitute(u, t)
            }
            case (t, u: Unknown) => {
              val checker = new OccurChecker(u)
              if (checker(t)) {
                throw new ConstraintException("Occur check.", constraint.pos)
              }

              substitute(u, t)
            }
            case (FunctionType(fas, ta), FunctionType(fbs, tb)) if (fbs.length == fas.length) => {
              remaining ++= fas.zip(fbs).map({ case (fa, fb) => Equal(fa, fb).setPos(constraint.pos) })
              remaining +:= Equal(ta, tb).setPos(constraint.pos)
            }
            case (TupleType(tas), TupleType(tbs)) if (tas.length == tbs.length) => {
              remaining ++= tas.zip(tbs).map({ case (ta, tb) => Equal(ta, tb).setPos(constraint.pos) })
            }
            case (ADTType(ida, tas), ADTType(idb, tbs)) if (ida == idb && tas.length == tbs.length) => {
              remaining ++= tas.zip(tbs).map({ case (ta, tb) => Equal(ta, tb).setPos(constraint.pos) })
            }
            case (SetType(ta), SetType(tb)) => {
              remaining +:= Equal(ta, tb).setPos(constraint.pos)
            }
            case (BagType(ta), BagType(tb)) => {
              remaining +:= Equal(ta, tb).setPos(constraint.pos)
            }
            case (MapType(fa, ta), MapType(fb, tb)) => {
              remaining +:= Equal(fa, fb).setPos(constraint.pos)
              remaining +:= Equal(ta, tb).setPos(constraint.pos)
            }
            case _ => throw new ConstraintException("Types incompatible: " + a + ", " + b, constraint.pos)
          }
          case AtIndexEqual(a, b, i) => a match {
            case u: Unknown => {
              typeClasses.get(u).foreach {
                case c => throw new ConstraintException("Type " + a + " can not be both a tuple and " + className(c), constraint.pos)
              }
              sortConstraints.get(u).foreach {
                case _ => throw new ConstraintException("Type " + a + " can not be both a tuple and an ADT", constraint.pos)
              }
              tupleConstraints += (u -> (tupleConstraints.get(u).getOrElse(Set()) + constraint))
            }
            case TupleType(tps) => {
              if (tps.length >= i) {
                remaining +:= Equal(tps(i - 1), b).setPos(constraint.pos)
              }
              else {
                throw new ConstraintException("Type " + a + " does not have a field at index " + i, constraint.pos)
              }
            }
            case _ => {
              throw new ConstraintException("Type " + a + " is not a tuple.", constraint.pos)
            }
          }
          case HasClass(a, c) => {
            a match {
              case u: Unknown => {
                tupleConstraints.get(u).foreach {
                  case _ => throw new ConstraintException("Type " + a + " can not be both a tuple and " + className(c), constraint.pos)
                }
                sortConstraints.get(u).foreach {
                  case _ => throw new ConstraintException("Type " + a + " can not be both an ADT and " + className(c), constraint.pos)
                }
                typeClasses += (u -> { typeClasses.get(u) match {
                  case None => c
                  case Some(c2) => c & c2
                }})
              }
              case _ if c.hasInstance(a) => ()
              case _ => throw new ConstraintException("Type " + a + " is not " + className(c), constraint.pos)
            }
          }
          case HasSortIn(a, sorts) => {
            val n = sorts.size
            if (n == 0) {
              throw new ConstraintException("Type " + a + " has no valid ADT sort", constraint.pos)
            }
            if (n == 1) {
              val (sort, rest) = sorts.toSeq.head
              val typeArgs = sort.tparams.map(x => Unknown.fresh(using constraint.pos))
              val expectedType = ADTType(sort.id, typeArgs)

              remaining +:= Equal(a, expectedType)
              remaining ++= rest(expectedType)
            }
            else {
              a match {
                case u: Unknown => {
                  sortConstraints.get(u) match {
                    case None => sortConstraints += u -> sorts
                    case Some(otherSorts) => {
                      val intersection = sorts.keySet.intersect(otherSorts.keySet).map { (k: ADTSort) =>
                        (k, (tpe: Type) => sorts(k)(tpe) ++ otherSorts(k)(tpe))
                      }.toMap

                      remaining +:= HasSortIn(u, intersection)
                      sortConstraints -= u
                    }
                  }
                }
                case ADTType(id, _) => {
                  val rest = sorts.collectFirst({
                    case (sort, rest) if (sort.id == id) => rest
                  }).getOrElse({
                    throw new ConstraintException("Type " + a + " has not a valid sort", constraint.pos)
                  })

                  remaining ++= rest(a)
                }
                case _ => {
                  throw new ConstraintException("Type " + a + " is not an ADT", constraint.pos)
                }
              }
            }
          }
        }
      }

      while (!remaining.isEmpty) {
        while (!remaining.isEmpty) {
          val constraint = remaining.head
          remaining = remaining.tail
          handle(constraint)
        }

        if (remaining.isEmpty) {
          // Set the default instance for classes.
          typeClasses.foreach({
            case (t, Integral | Numeric) => remaining +:= Equal(t, IntegerType()).setPos(t.pos)
            case (t, Bits) => remaining +:= Equal(t, Int32Type()).setPos(t.pos)
            case _ => ()
          })
        }
      }

      if (!unknowns.isEmpty) {
        throw new ConstraintException("Ambiguity. Try using type annotations.", unknowns.head.pos)
      }

      new Unifier(substitutions)
    }
  }
}
