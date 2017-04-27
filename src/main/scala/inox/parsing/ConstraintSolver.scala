/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

import scala.util.parsing.input._

trait ConstraintSolvers { self: Interpolator =>
  
  object Solver {

    import trees._

    case class Bounds(lowers: Set[Type], uppers: Set[Type])

    object UnknownCollector {
      var unknowns = Set[Unknown]()

      private val traverser = new TreeTraverser {
        override def traverse(t: Type) {
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

    object UnknownChecker {
      private var exists = false

      private val traverser = new TreeTraverser {
        override def traverse(t: Type) {
          if (!exists) {
            t match {
              case _: Unknown => exists = true
              case _ => super.traverse(t)
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



    object UnknownCollectorVariance {
      var positives = Set[Unknown]()
      var negatives = Set[Unknown]()

      private val traverser = new TreeTraverser {
        override def traverse(t: Type) {
          t match {
            case u: Unknown => {
              negatives += u
              positives += u
            }
            case _ => super.traverse(t)
          } 
        }
      }

      private def collect(tpe: Type, isPositive: Boolean): Unit = tpe match {
        case u: Unknown => if (isPositive) positives += u else negatives += u
        case FunctionType(fs, t) => {
          fs.foreach(collect(_, !isPositive))
          collect(t, isPositive)
        }
        case TupleType(ts) => ts.foreach(collect(_, !isPositive))
        case ADTType(id, ts) => {
          val adtDef = symbols.getADT(id)

          adtDef.tparams.zip(ts).foreach({
            case (tpDef, tpe) =>
              if (tpDef.tp.isCovariant) collect(tpe, isPositive)
              else if (tpDef.tp.isContravariant) collect(tpe, !isPositive)
              else traverser.traverse(tpe)
          })
        }
        case SetType(t) => traverser.traverse(t)
        case BagType(t) => traverser.traverse(t)
        case MapType(k, v) => {
          traverser.traverse(k)
          traverser.traverse(v)
        }
        case _ => ()
      } 

      def apply(t: Type): (Set[Unknown], Set[Unknown]) = {
        positives = Set[Unknown]()
        negatives = Set[Unknown]()
        collect(t, true)
        (positives, negatives)
      }
    }

    class OccurChecker(u: Unknown) {
      var exists = false

      val traverser = new TreeTraverser {
        override def traverse(t: Type) {
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
      var bounds: Map[Unknown, Bounds] = Map()
      var typeClasses: Map[Unknown, TypeClass] = Map()
      var tupleConstraints: Map[Unknown, Set[Constraint]] = Map()

      def substitute(u: Unknown, t: Type) {
        val subst = new Unifier(Map(u -> t))
        unknowns -= u
        remaining = remaining.map(subst(_))
        substitutions = substitutions.mapValues(subst(_))
        substitutions += (u -> t)
        tupleConstraints = tupleConstraints.mapValues(_.map(subst(_)))

        bounds = bounds.mapValues {
          case Bounds(ls, us) => Bounds(ls.map(subst(_)), us.map(subst(_)))
        }

        // If the variable we are substituting has bounds...
        bounds.get(u).foreach {

          // We reintroduce those bounds has constraints.
          case Bounds(ls, us) => {
            remaining ++= ls.map(Subtype(_, t).setPos(u.pos))
            remaining ++= us.map(Subtype(t, _).setPos(u.pos))
          }

          // We remove the bounds of the variable.
          bounds -= u
        }

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
          remaining +:= HasClass(t, c).setPos(c.pos)

          // Remove the entry for the variable.
          typeClasses -= u
        }
      }

      def verifyBounds(b: Bounds) {

      }

      def isSurelyEnd(tpe: Type, top: Boolean): Boolean = tpe match {
        case _: Unknown => false
        case NAryType(Seq(), _) => true
        case ADTType(id, tps) => {
          val adtDef = symbols.getADT(id)
          assert(tps.length == tps.length)

          val sortCorrect = if (top) {
            adtDef.root(symbols) == adtDef
          }
          else {
            adtDef.root(symbols) != adtDef || {
              adtDef.isInstanceOf[ADTSort] &&
              adtDef.asInstanceOf[ADTSort].cons.isEmpty
            }
          }

          sortCorrect && {
            adtDef.tparams.zip(tps).forall {
              case (tpDef, argTpe) => {
                if (tpDef.tp.isCovariant) {
                  isSurelyEnd(argTpe, top)
                }
                else if (tpDef.tp.isContravariant) {
                  isSurelyEnd(argTpe, !top)
                }
                else {
                  true
                }
              }
            }
          }
        }
        case TupleType(ts) => ts.forall(isSurelyEnd(_, top))
        case FunctionType(fs, t) => fs.forall(isSurelyEnd(_, !top)) && isSurelyEnd(t, top)
        case BagType(_) | SetType(_) | MapType(_, _) => true // Those are invariant.
      }

      def className(c: TypeClass) = c match {
        case Comparable => "comparable"
        case Numeric => "numeric"
        case Integral => "integral"
        case Bits => "a bit vector"
      }

      def handle(constraint: Constraint) {

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
          case Subtype(a, b) => (a, b) match {
            case _ if (a == b) => ()
            case (u1: Unknown, u2: Unknown) => {
              val Bounds(l1s, u1s) = bounds.get(u1).getOrElse(Bounds(Set(), Set()))
              val Bounds(l2s, u2s) = bounds.get(u2).getOrElse(Bounds(Set(), Set()))

              bounds += (u1 -> Bounds(l1s, u1s + u2))
              bounds += (u2 -> Bounds(l2s + u1, u2s))
            }
            case (u: Unknown, _) => {
              val checker = new OccurChecker(u)
              if (checker(b)) {
                throw new ConstraintException("Occur check.", constraint.pos)
              }

              if (isSurelyEnd(b, false)) {
                // If b is at the bottom of the subtyping chain...
                remaining +:= Equal(a, b).setPos(constraint.pos)
              }
              else {
                val Bounds(ls, us) = bounds.get(u).getOrElse(Bounds(Set(), Set()))
                val nBounds = Bounds(ls, us + b)
                verifyBounds(nBounds)
                bounds += (u -> nBounds)
              }
            }
            case (_, u: Unknown) => {
              val checker = new OccurChecker(u)
              if (checker(a)) {
                throw new ConstraintException("Occur check.", constraint.pos)
              }

              if (isSurelyEnd(a, true)) {
                // If a is at the top of the subtyping chain...
                remaining +:= Equal(a, b).setPos(constraint.pos)
              }
              else {
                val Bounds(ls, us) = bounds.get(u).getOrElse(Bounds(Set(), Set()))
                val nBounds = Bounds(ls + a, us)
                verifyBounds(nBounds)
                bounds += (u -> nBounds)
              }
            }
            case (ADTType(id1, t1s), ADTType(id2, t2s)) => {
              val adtDef1 = symbols.lookupADT(id1).getOrElse {
                throw new Error("Unknown ADT: " + id1)
              }

              val adtDef2 = symbols.lookupADT(id2).getOrElse {
                throw new Error("Unknown ADT: " + id2)
              }

              if (adtDef1 != adtDef2 && adtDef1.root(symbols) != adtDef2) {
                throw new ConstraintException("Type " + a + " can not be a subtype of " + b, constraint.pos)
              }

              if (t1s.length != t2s.length || t2s.length != adtDef1.tparams.length) {
                throw new ConstraintException("Type " + a + " can not be a subtype of " + b, constraint.pos)
              }

              assert(adtDef1.tparams.length == adtDef2.tparams.length)
              assert(adtDef1.tparams.zip(adtDef2.tparams).forall({
                case (tp1, tp2) => (tp1.tp.isCovariant == tp2.tp.isCovariant) &&
                                   (tp1.tp.isContravariant == tp2.tp.isContravariant) &&
                                   (tp1.tp.isInvariant == tp2.tp.isInvariant)
              }))

              adtDef1.tparams.zip(t1s.zip(t2s)).foreach {
                case (tpDef, (t1, t2)) => {
                  if (tpDef.tp.isCovariant) {
                    remaining +:= Subtype(t1, t2).setPos(constraint.pos)
                  }
                  if (tpDef.tp.isContravariant) {
                    remaining +:= Subtype(t2, t1).setPos(constraint.pos)
                  }
                  if (tpDef.tp.isInvariant) {
                    remaining +:= Equal(t1, t2).setPos(constraint.pos)
                  }
                }
              }
            }
            case (TupleType(tas), TupleType(tbs)) if (tas.length == tbs.length) => {
              tas.zip(tbs).foreach {
                case (ta, tb) => remaining +:= Subtype(ta, tb).setPos(constraint.pos)
              }
            }
            case (SetType(ta), SetType(tb)) => {
              remaining +:= Equal(ta, tb).setPos(constraint.pos)  // Sets are invariant.
            }
            case (BagType(ta), BagType(tb)) => {
              remaining +:= Equal(ta, tb).setPos(constraint.pos) // Bags are invariant.
            }
            case (MapType(fa, ta), MapType(fb, tb)) => {
              remaining +:= Equal(fa, fb).setPos(constraint.pos) // Maps are invariant.
              remaining +:= Equal(ta, tb).setPos(constraint.pos)
            }
            case (FunctionType(fas, ta), FunctionType(fbs, tb)) if (fas.length == fbs.length) => {
              fas.zip(fbs).foreach {
                case (fa, fb) => remaining +:= Subtype(fb, fa).setPos(constraint.pos)
              }
              remaining +:= Subtype(ta, tb).setPos(constraint.pos)
            }
            case (NAryType(Seq(), _), _) => {
              remaining +:= Equal(a, b).setPos(constraint.pos)
            }
            case (_, NAryType(Seq(), _)) => {
              remaining +:= Equal(a, b).setPos(constraint.pos)
            }
            case _ => {
              throw new ConstraintException("Type " + a + " can not be a subtype of " + b, constraint.pos)
            }
          }
          case AtIndexEqual(a, b, i) => a match {
            case u: Unknown => {
              typeClasses.get(u).foreach {
                case c => throw new ConstraintException("Type " + a + " can not be both a tuple and " + className(c), constraint.pos)
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
                bounds.get(u).foreach {
                  case Bounds(ls, us) => {
                    // Member of type classes are flat.
                    remaining ++= ls.map(Equal(u, _).setPos(constraint.pos))
                    remaining ++= us.map(Equal(u, _).setPos(constraint.pos))
                  }

                  bounds -= u
                }
                tupleConstraints.get(u).foreach {
                  case _ => throw new ConstraintException("Type " + a + " can not be both a tuple and " + className(c), constraint.pos)
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
        }
      }

      while (!remaining.isEmpty) {
        while (!remaining.isEmpty) {
          val constraint = remaining.head
          remaining = remaining.tail
          handle(constraint)
        }

        // val (inUppersAll, inLowersAll) = bounds.toSeq.map({
        //   case (u, Bounds(ls, us)) => {
        //     val (plss, nlss) = ls.map(UnknownCollectorVariance(_)).unzip
        //     val (puss, nuss) = us.map(UnknownCollectorVariance(_)).unzip

        //     val pus = puss.fold(Set[Unknown]())(_ ++ _)
        //     val nus = nuss.fold(Set[Unknown]())(_ ++ _)
        //     val pls = plss.fold(Set[Unknown]())(_ ++ _)
        //     val nls = nlss.fold(Set[Unknown]())(_ ++ _)

        //     ((pus ++ nls) - u, (pls ++ nus) - u)
        //   }
        // }).unzip

        // val inUppers = inUppersAll.fold(Set[Unknown]())(_ ++ _)
        // val inLowers = inLowersAll.fold(Set[Unknown]())(_ ++ _)

        bounds.foreach({
          case (u, Bounds(ls, us)) => {
            val uInUps = us.map(UnknownCollector(_)).fold(Set[Unknown]())(_ ++ _)
            val uInLws = ls.map(UnknownCollector(_)).fold(Set[Unknown]())(_ ++ _)

            if (!us.isEmpty && uInUps.isEmpty /* && !inLowers.contains(u) */) {
              val bound = symbols.greatestLowerBound(us.toSeq)
              if (bound == Untyped) {
                throw new ConstraintException("The following types are incompatible: " + us, u.pos)
              }
              remaining +:= Equal(u, bound).setPos(u.pos)
            }
            else if (!ls.isEmpty && uInLws.isEmpty /* && !inUppers.contains(u) */) {
              val bound = symbols.leastUpperBound(ls.toSeq)
              if (bound == Untyped) {
                throw new ConstraintException("The following types are incompatible: " + ls, u.pos)
              }
              remaining +:= Equal(u, bound).setPos(u.pos)
            }
          }
        })

        if (remaining.isEmpty) {
          // Set the default instance for classes.
          typeClasses.foreach({
            case (t, Integral | Numeric) => remaining +:= Equal(t, IntegerType).setPos(t.pos)
            case (t, Bits) => remaining +:= Equal(t, Int32Type).setPos(t.pos)
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