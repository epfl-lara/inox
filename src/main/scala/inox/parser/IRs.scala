package inox
package parser

trait IRs
  extends SimpleTypes
     with Constraints
     with Matchings
     with IdentifierIRs
     with TypeIRs {

  protected val trees: inox.ast.Trees

  trait Store {
    def getIdentifier(name: String): inox.Identifier
    def getSort(identifier: inox.Identifier): trees.ADTSort
  }

  trait Args {
    def get[A: Manifest](index: Int): A
  }

  trait IR[-C, S <: Stage, A] {
    def elaborate(context: C)(implicit store: Store, args: Args): Constrained[S, A]
    def extract(scrutinee: A): Matching
  }

  abstract class IRHole[-C, S <: Stage : Pure, A: Manifest] extends IR[C, S, A] {
    val index: Int

    override def elaborate(context: C)(implicit store: Store, args: Args): Constrained[S, A] =
      Constrained.pure[S, A](args.get[A](index))

    override def extract(scrutinee: A): Matching =
      Matching(index -> scrutinee)
  }

  sealed trait IRSeq[-C, S <: Stage, A] extends IR[C, S, Seq[A]] {
    val minSize: Int
    def actualSize(args: Args): Int

    def ++[D <: C](that: IRSeq[D, S, A]): IRSeq[D, S, A] = IRSeqConcatenate(this, that)
  }

  implicit class IRSeqSingleton[-C, S <: Stage, A](inner: IR[C, S, A]) extends IRSeq[C, S, A] {
    override val minSize: Int = 1
    override def actualSize(args: Args): Int = 1

    override def elaborate(context: C)(implicit store: Store, args: Args): Constrained[S, Seq[A]] = for {
      elem <- inner.elaborate(context)
    } yield elem.map(Seq(_))

    override def extract(scrutinee: Seq[A]): Matching = scrutinee match {
      case Seq(elem) => inner.extract(scrutinee)
      case _ => Matching.fail
    }
  }

  abstract class IRSeqHole[-C, S <: Stage, A: Manifest] extends IRHole[C, S, Seq[A]] with IRSeq[C, S, A] {
    override val minSize: Int = 0
    override def actualSize(args: Args): Int = args.get[Seq[A]](index).size

    override def elaborate(context: C)(implicit store: Store, args: Args): Constrained[S, Seq[A]] =
      Constrained.eventual(args.get[Seq[A]](index))

  }

  case class IRSeqConcatenate[-C, S <: Stage, A](left: IRSeq[C, S, A], right: IRSeq[C, S, A]) extends IRSeq[C, S, A] {
    override val minSize: Int = left.minSize + right.minSize
    override def actualSize(args: Args): Int = left.actualSize(args) + right.actualSize(args)

    override def elaborate(context: C)(implicit store: Store, args: Args): Constrained[S, Seq[A]] = for {
      l <- left.elaborate(context)
      r <- right.elaborate(context)
    } yield Eventual.withUnifier { implicit unifier: Unifier => l.get ++ r.get }

    override def extract(scrutinee: Seq[A]): Matching = {
      val size = scrutinee.size
      if (size < minSize) {
        Matching.fail
      }
      else {
        val (leftScrutinee, rightScrutinee) = scrutinee.splitAt(size - right.minSize)

        left.extract(leftScrutinee) <> right.extract(rightScrutinee)
      }
    }
  }
}