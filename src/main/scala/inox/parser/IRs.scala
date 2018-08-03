package inox
package parser

trait IRs
  extends SimpleTypes
     with Constraints
     with Matchings {

  protected val trees: inox.ast.Trees

  trait Store {
    def getIdentifier(name: String): inox.Identifier
  }

  trait Args {
    def get[A: Manifest](index: Int): A
  }

  trait IR[-C, A] {
    def elaborate(context: C)(implicit store: Store, args: Args): Constrained[A]
    def extract(scrutinee: A): Matching
  }

  abstract class IRHole[-C, A: Manifest] extends IR[C, A] {
    val index: Int

    override def elaborate(context: C)(implicit store: Store, args: Args): Constrained[A] = {
      val arg = args.get[A](index)
      if (arg.isInstanceOf[A]) {
        Constrained.pure(arg.asInstanceOf[A])
      }
      else {
        Constrained.fail("Unexpected argument for hole.")
      }
    }
    override def extract(scrutinee: A): Matching = Matching(index -> scrutinee)
  }

  sealed trait IRSeq[-C, A] extends IR[C, Seq[A]] {
    val minSize: Int

    def ++[D <: C](that: IRSeq[D, A]): IRSeq[D, A] = IRSeqConcatenate(this, that)
  }

  implicit class IRSeqSingleton[-C, A](inner: IR[C, A]) extends IRSeq[C, A] {
    override val minSize: Int = 1

    override def elaborate(context: C)(implicit store: Store, args: Args): Constrained[Seq[A]] = for {
      elem <- inner.elaborate(context)
    } yield elem.map(Seq(_))

    override def extract(scrutinee: Seq[A]): Matching = scrutinee match {
      case Seq(elem) => inner.extract(scrutinee)
      case _ => Matching.fail
    }
  }

  trait IRSeqHole[-C, A] extends IRHole[C, Seq[A]] with IRSeq[C, A] {
    override val minSize: Int = 0

    override def elaborate(context: C)(implicit store: Store, args: Args): Constrained[Seq[A]] = args.get(index) match {
      case xs: Seq[A] => Constrained.pure(xs)
    }
  }

  case class IRSeqConcatenate[-C, A](left: IRSeq[C, A], right: IRSeq[C, A]) extends IRSeq[C, A] {
    override val minSize: Int = left.minSize + right.minSize

    override def elaborate(context: C)(implicit store: Store, args: Args): Constrained[Seq[A]] = for {
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