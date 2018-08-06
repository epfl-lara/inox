package inox
package parser

trait Matchings {
  sealed abstract class Matching[+A] { self =>
    def getMatches(
      global: Map[String, inox.Identifier],
      local: Map[String, inox.Identifier]):
        Option[(Map[String, inox.Identifier], Map[Int, Any], A)]

    def extendLocal(name: String, identifier: inox.Identifier): Matching[A] = new Matching[A] {
      override def getMatches(
        global: Map[String, inox.Identifier],
        local: Map[String, inox.Identifier]):
          Option[(Map[String, inox.Identifier], Map[Int, Any], A)] = {

        self.getMatches(global, local + (name -> identifier))
      }
    }

    def extendLocal(pairs: Seq[(String, inox.Identifier)]): Matching[A] = new Matching[A] {
      override def getMatches(
        global: Map[String, inox.Identifier],
        local: Map[String, inox.Identifier]):
          Option[(Map[String, inox.Identifier], Map[Int, Any], A)] = {

        self.getMatches(global, pairs.foldLeft(local) { case (acc, pair) => acc + pair })
      }
    }

    def >>[B](that: Matching[B]): Matching[B] = new Matching[B] {
      override def getMatches(
        global: Map[String, inox.Identifier],
        local: Map[String, inox.Identifier]):
          Option[(Map[String, inox.Identifier], Map[Int, Any], B)] = {

        for {
          (newGlobal, firstMap, _) <- self.getMatches(global, local)
          (finalGlobal, secondMap, v) <- that.getMatches(newGlobal, local)
        } yield (finalGlobal, firstMap ++ secondMap, v)
      }
    }

    def <<[B](that: Matching[B]): Matching[A] = new Matching[A] {
      override def getMatches(
        global: Map[String, inox.Identifier],
        local: Map[String, inox.Identifier]):
          Option[(Map[String, inox.Identifier], Map[Int, Any], A)] = {

        for {
          (newGlobal, firstMap, v) <- self.getMatches(global, local)
          (finalGlobal, secondMap, _) <- that.getMatches(newGlobal, local)
        } yield (finalGlobal, firstMap ++ secondMap, v)
      }
    }

    def map[B](f: A => B): Matching[B] = new Matching[B] {
      override def getMatches(
        global: Map[String, inox.Identifier],
        local: Map[String, inox.Identifier]):
          Option[(Map[String, inox.Identifier], Map[Int, Any], B)] = {

        for {
          (newGlobal, mapping, v) <- self.getMatches(global, local)
        } yield (newGlobal, mapping, f(v))
      }
    }

    def flatMap[B](that: A => Matching[B]): Matching[B] = new Matching[B] {
      override def getMatches(
        global: Map[String, inox.Identifier],
        local: Map[String, inox.Identifier]):
          Option[(Map[String, inox.Identifier], Map[Int, Any], B)] = {

        for {
          (newGlobal, firstMap, v1) <- self.getMatches(global, local)
          (finalGlobal, secondMap, v2) <- that(v1).getMatches(newGlobal, local)
        } yield (finalGlobal, firstMap ++ secondMap, v2)
      }
    }

    def withValue[B](value: B): Matching[B] = this.map(_ => value)
  }

  object Matching {
    def ensureConsistent(name: String, identifier: inox.Identifier): Matching[Unit] =
      new Matching[Unit] {
        override def getMatches(
          global: Map[String, inox.Identifier],
          local: Map[String, inox.Identifier]):
            Option[(Map[String, inox.Identifier], Map[Int, Any], Unit)] = {

          local.get(name).orElse(global.get(name)) match {
            case None => Some((global + (name -> identifier), Map(), ()))
            case Some(otherIdentifier) => if (identifier != otherIdentifier) None else Some((global, Map(), ()))
          }
        }
      }

    def collect[A, B](scrutinee: A)(fun: PartialFunction[A, Matching[B]]): Matching[B] =
      fun.lift(scrutinee).getOrElse(Matching.fail)

    def conditionally(condition: Boolean): Matching[Unit] =
      if (condition) success else fail

    def apply(pairs: (Int, Any)*): Matching[Unit] = new Matching[Unit] {
      override def getMatches(
        global: Map[String, inox.Identifier],
        local: Map[String, inox.Identifier]):
          Option[(Map[String, inox.Identifier], Map[Int, Any], Unit)] =
        Some((global, Map(pairs: _*), ()))
    }

    def pure[A](x: A): Matching[A] = new Matching[A] {
      override def getMatches(
        global: Map[String, inox.Identifier],
        local: Map[String, inox.Identifier]):
          Option[(Map[String, inox.Identifier], Map[Int, Any], A)] = Some((global, Map(), x))
    }

    val success: Matching[Unit] = new Matching[Unit] {
      override def getMatches(
        global: Map[String, inox.Identifier],
        local: Map[String, inox.Identifier]):
          Option[(Map[String, inox.Identifier], Map[Int, Any], Unit)] = Some((global, Map(), ()))
    }

    val fail: Matching[Nothing] = new Matching[Nothing] {
      override def getMatches(
        global: Map[String, inox.Identifier],
        local: Map[String, inox.Identifier]):
          Option[(Map[String, inox.Identifier], Map[Int, Any], Nothing)] = None
    }

    def sequence[A](matchings: Seq[Matching[A]]): Matching[Seq[A]] = {

      matchings.foldLeft(Matching.pure(Seq[A]())) {
        case (acc, matching) => for {
          xs <- acc
          x  <- matching
        } yield xs :+ x
      }
    }
  }
}