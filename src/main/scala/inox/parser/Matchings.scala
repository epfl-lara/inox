package inox
package parser

trait Matchings {
  sealed abstract class Matching { self =>
    def getMatches(
      global: Map[String, inox.Identifier],
      local: Map[String, inox.Identifier]):
        Option[(Map[String, Identifier], Map[Int, Any])]

    def extendLocal(name: String, identifier: inox.Identifier): Matching = new Matching {
      override def getMatches(
        global: Map[String, inox.Identifier],
        local: Map[String, inox.Identifier]):
          Option[(Map[String, Identifier], Map[Int, Any])] = {

        self.getMatches(global, local + (name -> identifier))
      }
    }

    def <>(that: Matching): Matching = new Matching {
      override def getMatches(
        global: Map[String, inox.Identifier],
        local: Map[String, inox.Identifier]):
          Option[(Map[String, Identifier], Map[Int, Any])] = {

        for {
          (newGlobal, firstMap) <- self.getMatches(global, local)
          (finalGlobal, secondMap) <- that.getMatches(newGlobal, local)
        } yield (finalGlobal, firstMap ++ secondMap)
      }
    }
  }

  object Matching {
    def ensureConsistent(name: String, identifier: inox.Identifier): Matching =
      new Matching {
        override def getMatches(
          global: Map[String, inox.Identifier],
          local: Map[String, inox.Identifier]):
            Option[(Map[String, Identifier], Map[Int, Any])] = {

          local.get(name).orElse(global.get(name)) match {
            case None => Some((global + (name -> identifier), Map()))
            case Some(otherIdentifier) => if (identifier != otherIdentifier) None else Some((global, Map()))
          }
        }
      }

    // def lookup(name: String, ifFresh: => Option[(Int, inox.Identifier)])(ifBound: inox.Identifier => Option[Int]) =
    //   new Matching {
    //     override def getMatches(
    //       global: Map[String, inox.Identifier],
    //       local: Map[String, inox.Identifier]):
    //         Option[(Map[String, Identifier], Map[Int, Any])] = {

    //       local.get(name).orElse(global.get(name))) match {
    //         case None => ifFresh.map {
    //           case (index, identifier) => Some((global + (name -> identifier), Map(index -> identifier)))
    //         }
    //         case Some(identifier) => ifBound(identifier).map {
    //           case index => Some((global, Map(index -> identifier)))
    //         }
    //       }
    //     }
    //   }

    def apply(pairs: (Int, Any)*): Matching = new Matching {
      override def getMatches(
        global: Map[String, inox.Identifier],
        local: Map[String, inox.Identifier]):
          Option[(Map[String, Identifier], Map[Int, Any])] =
        Some((global, Map(pairs: _*)))
    }

    val fail: Matching = new Matching {
      override def getMatches(
        global: Map[String, inox.Identifier],
        local: Map[String, inox.Identifier]):
          Option[(Map[String, Identifier], Map[Int, Any])] = None
    }
  }
}