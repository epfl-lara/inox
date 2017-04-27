package inox
package parsing

sealed abstract class Level {
  val ops: Seq[String]
}
case class LeftAssoc(ops: Seq[String]) extends Level
case class RightAssoc(ops: Seq[String]) extends Level
case class AnyAssoc(op: String) extends Level {
  override val ops = Seq(op)
}

object Operators {
  val unaries: Seq[String] = Seq("-", "+", "!", "~")
  val binaries: Seq[Level] = Seq(

    LeftAssoc(Seq("*", "/", "%", "mod")),

    LeftAssoc(Seq("+", "-")),

    LeftAssoc(Seq("++")),

    LeftAssoc(Seq("∪", "∩", "∖")),

    LeftAssoc(Seq("⊆", "∈")),

    LeftAssoc(Seq("<<", ">>", ">>>")),

    LeftAssoc(Seq(">=", "<=", ">", "<")),

    LeftAssoc(Seq("==", "!=")),

    LeftAssoc(Seq("&")),

    LeftAssoc(Seq("^")),

    LeftAssoc(Seq("|")),

    AnyAssoc("&&"),

    AnyAssoc("||"),

    RightAssoc(Seq("==>")),

    RightAssoc(Seq("->"))
  )
}