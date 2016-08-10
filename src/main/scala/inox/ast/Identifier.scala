package inox.ast

import inox.utils.UniqueCounter

/** Represents a unique symbol in Inox.
  *
  * The name is stored in the decoded (source code) form rather than encoded (JVM) form.
  * The type may be left blank (Untyped) for Identifiers that are not variables.
  */
class Identifier (
  val name: String,
  val globalId: Int,
  private val id: Int,
  private val alwaysShowUniqueID: Boolean = false
) extends Ordered[Identifier] {

  override def equals(other: Any): Boolean = other match {
    case null => false
    case i: Identifier => i.globalId == this.globalId
    case _ => false
  }

  override def hashCode: Int = globalId

  override def toString: String = {
    if (alwaysShowUniqueID) uniqueName else name
  }

  def uniqueNameDelimited(delim: String) = s"$name$delim$id"

  def uniqueName: String = uniqueNameDelimited("$")

  def freshen: Identifier = FreshIdentifier(name, alwaysShowUniqueID)

  override def compare(that: Identifier): Int = {
    val ord = implicitly[Ordering[(String, Int, Int)]]
    ord.compare(
      (this.name, this.id, this.globalId),
      (that.name, that.id, that.globalId)
    )
  }
}

object FreshIdentifier {

  private val uniqueCounter = new UniqueCounter[String]()

  // Replace $opcode inside a string with the symbolic operator name
  private def decode(s: String) =
    scala.reflect.NameTransformer.decode(s)

  /** Builds a fresh identifier
    *
    * @param name The name of the identifier
    * @param alwaysShowUniqueID If the unique ID should always be shown
    */
  def apply(name: String, alwaysShowUniqueID: Boolean = false) : Identifier = {
    val decoded = decode(name)
    new Identifier(decoded, uniqueCounter.nextGlobal, uniqueCounter.next(decoded), alwaysShowUniqueID)
  }

  /** Builds a fresh identifier, whose ID is always shown
    *
    * @param name The name of the identifier
    * @param forceId The forced ID of the identifier
    * @param alwaysShowUniqueID If the unique ID should always be shown
    */
  def forceId(name: String, forceId: Int, alwaysShowUniqueID: Boolean = false): Identifier =
    new Identifier(decode(name), uniqueCounter.nextGlobal, forceId, alwaysShowUniqueID)
}
