package inox.ast

import inox.utils.{UniqueCounter, Positioned}

/** Represents a unique symbol in Inox.
  *
  * The name is stored in the decoded (source code) form rather than encoded (JVM) form.
  * The type may be left blank (Untyped) for Identifiers that are not variables.
  *
  * Identifiers are equal when their global ids are, so two identifiers with the same
  * global id must also have the same name and id. The constructor is therefore private:
  * identifiers are built by [[FreshIdentifier]], which hands out each global id once.
  */
class Identifier private[ast] (
  val name: String,
  val globalId: Int,
  val id: Int,
  private val alwaysShowUniqueID: Boolean = false
) extends Ordered[Identifier] {

  /** Builds an identifier that shares the global id, name and id of `base`, for
    * subclasses that attach more information to an existing identifier.
    */
  protected def this(base: Identifier, alwaysShowUniqueID: Boolean) =
    this(base.name, base.globalId, base.id, alwaysShowUniqueID)

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
    val ord = summon[Ordering[(String, Int, Int)]]
    ord.compare(
      (this.name, this.id, this.globalId),
      (that.name, that.id, that.globalId)
    )
  }

  def asString(using opts: Trees#PrinterOptions): String = {
    if (opts.printUniqueIds) uniqueName else toString
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

  /** The `i`-th canonical identifier, which is the same in every process.
    *
    * Code that puts trees in a canonical form, such as to use them as cache keys, can name
    * their variables with these. Their global ids are negative, so they differ from those
    * of the identifiers built by [[apply]] and [[forceId]].
    */
  def canonical(i: Int): Identifier = {
    require(i >= 0, s"Canonical identifiers have non-negative indices, not $i")
    new Identifier("x", -1 - i, i)
  }

  /** Rebuilds an identifier that was created elsewhere, such as in the process that serialized it,
    * and makes sure that fresh identifiers never get its global id, since identifiers are equal
    * when their global ids are.
    *
    * This is the only way to build an identifier from a given global id, and it is trusted:
    * the caller must pass the name and id that the identifier had where it was created.
    * Restoring a global id that this process already uses for another name or id would
    * make two different identifiers equal.
    */
  def restore(name: String, globalId: Int, id: Int): Identifier = {
    uniqueCounter.reserveGlobal(globalId)
    new Identifier(name, globalId, id)
  }
}
