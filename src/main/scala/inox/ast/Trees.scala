/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

import utils._
import scala.language.implicitConversions

case object DebugSectionTrees extends DebugSection("trees")

trait Trees extends Expressions with Extractors with Types with Definitions with Printers {

  class Unsupported(t: Tree, msg: String)(implicit ctx: InoxContext)
    extends Exception(s"${t.asString(PrinterOptions.fromContext(ctx))}@${t.getPos} $msg")

  abstract class Tree extends utils.Positioned with Serializable {
    def copiedFrom(o: Tree): this.type = {
      setPos(o)
      this
    }

    // @EK: toString is considered harmful for non-internal things. Use asString(ctx) instead.

    def asString(implicit opts: PrinterOptions): String = PrettyPrinter(this, opts)

    override def toString = asString(PrinterOptions.fromContext(InoxContext.printNames))
  }

  object exprOps extends {
    private[ast] val trees: Trees.this.type = Trees.this
  } with ExprOps

  /** Represents a unique symbol in Inox.
    *
    * The name is stored in the decoded (source code) form rather than encoded (JVM) form.
    * The type may be left blank (Untyped) for Identifiers that are not variables.
    */
  class Identifier private[Trees](
    val name: String,
    val globalId: Int,
    private[Trees] val id: Int,
    private val alwaysShowUniqueID: Boolean = false
  ) extends Tree with Ordered[Identifier] {

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

    def freshen: Identifier = FreshIdentifier(name, alwaysShowUniqueID).copiedFrom(this)

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
      * @param tpe The type of the identifier
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
      * @param tpe The type of the identifier
      */
    def forceId(name: String, forceId: Int, alwaysShowUniqueID: Boolean = false): Identifier =
      new Identifier(decode(name), uniqueCounter.nextGlobal, forceId, alwaysShowUniqueID)
  }

  def aliased(id1: Identifier, id2: Identifier) = {
    id1.toString == id2.toString
  }

  /** Returns true if the two group of identifiers ovelap. */
  def aliased(ids1: Set[Identifier], ids2: Set[Identifier]) = {
    val s1 = ids1.groupBy{ _.toString }.keySet
    val s2 = ids2.groupBy{ _.toString }.keySet
    (s1 & s2).nonEmpty
  }

  def aliasedSymbols[T1 <: VariableSymbol,T2 <: VariableSymbol](vs1: Set[T1], vs2: Set[T2]): Boolean = {
    aliased(vs1.map(_.id), vs2.map(_.id))
  }
}
