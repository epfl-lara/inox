/* Copyright 2009-2016 EPFL, Lausanne */

package inox

import OptionParsers._

import scala.util.Try
import scala.reflect.ClassTag

abstract class InoxOptionDef[+A] {
  val name: String
  val description: String
  def default: A
  val parser: OptionParser[A]
  val usageRhs: String

  def usageDesc = {
    if (usageRhs.isEmpty) s"--$name"
    else s"--$name=$usageRhs"
  }

  def helpString = {
    f"$usageDesc%-28s" + description.replaceAll("\n", "\n" + " " * 28)
  }

  private def parseValue(s: String)(implicit reporter: Reporter): A = {
    parser(s).getOrElse(
      reporter.fatalError(
        s"Invalid option usage: --$name\n" +
        "Try 'leon --help' for more information."
      )
    )
  }

  def parse(s: String)(implicit reporter: Reporter): InoxOption[A] =
    InoxOption(this)(parseValue(s))

  def withDefaultValue: InoxOption[A] =
    InoxOption(this)(default)

  // @mk: FIXME: Is this cool?
  override def equals(other: Any) = other match {
    case that: InoxOptionDef[_] => this.name == that.name
    case _ => false
  }

  override def hashCode = name.hashCode
}

case class InoxFlagOptionDef(name: String, description: String, default: Boolean) extends InoxOptionDef[Boolean] {
  val parser = booleanParser
  val usageRhs = ""
}

case class InoxStringOptionDef(name: String, description: String, default: String, usageRhs: String) extends InoxOptionDef[String] {
  val parser = stringParser
}

case class InoxLongOptionDef(name: String, description: String, default: Long, usageRhs: String) extends InoxOptionDef[Long] {
  val parser = longParser
}

class InoxOption[+A] private (val optionDef: InoxOptionDef[A], val value: A) {
  override def toString = s"--${optionDef.name}=$value"
  override def equals(other: Any) = other match {
    case InoxOption(optionDef, value) =>
      optionDef.name == this.optionDef.name && value == this.value
    case _ => false
  }
  override def hashCode = optionDef.hashCode + value.hashCode
}

object InoxOption {
  def apply[A](optionDef: InoxOptionDef[A])(value: A) = {
    new InoxOption(optionDef, value)
  }
  def unapply[A](opt: InoxOption[A]) = Some((opt.optionDef, opt.value))
}

object OptionParsers {
  type OptionParser[A] = String => Option[A]

  val longParser: OptionParser[Long] = { s =>
    Try(s.toLong).toOption
  }
  val stringParser: OptionParser[String] = Some(_)
  val booleanParser: OptionParser[Boolean] = {
    case "on"  | "true"  | "yes" | "" => Some(true)
    case "off" | "false" | "no"       => Some(false)
    case _  => None
  }

  def seqParser[A](base: OptionParser[A]): OptionParser[Seq[A]] = s => {
    @inline def foo: Option[Seq[A]] = Some(
      s.split(",")
        .filter(_.nonEmpty)
        .map(base andThen (_.getOrElse(return None)))
    )
    foo
  }

  def setParser[A](base: OptionParser[A]): OptionParser[Set[A]] = {
    seqParser(base)(_).map(_.toSet)
  }
}

object OptionsHelpers {

  private val matcher = s"--(.*)=(.*)".r
  private val matcherWithout = s"--(.*)".r

  def nameValue(s: String) = s match {
    case matcher(name, value) => Some(name, value)
    case matcherWithout(name) => Some(name, "")
    case _ => None
  }

  // helper for options that include patterns

  def matcher(patterns: Traversable[String]): String => Boolean = {
    val regexPatterns = patterns map { s =>
      import java.util.regex.Pattern

      // wildcards become ".*", rest is quoted.
      var p = s.split("_").toList.map(Pattern.quote).mkString(".*")

      // We account for _ at begining and end
      if (s.endsWith("_")) {
        p += ".*"
      }

      if (s.startsWith("_")) {
        p = ".*"+p
      }

      // Finally, we match qualified suffixes (e.g. searching for 'size' will
      // match 'List.size' but not 'thesize')
      Pattern.compile("(.+\\.)?"+p)
    }

    (name: String) => regexPatterns.exists(p => p.matcher(name).matches())
  }

  def filterInclusive[T](included: Option[T => Boolean], excluded: Option[T => Boolean]): T => Boolean = {
    included match {
      case Some(i) =>
        i
      case None =>
        excluded match {
          case Some(f) => (t: T) => !f(t)
          case None    => (t: T) => true
        }
    }
  }
}

case class InoxOptions(options: Seq[InoxOption[Any]]) {

  def findOption[A: ClassTag](optDef: InoxOptionDef[A]): Option[A] = options.collectFirst {
    case InoxOption(`optDef`, value: A) => value
  }

  def findOptionOrDefault[A: ClassTag](optDef: InoxOptionDef[A]): A = findOption(optDef).getOrElse(optDef.default)

  def +(newOpt: InoxOption[Any]): InoxOptions = InoxOptions(
    options.filter(_.optionDef != newOpt.optionDef) :+ newOpt
  )

  def ++(newOpts: Seq[InoxOption[Any]]): InoxOptions = InoxOptions {
    val defs = newOpts.map(_.optionDef).toSet
    options.filter(opt => !defs(opt.optionDef)) ++ newOpts
  }

  @inline
  def ++(that: InoxOptions): InoxOptions = this ++ that.options
}

object InoxOptions {

  def empty: InoxOptions = InoxOptions(Seq())

  val optSelectedSolvers = new InoxOptionDef[Set[String]] {
    val name = "solvers"
    val description = "Use solvers s1, s2,...\n" +
      solvers.SolverFactory.solversPretty
    val default = Set("nativez3")
    val parser = setParser(stringParser)
    val usageRhs = "s1,s2,..."
  }

  val optDebug = new InoxOptionDef[Set[DebugSection]] {
    import OptionParsers._
    val name = "debug"
    val description = {
      /*
      val sects = DebugSections.all.toSeq.map(_.name).sorted
      val (first, second) = sects.splitAt(sects.length/2 + 1)
      */
      "Enable detailed messages per component." /* +
      "\nAvailable:\n" +
        "  " + first.mkString(", ") + ",\n" +
        "  " + second.mkString(", ")*/
    }
    val default = Set[DebugSection]()
    val usageRhs = "d1,d2,..."
    private val debugParser: OptionParser[Set[DebugSection]] = s => {
      /*
      if (s == "all") {
        Some(DebugSections.all)
      } else {
        DebugSections.all.find(_.name == s).map(Set(_))
      }*/
     None

    }
    val parser: String => Option[Set[DebugSection]] = {
      setParser[Set[DebugSection]](debugParser)(_).map(_.flatten)
    }
  }

  val optTimeout = InoxLongOptionDef(
    "timeout",
    "Set a timeout for attempting to prove a verification condition/ repair a function (in sec.)",
    0L,
    "t"
  )
}
