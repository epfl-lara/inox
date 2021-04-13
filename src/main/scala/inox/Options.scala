/* Copyright 2009-2018 EPFL, Lausanne */

package inox

import OptionParsers._

import scala.util.Try
import scala.reflect.ClassTag
import scala.concurrent.duration._

object DebugSectionOptions extends DebugSection("options")

abstract class OptionDef[A] {
  val name: String
  def default: A
  def parser: OptionParser[A]
  def usageRhs: String

  def usageDesc = {
    if (usageRhs.isEmpty) s"--$name"
    else s"--$name=$usageRhs"
  }

  def formatDefault: String = default.toString

  private def parseValue(s: String)(implicit reporter: Reporter): A = {
    parser(s).getOrElse(
      reporter.fatalError(
        s"Invalid option usage: --$name=$s\n" +
        "Try '--help' for more information."
      )
    )
  }

  def parse(s: String)(implicit reporter: Reporter): OptionValue[A] =
    OptionValue(this)(parseValue(s))

  def withDefaultValue: OptionValue[A] =
    OptionValue(this)(default)

  def apply(value: A): OptionValue[A] = OptionValue(this)(value)

  override def equals(other: Any) = other match {
    case that: OptionDef[_] => this.name == that.name
    case _ => false
  }

  override def hashCode = name.hashCode
}

case class FlagOptionDef(name: String, default: Boolean) extends OptionDef[Boolean] {
  val parser = booleanParser
  val usageRhs = "true|false"
  override def usageDesc = {
    s"--$name[=$usageRhs]"
  }
}

case class MarkerOptionDef(name: String) extends OptionDef[Boolean] {
  val default = false
  val parser = (s: String) => if (s.isEmpty) Some(true) else None
  val usageRhs = ""
  override def formatDefault = ""
}

case class StringOptionDef(name: String, default: String, usageRhs: String) extends OptionDef[String] {
  val parser = stringParser
}

case class LongOptionDef(name: String, default: Long, usageRhs: String) extends OptionDef[Long] {
  val parser = longParser
}

case class IntOptionDef(name: String, default: Int, usageRhs: String) extends OptionDef[Int] {
  val parser = intParser
}

case class DoubleOptionDef(name: String, default: Double, usageRhs: String) extends OptionDef[Double] {
  val parser = doubleParser
}

abstract class SetOptionDef[A] extends OptionDef[Set[A]] {
  val elementParser: OptionParser[A]
  def parser = setParser(elementParser)
  override def formatDefault = if (default.isEmpty) "<none>" else default.mkString(",")
}

abstract class SeqOptionDef[A] extends OptionDef[Seq[A]] {
  val elementParser: OptionParser[A]
  def parser = seqParser(elementParser)
  override def formatDefault = if (default.isEmpty) "<none>" else default.mkString(",")
}

class OptionValue[A] private (val optionDef: OptionDef[A], val value: A) {
  override def toString = s"--${optionDef.name}=$value"
  override def equals(other: Any) = other match {
    case OptionValue(optionDef, value) =>
      optionDef.name == this.optionDef.name && value == this.value
    case _ => false
  }
  override def hashCode = optionDef.hashCode + value.hashCode
}

object OptionValue {
  def apply[A](optionDef: OptionDef[A])(value: A) = {
    new OptionValue(optionDef, value)
  }
  def unapply[A](opt: OptionValue[A]) = Some((opt.optionDef, opt.value))
}

object OptionParsers {
  type OptionParser[A] = String => Option[A]

  val intParser: OptionParser[Int] = { s => Try(s.toInt).toOption }
  val longParser: OptionParser[Long] = { s => Try(s.toLong).toOption }
  val doubleParser: OptionParser[Double] = { s => Try(s.toDouble).toOption }
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

  private val matcher = s"--(.*?)=(.*)".r
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

case class Options(options: Seq[OptionValue[_]]) {

  def findOption[A: ClassTag](optDef: OptionDef[A]): Option[A] = options.collectFirst {
    case OptionValue(`optDef`, value: A) => value
  }

  def findOptionOrDefault[A: ClassTag](optDef: OptionDef[A]): A = findOption(optDef).getOrElse(optDef.default)

  def +(newOpt: OptionValue[_]): Options = Options(
    options.filter(_.optionDef != newOpt.optionDef) :+ newOpt
  )

  def ++(newOpts: Seq[OptionValue[_]]): Options = Options {
    val defs = newOpts.map(_.optionDef).toSet
    options.filter(opt => !defs(opt.optionDef)) ++ newOpts
  }

  @inline
  def ++(that: Options): Options = this ++ that.options
}

object Options {
  def empty: Options = Options(Seq())
}

object optTimeout extends OptionDef[Duration] {
  val name = "timeout"
  val default = 0.0.seconds
  val parser: OptionParser[Duration] = { s => doubleParser(s).map(_.seconds) }
  val usageRhs = "t"

  def apply(secs: Double): OptionValue[Duration] = apply(secs.seconds)
}

object optSelectedSolvers extends SetOptionDef[String] {
  val name = "solvers"
  val default = Set("nativez3")
  val elementParser: OptionParser[String] = { s =>
    stringParser(s).filter(solvers.SolverFactory.solverNames contains _)
  }

  val usageRhs = "s1,s2,..."

  override def formatDefault: String = default.mkString(",")
}

object optNoColors extends inox.FlagOptionDef("no-colors", false)
