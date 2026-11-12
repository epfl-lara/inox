/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import inox.OptionParsers._

object optCVC5Options extends SetOptionDef[String] {
  val name = "solver:cvc5"
  val default = Set[String]()
  val elementParser = stringParser
  val usageRhs = "<cvc5-opt>"
}

// In millions of cvc5 resource units
// An Int, so that the limit in resource units can't overflow the Long it is computed in
object optCVC5Rlimit extends IntOptionDef("cvc5-rlimit", -1, "<N>")

trait CVC5Solver extends CVCSolver with CVC5Target {
  import context.{given, _}

  override def optCVCOptions: SetOptionDef[String] = optCVC5Options

  override def interpreterOpts = {
    val rlimit = options.findOptionOrDefault(optCVC5Rlimit).toLong * 1000000L
    super.interpreterOpts ++ (if (rlimit >= 0) Seq(s"--rlimit-per=$rlimit") else Seq())
  }

  // Under `--strings-bmp`, restrict the string alphabet to the BMP (by default, cvc5 uses all
  // 0x30000 SMT-LIB characters).
  override protected def targetOpts: Seq[String] =
    if (maxStringChar == 0xFFFF) Seq("--strings-alpha-card=65536") else Seq.empty
}
