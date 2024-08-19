/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

import utils._
import org.apache.commons.lang3.StringEscapeUtils
import scala.language.implicitConversions

object optPrintPositions extends FlagOptionDef("print-positions", false)
object optPrintUniqueIds extends FlagOptionDef("print-ids",       false)
object optPrintTypes     extends FlagOptionDef("print-types",     false)
object optPrintUnicode   extends FlagOptionDef("print-unicode",   false)

trait Printers { self: Trees =>

  val printer: Printer { val trees: self.type }

  case class PrinterContext(current: Tree,
                            parents: List[Tree],
                            lvl: Int,
                            opts: PrinterOptions,
                            sb: StringBuffer = new StringBuffer) {

    def parent = parents.headOption
  }

  case class PrinterOptions(baseIndent: Int = 0,
                            printPositions: Boolean = false,
                            printUniqueIds: Boolean = false,
                            printTypes: Boolean = false,
                            printChooses: Boolean = false,
                            printUnicode: Boolean = false,
                            symbols: Option[Symbols] = None) {
    require(
      !printTypes || symbols.isDefined,
      "Can't print types without an available symbol table"
    )
  }

  object PrinterOptions {
    def fromContext(ctx: Context, symbols: Option[Symbols] = None): PrinterOptions = {
      PrinterOptions(
        baseIndent = 0,
        printPositions = ctx.options.findOptionOrDefault(optPrintPositions),
        printUniqueIds = ctx.options.findOptionOrDefault(optPrintUniqueIds),
        printTypes = ctx.options.findOptionOrDefault(optPrintTypes) && symbols.isDefined,
        printChooses = ctx.options.findOptionOrDefault(optPrintChooses),
        printUnicode = ctx.options.findOptionOrDefault(optPrintUnicode),
        symbols = symbols
      )
    }

    def fromSymbols(s: Symbols, ctx: Context): PrinterOptions = {
      fromContext(ctx, symbols = Some(s))
    }
  }

  trait Printable {
    def asString(using opts: PrinterOptions): String
  }

  def asString(obj: Any)(using opts: PrinterOptions): String = obj match {
    case tree: Tree => prettyPrint(tree, opts)
    case id: Identifier => id.asString
    case _ => obj.toString
  }

  def prettyPrint(tree: Tree, opts: PrinterOptions = PrinterOptions()): String = {
    val ctx = PrinterContext(tree, Nil, opts.baseIndent, opts)
    printer.pp(tree)(using ctx)
    ctx.sb.toString
  }
}

trait Printer {
  protected val trees: Trees
  import trees._

  protected def optP(body: => Any)(using ctx: PrinterContext) = {
    if (requiresParentheses(ctx.current, ctx.parent)) {
      ctx.sb.append("(")
      body
      ctx.sb.append(")")
    } else {
      body
    }
  }

  private val dbquote = "\""
  private val notUC = "\u00AC"
  private val neqUC = "\u2260"
  private val notInUC = "\u2209"
  private val inUC = "\u2208"
  private val subsetUC = "\u2286"
  private val notSubsetUC = "\u2288"
  private val unionUC = "\u222A"
  private val interUC = "\u2229"
  private val forallUC = "\u2200"

  def pp(tree: Tree)(using ctx: PrinterContext): Unit = {
    if (requiresBraces(tree, ctx.parent) && !ctx.parent.contains(tree)) {
      p"""|{
          |  $tree
          |}"""
    } else {
      ppPrefix(tree)
      ppBody(tree)
      ppSuffix(tree)
    }
  }

  protected def ppPrefix(tree: Tree)(using ctx: PrinterContext): Unit = {
    if (ctx.opts.printTypes) {
      tree match {
        case t: Expr =>
          p"⟨"

        case _ =>
      }
    }
  }

  protected def ppBody(tree: Tree)(using ctx: PrinterContext): Unit = tree match {
    case Variable(id, _, _) =>
      p"$id"

    case Let(vd, expr, SubString(v2: Variable, start, StringLength(v3: Variable))) if vd.toVariable == v2 && v2 == v3 =>
      p"$expr.substring($start)"

    case Let(b, d, e) =>
      p"""|val $b = $d
          |$e"""

    case Forall(args, e) =>
      ppForall(args, e)

    case Choose(res, pred) =>
      p"choose(($res) => $pred)"

    case Assume(pred, body) =>
      p"""|assume($pred)
          |$body"""

    case e @ ADT(id, tps, args) =>
      p"$id${nary(tps, ", ", "[", "]")}($args)"

    case And(exprs) => optP {
      p"${nary(exprs, " && ")}"
    }
    case Or(exprs) => optP {
      p"${nary(exprs, "| || ")}"
    } // Ugliness award! The first | is there to shield from stripMargin()
    case Not(Equals(l, r)) => optP {
      ppNeq(l, r)
    }
    case Implies(l, r) => optP {
      p"$l ==> $r"
    }
    case UMinus(expr) => p"-$expr"
    case Equals(l, r) => optP {
      p"$l == $r"
    }

    case StringConcat(lhs, rhs) => optP {
      p"$lhs + $rhs"
    }
    case SubString(expr, start, end) => p"$expr.substring($start, $end)"
    case StringLength(expr) => p"$expr.length"

    case Int8Literal(v) => p"$v"
    case Int16Literal(v) => p"$v"
    case Int32Literal(v) => p"$v"
    case Int64Literal(v) => p"$v"
    case BVLiteral(_, bits, size) => p"x${(size to 1 by -1).map(i => if (bits(i)) "1" else "0").mkString("")}"
    case IntegerLiteral(v) => p"$v"
    case FractionLiteral(n, d) =>
      if (d == 1) p"$n"
      else p"$n/$d"
    case CharLiteral(v) => p"'${StringEscapeUtils.escapeJava(v.toString)}'"
    case BooleanLiteral(v) => p"$v"
    case UnitLiteral() => p"()"
    case StringLiteral(v) =>
      if (v.count(c => c == '\n') >= 1 && v.length >= 80 && v.indexOf("\"\"\"") == -1) {
        p"$dbquote$dbquote$dbquote$v$dbquote$dbquote$dbquote"
      } else {
        val escaped = StringEscapeUtils.escapeJava(v)
        p"$dbquote$escaped$dbquote"
      }
    case GenericValue(tp, id) => p"$tp#$id"
    case Tuple(exprs) => p"($exprs)"
    case TupleSelect(t, i) => p"$t._$i"
    case IsConstructor(e, id) => p"$e is $id"
    case ADTSelector(e, id) => p"$e.$id"

    case FunctionInvocation(id, tps, args) =>
      p"$id${nary(tps, ", ", "[", "]")}"
      if (args.nonEmpty) {
        p"($args)"
      }

    case Application(caller, args) =>
      p"$caller($args)"

    case Lambda(Seq(vd), FunctionInvocation(id, Seq(), Seq(arg))) if vd.toVariable == arg =>
      p"$id"

    case Lambda(args, body) =>
      optP {
        p"($args) => $body"
      }

    case Plus(l, r) => optP {
      p"$l + $r"
    }
    case Minus(l, r) => optP {
      p"$l - $r"
    }
    case Times(l, r) => optP {
      p"$l * $r"
    }
    case Division(l, r) => optP {
      p"$l / $r"
    }
    case Remainder(l, r) => optP {
      p"$l % $r"
    }
    case Modulo(l, r) => optP {
      p"$l mod $r"
    }
    case LessThan(l, r) => optP {
      p"$l < $r"
    }
    case GreaterThan(l, r) => optP {
      p"$l > $r"
    }
    case LessEquals(l, r) => optP {
      p"$l <= $r"
    }
    case GreaterEquals(l, r) => optP {
      p"$l >= $r"
    }
    case BVNot(e) => optP {
      p"~$e"
    }
    case BVXor(l, r) => optP {
      p"$l ^ $r"
    }
    case BVOr(l, r) => optP {
      p"$l | $r"
    }
    case BVAnd(l, r) => optP {
      p"$l & $r"
    }
    case BVShiftLeft(l, r) => optP {
      p"$l << $r"
    }
    case BVAShiftRight(l, r) => optP {
      p"$l >> $r"
    }
    case BVLShiftRight(l, r) => optP {
      p"$l >>> $r"
    }

    case BVNarrowingCast(e, Int8Type())  => p"$e.toByte"
    case BVNarrowingCast(e, Int16Type()) => p"$e.toShort"
    case BVNarrowingCast(e, Int32Type()) => p"$e.toInt"
    case BVNarrowingCast(e, Int64Type()) => p"$e.toLong"
    case BVNarrowingCast(e, BVType(_, size)) => p"$e.toBV($size)"
    case BVWideningCast(e, Int8Type())  => p"$e.toByte"
    case BVWideningCast(e, Int16Type()) => p"$e.toShort"
    case BVWideningCast(e, Int32Type()) => p"$e.toInt"
    case BVWideningCast(e, Int64Type()) => p"$e.toLong"
    case BVWideningCast(e, BVType(_, size)) => p"$e.toBV($size)"
    case BVUnsignedToSigned(e) => p"$e.toSigned"
    case BVSignedToUnsigned(e) => p"$e.toUnsigned"

    case fs @ FiniteSet(rs, _) => p"Set(${rs})"
    case fs @ FiniteBag(rs, _) => p"Bag(${rs.toSeq})"
    case fm @ FiniteMap(rs, dflt, _, _) =>
      if (rs.isEmpty) {
        p"{* -> $dflt}"
      } else {
        p"{${rs.toSeq}, * -> $dflt}"
      }
    case Not(ElementOfSet(e, s)) => ppNotIn(e, s)
    case ElementOfSet(e, s) => ppIn(e, s)
    case SubsetOf(l, r) => ppSubset(l, r)
    case Not(SubsetOf(l, r)) => ppNotSubset(l, r)
    case SetAdd(s, e) => ppSetAdd(s, e)
    case SetUnion(l, r) => ppSetUnion(l, r)
    case BagUnion(l, r) => ppSetUnion(l, r)
    case SetDifference(l, r) => p"$l \\ $r"
    case BagDifference(l, r) => p"$l \\ $r"
    case SetIntersection(l, r) => ppSetInter(l, r)
    case BagIntersection(l, r) => ppSetInter(l, r)
    case BagAdd(b, e) => p"$b + $e"
    case MultiplicityInBag(e, b) => p"$b($e)"
    case MapApply(m, k) => p"$m($k)"
    case MapUpdated(m, k, v) => p"$m.updated($k, $v)"
    case MapMerge(mask, m1, m2) => p"$mask.mapMerge($m1, $m2)"

    case Not(expr) => ppNot(expr)

    case vd @ ValDef(id, tpe, flags) =>
      if (flags.isEmpty) {
        p"$id: $tpe"
      } else {
        p"($id: $tpe)"
        for (f <- flags) p" @${f.asString(using ctx.opts)}"
      }

    case (tfd: TypedFunDef) => p"typed def ${tfd.id}[${tfd.tps}]"
    case (afd: TypedADTSort) => p"typed class ${afd.id}[${afd.tps}]"
    case (afd: TypedADTConstructor) => p"typed class ${afd.id}[${afd.tps}]"

    case tpd: TypeParameterDef =>
      p"${tpd.tp}"

    case TypeParameter(id, flags) =>
      p"$id"
      for (f <- flags) p" @${f.asString(using ctx.opts)}"

    case IfExpr(c, t, ie: IfExpr) =>
      optP {
        p"""|if ($c) {
            |  $t
            |} else $ie"""
      }

    case IfExpr(c, t, e) =>
      optP {
        p"""|if ($c) {
            |  $t
            |} else {
            |  $e
            |}"""
      }

    // Types
    case Untyped => p"<untyped>"
    case UnitType() => p"Unit"
    case Int8Type() => p"Byte"
    case Int16Type() => p"Short"
    case Int32Type() => p"Int"
    case Int64Type() => p"Long"
    case BVType(true, size) => p"Int$size"
    case BVType(false, size) => p"UInt$size"
    case IntegerType() => p"BigInt"
    case RealType() => p"Real"
    case CharType() => p"Char"
    case BooleanType() => p"Boolean"
    case StringType() => p"String"
    case SetType(bt) => p"Set[$bt]"
    case BagType(bt) => p"Bag[$bt]"
    case MapType(ft, tt) => p"Map[$ft, $tt]"
    case TupleType(tpes) => p"($tpes)"
    case FunctionType(fts, tt) => p"($fts) => $tt"
    case adt: ADTType =>
      p"${adt.id}${nary(adt.tps, ", ", "[", "]")}"

    case RefinementType(vd, pred) =>
      p"|{ $vd "
      ctx.sb.append("|")
      p"| $pred }"

    case PiType(params, to) => p"($params) => $to"
    case SigmaType(params, to) => p"($params, $to)"

    // Definitions
    case sort: ADTSort =>
      for (an <- sort.flags) p"""|@${an.asString(using ctx.opts)}
                                 |"""
      p"abstract class ${sort.id}"
      if (sort.tparams.nonEmpty) p"${nary(sort.tparams, ", ", "[", "]")}"
      for (cons <- sort.constructors) {
        p"""|
            |case class ${cons.id}"""
        if (sort.tparams.nonEmpty) p"${nary(sort.tparams, ", ", "[", "]")}"
        p"(${cons.fields})"
        p" extends ${sort.id}"
        if (sort.tparams.nonEmpty) p"${nary(sort.tparams.map(_.tp), ", ", "[", "]")}"
      }

    case cons: ADTConstructor =>
      val optTparams =
        ctx.opts.symbols.flatMap(_.lookupSort(cons.sort))
          .map(_.tparams).filter(_.nonEmpty)

      p"case class ${cons.id}"
      p"(${cons.fields})"
      optTparams.foreach(tparams => p"${nary(tparams, ", ", "[", "]")}")
      p" extends ${cons.sort}"
      optTparams.foreach(tparams => p"${nary(tparams.map(_.tp), ", ", "[", "]")}")

    case fd: FunDef =>
      for (an <- fd.flags) {
        p"""|@${an.asString(using ctx.opts)}
            |"""
      }

      p"def ${fd.id}${nary(fd.tparams, ", ", "[", "]")}"
      if (fd.params.nonEmpty) {
        p"(${fd.params})"
      }

      p": ${fd.returnType} = "
      p"${fd.fullBody}"

    case _ => ctx.sb.append("Tree? (" + tree.getClass + ")")
  }

  protected def ppSuffix(tree: Tree)(using ctx: PrinterContext): Unit = {
    if (ctx.opts.printTypes) {
      tree match {
        case t: Expr =>
          p" : ${t.getType(using ctx.opts.symbols.get)} ⟩"

        case _ =>
      }
    }
    if (ctx.opts.printPositions) {
      tree.getPos match {
        case op: OffsetPosition =>
          p"@($op)"
        case rp: RangePosition =>
          if (rp.lineFrom == rp.lineTo) {
            if (rp.colFrom == rp.colTo) {
              p"@(${rp.lineFrom}:${rp.colFrom})"
            } else {
              p"@(${rp.lineFrom}:${rp.colFrom}-${rp.colTo})"
            }
          } else {
            p"@(${rp.focusBegin}-${rp.focusEnd})"
          }
        case _ =>
          p"@(?)"
      }
    }
  }

  protected def isSimpleExpr(e: Expr): Boolean = e match {
    case _: Let => false
    case _: Assume => false
    case _ => true
  }

  protected def noBracesSub(e: Tree): Seq[Expr] = e match {
    case Let(_, _, bd) => Seq(bd)
    case IfExpr(_, t, e) => Seq(t, e) // if-else always has braces anyway
    case Assume(_, bd) => Seq(bd)
    case _ => Seq()
  }

  protected def requiresBraces(ex: Tree, within: Option[Tree]) = (ex, within) match {
    case (e: Expr, _) if isSimpleExpr(e) => false
    case (e: Expr, Some(within)) if noBracesSub(within) contains e => false
    case (e: Expr, Some(_)) => true
    case _ => false
  }

  protected def precedence(ex: Expr): Int = ex match {
    // 0: Letters
    case (_: ElementOfSet | _: Modulo) => 0
    // 1: |
    case (_: Or | _: BVOr) => 1
    // 2: ^
    case (_: BVXor) => 2
    // 3: &
    case (_: And | _: BVAnd | _: SetIntersection) => 3
    // 4: < >
    case (
      _: GreaterThan | _: GreaterEquals | _: LessEquals | _: LessThan |
      _: BVAShiftRight | _: BVLShiftRight | _: BVShiftLeft
      ) => 4
    // 5: = !
    case (_: Equals | _: Not | _: Implies) => 5
    // 6: :
    // 7: + -
    case (_: Plus | _: Minus | _: SetUnion | _: SetDifference | _: StringConcat) => 7
    // 8: * / %
    case (_: Times | _: Division | _: Remainder) => 8
    // 9: Other special characters
    case _ => 9
  }

  protected def requiresParentheses(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
    case (_, None) => false
    case (_, Some(
      _: Definition | _: Let | _: IfExpr | _: ADT | _: Lambda | _: Choose | _: Tuple | _: Assume
    )) => false
    case (ex: StringConcat, Some(_: StringConcat)) => false
    case (_, Some(_: FunctionInvocation)) => false
    case (ie: IfExpr, _) => true
    case (e1: Expr, Some(e2: Expr)) if precedence(e1) > precedence(e2) => false
    case (_, _) => true
  }

  protected def ppNot(e: Tree)(using pc: PrinterContext): Unit =
    if (pc.opts.printUnicode) p"$notUC$e"
    else p"!$e"

  protected def ppNeq(l: Tree, r: Tree)(using pc: PrinterContext): Unit =
    if (pc.opts.printUnicode) p"$l $neqUC $r"
    else p"$l != $r"

  protected def ppNotIn(e: Tree, s: Tree)(using pc: PrinterContext): Unit =
    if (pc.opts.printUnicode) p"$e $notInUC $s"
    else p"!$s.contains($e)"

  protected def ppIn(e: Tree, s: Tree)(using pc: PrinterContext): Unit =
    if (pc.opts.printUnicode) p"$e $inUC $s"
    else p"$s.contains($e)"

  protected def ppSubset(l: Tree, r: Tree)(using pc: PrinterContext): Unit =
    if (pc.opts.printUnicode) p"$l $subsetUC $r"
    else p"$l.subsetOf($r)"

  protected def ppNotSubset(l: Tree, r: Tree)(using pc: PrinterContext): Unit =
    if (pc.opts.printUnicode) p"$l $notSubsetUC $r"
    else p"!$l.subsetOf($r)"

  protected def ppSetAdd(s: Tree, e: Tree)(using pc: PrinterContext): Unit =
    if (pc.opts.printUnicode) p"$s $unionUC {$e}"
    else p"$s + $e"

  protected def ppSetUnion(l: Tree, r: Tree)(using pc: PrinterContext): Unit =
    if (pc.opts.printUnicode) p"$l $unionUC $r"
    else p"$l ++ $r"

  protected def ppSetInter(l: Tree, r: Tree)(using pc: PrinterContext): Unit =
    if (pc.opts.printUnicode) p"$l $interUC $r"
    else p"$l & $r"

  protected def ppForall(args: Seq[ValDef], e: Expr)(using pc: PrinterContext): Unit =
    if (pc.opts.printUnicode) p"$forallUC${nary(args)}. $e"
    else p"forall((${nary(args)}) => $e)"

  class PrintWrapper(val f: PrinterContext ?=> Any) {
    def print(ctx: PrinterContext) = f(using ctx)
  }

  extension (sc: StringContext) {
    def p(args: Any*)(using ctx: PrinterContext): Unit = {
      val sb = ctx.sb

      val strings = sc.parts.iterator
      val expressions = args.iterator

      var extraInd = 0
      var firstElem = true

      while (strings.hasNext) {
        val currval = strings.next()
        val s = if (currval != " || ") {
          currval.stripMargin
        } else currval

        // Compute indentation
        val start = s.lastIndexOf('\n')
        if (start >= 0 || firstElem) {
          var i = start + 1
          while (i < s.length && s(i) == ' ') {
            i += 1
          }
          extraInd = (i - start - 1) / 2
        }

        firstElem = false

        // Make sure new lines are also indented
        sb.append(s.replaceAll("\n", "\n" + ("  " * ctx.lvl)))

        val nctx = ctx.copy(lvl = ctx.lvl + extraInd)

        if (expressions.hasNext) {
          val e = expressions.next()

          e match {
            case (t1, t2) =>
              nary(Seq(t1, t2), " -> ").print(nctx)

            case ts: Seq[Any] =>
              nary(ts).print(nctx)

            case t: Tree =>
              // Don't add same tree twice in parents
              val parents = if (nctx.parents.headOption contains nctx.current) {
                nctx.parents
              } else {
                nctx.current :: nctx.parents
              }
              val nctx2 = nctx.copy(parents = parents, current = t)
              pp(t)(using nctx2)

            case id: Identifier =>
              val name = if (ctx.opts.printUniqueIds) {
                id.uniqueName
              } else {
                id.toString
              }
              p"$name"

            case p: PrintWrapper =>
              p.print(nctx)

            case e =>
              sb.append(e.toString)
          }
        }
      }
    }
  }

  def nary(ls: Seq[Any], sep: String = ", ", init: String = "", closing: String = ""): PrintWrapper = PrintWrapper {
    val (i, c) = if (ls.isEmpty) ("", "") else (init, closing)
    val strs = i +: List.fill(ls.size - 1)(sep) :+ c
    new StringContext(strs*).p(ls*)
  }

  def typed(t: Tree & Typed)(using Symbols): PrintWrapper = PrintWrapper {
    p"$t : ${t.getType}"
  }

  def typed(ts: Seq[Tree & Typed])(using Symbols): PrintWrapper = PrintWrapper {
    nary(ts.map(typed))
  }
}
