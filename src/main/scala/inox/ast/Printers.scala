/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

import utils._
import org.apache.commons.lang3.StringEscapeUtils
import scala.language.implicitConversions

object optPrintPositions extends FlagOptionDef("printpositions", false)
object optPrintUniqueIds extends FlagOptionDef("printids",       false)
object optPrintTypes     extends FlagOptionDef("printtypes",     false)

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
                            symbols: Option[Symbols] = None) {

    require(
      !printTypes || symbols.isDefined,
      "Can't print types without an available symbol table"
    )
  }

  object PrinterOptions {
    def fromContext(ctx: Context): PrinterOptions = {
      PrinterOptions(
        baseIndent = 0,
        printPositions = ctx.options.findOptionOrDefault(optPrintPositions),
        printUniqueIds = ctx.options.findOptionOrDefault(optPrintUniqueIds),
        printTypes = ctx.options.findOptionOrDefault(optPrintTypes),
        symbols = None
      )
    }

    def fromSymbols(s: Symbols, ctx: Context): PrinterOptions = {
      fromContext(ctx).copy(symbols = Some(s))
    }
  }

  trait Printable {
    def asString(implicit opts: PrinterOptions): String
  }

  def asString(obj: Any)(implicit opts: PrinterOptions): String = obj match {
    case tree: Tree => prettyPrint(tree, opts)
    case id: Identifier => id.asString
    case _ => obj.toString
  }

  def prettyPrint(tree: Tree, opts: PrinterOptions = PrinterOptions()): String = {
    val ctx = PrinterContext(tree, Nil, opts.baseIndent, opts)
    printer.pp(tree)(ctx)
    ctx.sb.toString
  }
}

trait Printer {
  protected val trees: Trees
  import trees._

  protected def optP(body: => Any)(implicit ctx: PrinterContext) = {
    if (requiresParentheses(ctx.current, ctx.parent)) {
      ctx.sb.append("(")
      body
      ctx.sb.append(")")
    } else {
      body
    }
  }

  private val dbquote = "\""

  def pp(tree: Tree)(implicit ctx: PrinterContext): Unit = {
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

  protected def ppPrefix(tree: Tree)(implicit ctx: PrinterContext): Unit = {
    if (ctx.opts.printTypes) {
      tree match {
        case t: Expr =>
          p"⟨"

        case _ =>
      }
    }
  }

  protected def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case Variable(id, _, _) =>
      p"$id"

    case Let(vd, expr, SubString(v2: Variable, start, StringLength(v3: Variable))) if vd.toVariable == v2 && v2 == v3 =>
      p"$expr.substring($start)"

    case Let(b, d, e) =>
      p"""|val $b = $d
          |$e"""

    case Forall(args, e) =>
      p"\u2200${nary(args)}. $e"

    case Choose(res, pred) =>
      p"choose(($res) => $pred)"

    case Assume(pred, body) =>
      p"""|assume($pred)
          |$body"""

    case e @ ADT(adt, args) =>
      p"$adt($args)"

    case And(exprs) => optP {
      p"${nary(exprs, " && ")}"
    }
    case Or(exprs) => optP {
      p"${nary(exprs, "| || ")}"
    } // Ugliness award! The first | is there to shield from stripMargin()
    case Not(Equals(l, r)) => optP {
      p"$l \u2260 $r"
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
    case BVLiteral(bits, size) => p"x${(size to 1 by -1).map(i => if (bits(i)) "1" else "0")}"
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
    case AsInstanceOf(e, ct) => p"""$e.asInstanceOf[$ct]"""
    case IsInstanceOf(e, cct) => p"$e.isInstanceOf[$cct]"
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

    case BVNarrowingCast(e, Int8Type)  => p"$e.toByte"
    case BVNarrowingCast(e, Int16Type)  => p"$e.toShort"
    case BVNarrowingCast(e, Int32Type) => p"$e.toInt"
    case BVNarrowingCast(e, Int64Type)  => p"$e.toLong"
    case BVWideningCast(e, Int8Type)   => p"$e.toByte"
    case BVWideningCast(e, Int16Type)   => p"$e.toShort"
    case BVWideningCast(e, Int32Type)  => p"$e.toInt"
    case BVWideningCast(e, Int64Type)   => p"$e.toLong"

    case fs @ FiniteSet(rs, _) => p"{${rs}}"
    case fs @ FiniteBag(rs, _) => p"{${rs.toSeq}}"
    case fm @ FiniteMap(rs, dflt, _, _) =>
      if (rs.isEmpty) {
        p"{* -> $dflt}"
      } else {
        p"{${rs.toSeq}, * -> $dflt}"
      }
    case Not(ElementOfSet(e, s)) => p"$e \u2209 $s"
    case ElementOfSet(e, s) => p"$e \u2208 $s"
    case SubsetOf(l, r) => p"$l \u2286 $r"
    case Not(SubsetOf(l, r)) => p"$l \u2288 $r"
    case SetAdd(s, e) => p"$s \u222A {$e}"
    case SetUnion(l, r) => p"$l \u222A $r"
    case BagUnion(l, r) => p"$l \u222A $r"
    case SetDifference(l, r) => p"$l \\ $r"
    case BagDifference(l, r) => p"$l \\ $r"
    case SetIntersection(l, r) => p"$l \u2229 $r"
    case BagIntersection(l, r) => p"$l \u2229 $r"
    case BagAdd(b, e) => p"$b + $e"
    case MultiplicityInBag(e, b) => p"$b($e)"
    case MapApply(m, k) => p"$m($k)"
    case MapUpdated(m, k, v) => p"$m.updated($k, $v)"

    case Not(expr) => p"\u00AC$expr"

    case vd @ ValDef(id, tpe, flags) =>
      if (flags.isEmpty) {
        p"$id: $tpe"
      } else {
        p"($id: $tpe)"
        for (f <- flags) p" @${f.asString(ctx.opts)}"
      }

    case (tfd: TypedFunDef) => p"typed def ${tfd.id}[${tfd.tps}]"
    case (afd: TypedADTDefinition) => p"typed class ${afd.id}[${afd.tps}]"

    case tpd: TypeParameterDef =>
      if (tpd.tp.isCovariant) p"+"
      else if (tpd.tp.isContravariant) p"-"
      p"${tpd.tp}"

    case TypeParameter(id, flags) =>
      p"$id"
      for (f <- flags) p" @${f.asString(ctx.opts)}"

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
    case UnitType => p"Unit"
    case Int8Type => p"Byte"
    case Int16Type => p"Short"
    case Int32Type => p"Int"
    case Int64Type => p"Long"
    case IntegerType => p"BigInt"
    case RealType => p"Real"
    case CharType => p"Char"
    case BooleanType => p"Boolean"
    case StringType => p"String"
    case SetType(bt) => p"Set[$bt]"
    case BagType(bt) => p"Bag[$bt]"
    case MapType(ft, tt) => p"Map[$ft, $tt]"
    case TupleType(tpes) => p"($tpes)"
    case FunctionType(fts, tt) => p"($fts) => $tt"
    case adt: ADTType =>
      p"${adt.id}${nary(adt.tps, ", ", "[", "]")}"

    // Definitions
    case sort: ADTSort =>
      for (an <- sort.flags) p"""|@${an.asString(ctx.opts)}
                                 |"""
      p"abstract class ${sort.id}${nary(sort.tparams, ", ", "[", "]")}"

    case cons: ADTConstructor =>
      for (an <- cons.flags) p"""|@${an.asString(ctx.opts)}
                                 |"""
      p"case class ${cons.id}"
      p"${nary(cons.tparams, ", ", "[", "]")}"
      p"(${cons.fields})"

      cons.sort.foreach { s =>
        // Remember child and parents tparams are simple bijection
        p" extends $s${nary(cons.tparams, ", ", "[", "]")}"
      }

    case fd: FunDef =>
      for (an <- fd.flags) {
        p"""|@${an.asString(ctx.opts)}
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

  protected def ppSuffix(tree: Tree)(implicit ctx: PrinterContext): Unit = {
    if (ctx.opts.printTypes) {
      tree match {
        case t: Expr =>
          p" : ${t.getType(ctx.opts.symbols.get)} ⟩"

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

  implicit class PrintWrapper(val f: PrinterContext => Any) {
    def print(ctx: PrinterContext) = f(ctx)
  }

  implicit class PrintingHelper(val sc: StringContext) {

    def p(args: Any*)(implicit ctx: PrinterContext): Unit = {
      val sb = ctx.sb

      val strings = sc.parts.iterator
      val expressions = args.iterator

      var extraInd = 0
      var firstElem = true

      while (strings.hasNext) {
        val currval = strings.next
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
          val e = expressions.next
          if (e == "||")
            println("Seen Expression: " + e)

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
              pp(t)(nctx2)

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

  def nary(ls: Seq[Any], sep: String = ", ", init: String = "", closing: String = ""): PrintWrapper = {
    val (i, c) = if (ls.isEmpty) ("", "") else (init, closing)
    val strs = i +: List.fill(ls.size - 1)(sep) :+ c

    implicit pctx: PrinterContext =>
      new StringContext(strs: _*).p(ls: _*)
  }

  def typed(t: Tree with Typed)(implicit s: Symbols): PrintWrapper = {
    implicit pctx: PrinterContext =>
      p"$t : ${t.getType}"
  }

  def typed(ts: Seq[Tree with Typed])(implicit s: Symbols): PrintWrapper = {
    nary(ts.map(typed))
  }
}
