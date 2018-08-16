package inox
package parser

import scala.reflect.macros.whitebox.Context

import scala.language.experimental.macros

trait Interpolators {
  protected val trees: inox.ast.Trees

  type Interpolator
}

trait RunTimeInterpolators
  extends Interpolators
     with Elaborators
     with Extractors
     with Parsers {

  import trees._

  implicit class Interpolator(sc: StringContext)(implicit symbols: trees.Symbols = trees.NoSymbols) {

    object e {
      def apply(args: Any*): Expr = {
        parseSC(sc)(phrase(exprParser)) match {
          case Left(err) => throw new Exception(err)
          case Right(ir) => ExprE.elaborate(ir)(createStore(symbols, args)).get match {
            case Left(err) => throw new Exception(err)
            case Right(((_, ev), cs)) => solve(cs) match {
              case Left(err) => throw new Exception(err)
              case Right(u) => ev.get(u)
            }
          }
        }
      }

      def unapplySeq(arg: Expr): Option[Seq[Any]] = {
        parseSC(sc)(phrase(exprParser)) match {
          case Left(err) => None
          case Right(ir) => ExprX.extract(ir, arg).getMatches(symbols) match {
            case None => None
            case Some(mapping) => Some(Seq.tabulate(mapping.size) { i => mapping(i) })
          }
        }
      }
    }

    object t {
      def apply(args: Any*): Type = {
        parseSC(sc)(phrase(typeParser)) match {
          case Left(err) => throw new Exception(err)
          case Right(ir) => TypeE.elaborate(ir)(createStore(symbols, args)).get match {
            case Left(err) => throw new Exception(err)
            case Right(((_, ev), cs)) => solve(cs) match {
              case Left(err) => throw new Exception(err)
              case Right(u) => ev.get(u)
            }
          }
        }
      }

      def unapplySeq(arg: Type): Option[Seq[Any]] = {
        parseSC(sc)(phrase(typeParser)) match {
          case Left(err) => None
          case Right(ir) => TypeX.extract(ir, arg).getMatches(symbols) match {
            case None => None
            case Some(mapping) => Some(Seq.tabulate(mapping.size) { i => mapping(i) })
          }
        }
      }
    }

    object vd {
      def apply(args: Any*): ValDef = {
        parseSC(sc)(phrase(bindingParser(explicitOnly=true))) match {
          case Left(err) => throw new Exception(err)
          case Right(ir) => BindingE.elaborate(ir)(createStore(symbols, args)).get match {
            case Left(err) => throw new Exception(err)
            case Right((sb, cs)) => solve(cs) match {
              case Left(err) => throw new Exception(err)
              case Right(u) => sb.evValDef.get(u)
            }
          }
        }
      }

      def unapplySeq(arg: ValDef): Option[Seq[Any]] = {
        parseSC(sc)(phrase(bindingParser(explicitOnly=false))) match {
          case Left(err) => None
          case Right(ir) => BindingX.extract(ir, arg).getMatches(symbols) match {
            case None => None
            case Some(mapping) => Some(Seq.tabulate(mapping.size) { i => mapping(i) })
          }
        }
      }
    }

    object fd {
      def apply(args: Any*): FunDef = {
        parseSC(sc)(phrase(functionDefinitionParser)) match {
          case Left(err) => throw new Exception(err)
          case Right(ir) => SingleFunctionE.elaborate(ir)(createStore(symbols, args)).get match {
            case Left(err) => throw new Exception(err)
            case Right((ev, cs)) => solve(cs) match {
              case Left(err) => throw new Exception(err)
              case Right(u) => ev.get(u)
            }
          }
        }
      }

      def unapplySeq(arg: FunDef): Option[Seq[Any]] = {
        parseSC(sc)(phrase(functionDefinitionParser)) match {
          case Left(err) => None
          case Right(ir) => FunctionX.extract(ir, arg).getMatches(symbols) match {
            case None => None
            case Some(mapping) => Some(Seq.tabulate(mapping.size) { i => mapping(i) })
          }
        }
      }
    }

    object td {
      def apply(args: Any*): ADTSort = {
        parseSC(sc)(phrase(adtDefinitionParser)) match {
          case Left(err) => throw new Exception(err)
          case Right(ir) => SortE.elaborate(ir)(createStore(symbols, args)).get match {
            case Left(err) => throw new Exception(err)
            case Right(((_, ev), cs)) => solve(cs) match {
              case Left(err) => throw new Exception(err)
              case Right(u) => ev.get(u)
            }
          }
        }
      }

      def unapplySeq(arg: ADTSort): Option[Seq[Any]] = {
        parseSC(sc)(phrase(adtDefinitionParser)) match {
          case Left(err) => None
          case Right(ir) => SortX.extract(ir, arg).getMatches(symbols) match {
            case None => None
            case Some(mapping) => Some(Seq.tabulate(mapping.size) { i => mapping(i) })
          }
        }
      }
    }
  }
}

object CompileTimeInterpolators
  extends Interpolators
     with Elaborators
     with Extractors {

  override protected val trees = inox.trees
  import trees._

  implicit class Interpolator(sc: StringContext)(implicit val symbols: Symbols = NoSymbols) {

    object t {
      def apply(args: Any*): Type = macro CompileTimeInterpolatorsImpl.t_apply
      def unapply(arg: Type): Option[Any] = macro CompileTimeInterpolatorsImpl.t_unapply
    }

    object e {
      def apply(args: Any*): Expr = macro CompileTimeInterpolatorsImpl.e_apply
      def unapply(arg: Expr): Option[Any] = macro CompileTimeInterpolatorsImpl.e_unapply
    }
  }
}

private class CompileTimeInterpolatorsImpl(context: Context) extends Macros(context) {
  import c.universe._
  override protected lazy val targetTrees: c.Tree = q"_root_.inox.trees"
  override protected val interpolator: c.Tree = q"_root_.inox.parser.CompileTimeInterpolators"
}