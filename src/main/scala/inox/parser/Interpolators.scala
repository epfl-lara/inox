package inox
package parser

import scala.reflect.macros.whitebox.Context

import scala.language.experimental.macros

trait Interpolators extends Trees

trait MacrosInterpolators extends Interpolators { self =>

  import trees._

  object Factory
    extends Elaborators
       with Extractors {
    override val trees: self.trees.type = self.trees
  }

  implicit class Interpolator(sc: StringContext)(implicit val symbols: trees.Symbols = trees.NoSymbols) {

    object t {
      def apply(args: Any*): Type = macro Macros.t_apply
      def unapply(arg: Type): Option[Any] = macro Macros.t_unapply
    }

    object e {
      def apply(args: Any*): Expr = macro Macros.e_apply
      def unapply(arg: Expr): Option[Any] = macro Macros.e_unapply
    }

    object vd {
      def apply(args: Any*): ValDef = macro Macros.vd_apply
      def unapply(arg: ValDef): Option[Any] = macro Macros.vd_unapply
    }

    object fd {
      def apply(args: Any*): FunDef = macro Macros.fd_apply
      def unapply(arg: FunDef): Option[Any] = macro Macros.fd_unapply
    }

    object td {
      def apply(args: Any*): ADTSort = macro Macros.td_apply
      def unapply(arg: ADTSort): Option[Any] = macro Macros.td_unapply
    }

    object p {
      def apply(args: Any*): Seq[Definition] = macro Macros.p_apply
    }
  }
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
          case Left(err) => throw new InterpolatorException(err)
          case Right(ir) => ExprE.elaborate(ir)(createStore(symbols, args)).get match {
            case Left(err) => throw new InterpolatorException(err)
            case Right(((_, ev), cs)) => solve(cs) match {
              case Left(err) => throw new InterpolatorException(err)
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
          case Left(err) => throw new InterpolatorException(err)
          case Right(ir) => TypeE.elaborate(ir)(createStore(symbols, args)).get match {
            case Left(err) => throw new InterpolatorException(err)
            case Right(((_, ev), cs)) => solve(cs) match {
              case Left(err) => throw new InterpolatorException(err)
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
          case Left(err) => throw new InterpolatorException(err)
          case Right(ir) => BindingE.elaborate(ir)(createStore(symbols, args)).get match {
            case Left(err) => throw new InterpolatorException(err)
            case Right((sb, cs)) => solve(cs) match {
              case Left(err) => throw new InterpolatorException(err)
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
          case Left(err) => throw new InterpolatorException(err)
          case Right(ir) => SingleFunctionE.elaborate(ir)(createStore(symbols, args)).get match {
            case Left(err) => throw new InterpolatorException(err)
            case Right((ev, cs)) => solve(cs) match {
              case Left(err) => throw new InterpolatorException(err)
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
          case Left(err) => throw new InterpolatorException(err)
          case Right(ir) => SortE.elaborate(ir)(createStore(symbols, args)).get match {
            case Left(err) => throw new InterpolatorException(err)
            case Right(((_, ev), cs)) => solve(cs) match {
              case Left(err) => throw new InterpolatorException(err)
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

    def p(args: Any*): Seq[Definition] = {
      parseSC(sc)(phrase(programParser)) match {
        case Left(err) => throw new InterpolatorException(err)
        case Right(ir) => ProgramE.elaborate(ir)(createStore(symbols, args)).get match {
          case Left(err) => throw new InterpolatorException(err)
          case Right((evs, cs)) => solve(cs) match {
            case Left(err) => throw new InterpolatorException(err)
            case Right(u) => evs.map(_.get(u))
          }
        }
      }
    }
  }
}