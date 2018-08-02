/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

trait ExpressionExtractors { self: Extractors =>

  trait ExpressionExtractor { self0: Extractor =>

    import ExprIR._

    private type MatchObligation = Option[Match]

    protected def toIdObl(pair: (inox.Identifier, Identifier)): MatchObligation = {
      val (id, templateId) = pair

      templateId match {
        case IdentifierName(name) if name == id.name => Some(empty)
        case IdentifierHole(index) => Some(matching(index, id))
        case _ => None
      }
    }
    protected def toExprObl(pair: (trees.Expr, Expression)): MatchObligation = {
      extract(pair._1, pair._2)
    }
    protected def toTypeObl(pair: (trees.Type, Type)): MatchObligation = {
      val (tpe, template) = pair
      extract(tpe, template)
    }
    protected def toOptTypeObl(pair: (trees.Type, Option[Type])): MatchObligation = {
      val (tpe, optTemplateType) = pair

      if (optTemplateType.isEmpty) {
        Some(empty)
      }
      else {
        toTypeObl(tpe -> optTemplateType.get)
      }
    }
    protected def toExprObls(pair: (Seq[trees.Expr], Seq[Expression])): MatchObligation = {
      pair match {
        case (Seq(), Seq()) => Some(empty)
        case (Seq(), _) => None
        case (_, Seq()) => None
        case (_, Seq(ExpressionSeqHole(i), templateRest @ _*)) => {
          val n = pair._1.length - templateRest.length

          if (n < 0) {
            None
          }
          else {
            val (matches, rest) = pair._1.splitAt(n)

            toExprObls(rest -> templateRest) map {
              case matchings => matching(i, matches) ++ matchings
            }
          }
        }
        case (Seq(expr, exprRest @ _*), Seq(template, templateRest @ _*)) => for {
          matchingsHead <- extract(toExprObl(expr -> template))
          matchingsRest <- extract(toExprObls(exprRest -> templateRest))
        } yield matchingsHead ++ matchingsRest
      }
    }
    protected def toTypeObls(pair: (Seq[trees.Type], Seq[Type])): MatchObligation = {
      extractSeq(pair._1, pair._2)
    }
    protected def toOptTypeObls(pair: (Seq[trees.Type], Seq[Option[Type]])): MatchObligation = {
      val pairs = pair._1.zip(pair._2).collect {
        case (tpe, Some(template)) => toTypeObl(tpe -> template)
      }
      extract(pairs : _*)
    }
    protected def toIdObls(pair: (Seq[inox.Identifier], Seq[Identifier])): MatchObligation = {

      // TODO: Change this.
      val (ids, templatesIds) = pair

      if (ids.length == templatesIds.length) {
        extract(ids.zip(templatesIds).map(toIdObl) : _*)
      }
      else {
        None
      }
    }

    protected def extract(pairs: MatchObligation*): MatchObligation = {

      val zero: MatchObligation = Some(empty)

      pairs.foldLeft(zero) {
        case (None, _) => None
        case (Some(matchingsAcc), obligation) => {
          obligation map {
            case extraMatchings => matchingsAcc ++ extraMatchings
          }
        }
      }
    }

    def extract(expr: trees.Expr, template: Expression): MatchObligation = {

      val success = Some(empty)

      template match {
        case ExpressionHole(index) =>
          return Some(Map(index -> expr))
        case TypeAnnotationOperation(templateInner, templateType) =>
          return extract(toTypeObl(expr.getType -> templateType), toExprObl(expr -> templateInner))
        case _ => ()
      }

      expr match {

        // Variables

        case trees.Variable(inoxId, _, _) => template match {
          case Variable(templateId) => extract(toIdObl(inoxId -> templateId))
          case _ => fail
        }

        // Control structures.

        case trees.IfExpr(cond, thenn, elze) => template match {
          case Operation("IfThenElse", Seq(templateCond, templateThenn, templateElze)) =>
            extract(toExprObl(cond -> templateCond), toExprObl(thenn -> templateThenn), toExprObl(elze -> templateElze))
          case _ => fail
        }

        case trees.Assume(pred, body) => template match {
          case Operation("Assume", Seq(templatePred, templateBody)) =>
            extract(toExprObl(pred -> templatePred), toExprObl(body -> templateBody))
          case _ => fail
        }

        case trees.Let(vd, value, body) => template match {
          case Let(Seq(((templateId, optTemplateType), templateValue), rest @ _*), templateBody) => {

            val templateRest = rest match {
              case Seq() => templateBody
              case _ => Let(rest, templateBody)
            }

            extract(
              toExprObl(value -> templateValue),
              toOptTypeObl(vd.getType -> optTemplateType),
              toIdObl(vd.id -> templateId),
              toExprObl(body -> templateRest))
          }
          case _ => fail
        }

        case trees.Lambda(args, body) => template match {
          case Abstraction(Lambda, templateArgs, templateBody) =>
            extract(
              toOptTypeObls(args.map(_.getType) -> templateArgs.map(_._2)),
              toIdObls(args.map(_.id) -> templateArgs.map(_._1)),
              toExprObl(body -> templateBody))
          case _ => fail
        }

        case trees.Forall(args, body) => template match {
          case Abstraction(Forall, templateArgs, templateBody) =>
            extract(
              toOptTypeObls(args.map(_.getType) -> templateArgs.map(_._2)),
              toIdObls(args.map(_.id) -> templateArgs.map(_._1)),
              toExprObl(body -> templateBody))
          case _ => fail
        }

        case trees.Choose(arg, pred) => template match {
          case Abstraction(Choose, Seq((templateId, optTemplateType), rest @ _*), templatePred) => {
            val templateRest = rest match {
              case Seq() => templatePred
              case _ => Abstraction(Choose, rest, templatePred)
            }

            extract(
              toOptTypeObl(arg.getType -> optTemplateType),
              toIdObl(arg.id -> templateId),
              toExprObl(pred -> templateRest))
          }
          case _ => fail
        }

        // Functions.

        case trees.Application(callee, args) => template match {
          case Application(templateCallee, templateArgs) =>
            extract(toExprObl(callee -> templateCallee), toExprObls(args -> templateArgs))
          case _ => fail
        }

        case trees.FunctionInvocation(id, tpes, args) => template match {
          case Application(TypedFunDef(fd, optTemplatesTypes), templateArgs) if (id == fd.id) => {
            optTemplatesTypes match {
              case None => extract(toExprObls(args -> templateArgs))
              case Some(templateTypes) => extract(toExprObls(args -> templateArgs), toTypeObls(tpes -> templateTypes))
              case _ => fail
            }
          }
          case Application(TypeApplication(ExpressionHole(index), templateTypes), templateArgs) => for {
            matchings <- extract(toTypeObls(tpes -> templateTypes), toExprObls(args -> templateArgs))
          } yield matching(index, id) ++ matchings
          case Application(ExpressionHole(index), templateArgs) => for {
            matchings <- extract(toExprObls(args -> templateArgs))
          } yield matching(index, id) ++ matchings
          case _ => fail
        }

        // ADTs.

        case trees.ADT(id, tpes, args) => template match {
          case Application(TypedConsDef(cons, optTemplatesTypes), templateArgs) if (id == cons.id) => {
            optTemplatesTypes match {
              case None => extract(toExprObls(args -> templateArgs))
              case Some(templateTypes) => extract(toExprObls(args -> templateArgs), toTypeObls(tpes -> templateTypes))
              case _ => fail
            }
          }
          case Application(TypeApplication(ExpressionHole(index), templateTypes), templateArgs) => for {
            matchings <- extract(toTypeObls(tpes -> templateTypes), toExprObls(args -> templateArgs))
          } yield matching(index, id) ++ matchings
          case Application(ExpressionHole(index), templateArgs) => for {
            matchings <- extract(toExprObls(args -> templateArgs))
          } yield matching(index, id) ++ matchings
          case _ => fail
        }

        case trees.ADTSelector(adt, selector) => template match {
          case Selection(adtTemplate, FieldHole(index)) => for {
            matchings <- extract(toExprObl(adt -> adtTemplate))
          } yield matching(index, selector) ++ matchings
          case Selection(adtTemplate, Field((cons, vd))) if (vd.id == selector) =>  // TODO: Handle selectors with the same name.
            extract(toExprObl(adt -> adtTemplate))
          case _ => fail
        }

        // Instance checking and casting.

        case trees.IsConstructor(inner, id) => template match {
          case IsConstructorOperation(templateInner, name) if id.name == name =>
            extract(toExprObl(inner -> templateInner))
          case _ => fail
        }

        // Various.

        case trees.CharLiteral(char) => template match {
          case Literal(CharLiteral(`char`)) => success
          case _ => fail
        }

        case trees.UnitLiteral() => template match {
          case Literal(UnitLiteral) => success
          case _ => fail
        }

        case trees.Equals(left, right) => template match {
          case Operation("==", Seq(templateLeft, templateRight)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight))
          case _ => fail
        }

        // Booleans.

        case trees.BooleanLiteral(bool) => template match {
          case Literal(BooleanLiteral(`bool`)) => success
          case _ => fail
        }

        case trees.And(exprs) => template match {
          case BooleanAndOperation(templates) =>
            extract(toExprObls(exprs -> templates))
          case _ => fail
        }

        case trees.Or(exprs) => template match {
          case BooleanOrOperation(templates) =>
            extract(toExprObls(exprs -> templates))
          case _ => fail
        }

        case trees.Implies(left, right) => template match {
          case Operation("==>", Seq(templateLeft, templateRight)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight))
          case _ => fail
        }

        case trees.Not(inner) => template match {
          case Operation("!", Seq(templateInner)) => extract(toExprObl(inner -> templateInner))
          case _ => fail
        }

        // Strings.

        case trees.StringLiteral(string) => template match {
          case Literal(StringLiteral(`string`)) => success
          case _ => fail
        }

        case trees.StringConcat(left, right) => template match {
          case ConcatenateOperation(templateLeft, templateRight) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight))
          case _ => fail
        }

        case trees.SubString(string, from, to) => template match {
          case SubstringOperation(templateString, templateFrom, templateTo) =>
            extract(toExprObl(string -> templateString), toExprObl(from -> templateFrom), toExprObl(to -> templateTo))
          case _ => fail
        }

        case trees.StringLength(string) => template match {
          case StringLengthOperation(templateString) => extract(toExprObl(string -> templateString))
          case _ => fail
        }

        // Numbers.

        case trees.IntegerLiteral(value) => template match {
          case Literal(NumericLiteral(string)) if (scala.util.Try(BigInt(string)).toOption == Some(value)) => success
          case _ => fail
        }

        case trees.FractionLiteral(numerator, denominator) => template match {
          case Literal(NumericLiteral(string)) if { val n = BigInt(string); n * denominator == numerator } => success
          case Literal(DecimalLiteral(w, t, r)) if { val (n, d) = Utils.toFraction(w, t, r); n * denominator == d * numerator } => success
          case _ => fail
        }

        case trees.Plus(left, right) => template match {
          case Operation("+", Seq(templateLeft, templateRight)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight))
          case _ => fail
        }

        case trees.Minus(left, right) => template match {
          case Operation("-", Seq(templateLeft, templateRight)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight))
          case _ => fail
        }

        case trees.Times(left, right) => template match {
          case Operation("*", Seq(templateLeft, templateRight)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight))
          case _ => fail
        }

        case trees.Division(left, right) => template match {
          case Operation("/", Seq(templateLeft, templateRight)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight))
          case _ => fail
        }

        case trees.UMinus(inner) => template match {
          case Operation("-", Seq(templateInner)) => extract(toExprObl(inner -> templateInner))
          case _ => fail
        }

        case trees.Remainder(left, right) => template match {
          case Operation("%", Seq(templateLeft, templateRight)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight))
          case _ => fail
        }

        case trees.Modulo(left, right) => template match {
          case Operation("mod", Seq(templateLeft, templateRight)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight))
          case _ => fail
        }

        case trees.LessThan(left, right) => template match {
          case Operation("<", Seq(templateLeft, templateRight)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight))
          case _ => fail
        }

        case trees.GreaterThan(left, right) => template match {
          case Operation(">", Seq(templateLeft, templateRight)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight))
          case _ => fail
        }

        case trees.LessEquals(left, right) => template match {
          case Operation("<=", Seq(templateLeft, templateRight)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight))
          case _ => fail
        }

        case trees.GreaterEquals(left, right) => template match {
          case Operation(">=", Seq(templateLeft, templateRight)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight))
          case _ => fail
        }

        // Bit vectors.

        case v@trees.BVLiteral(value, base) => template match {
          case Literal(NumericLiteral(string)) if (scala.util.Try(trees.BVLiteral(BigInt(string), base)).toOption == Some(v)) => success
          case _ => fail
        }

        case trees.BVNot(inner) => template match {
          case Operation("~", Seq(templateInner)) => extract(toExprObl(inner -> templateInner))
          case _ => fail
        }

        case trees.BVOr(left, right) => template match {
          case Operation("|", Seq(templateLeft, templateRight)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight))
        }

        case trees.BVAnd(left, right) => template match {
          case Operation("&", Seq(templateLeft, templateRight)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight))
          case _ => fail
        }

        case trees.BVXor(left, right) => template match {
          case Operation("^", Seq(templateLeft, templateRight)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight))
          case _ => fail
        }

        case trees.BVShiftLeft(left, right) => template match {
          case Operation("<<", Seq(templateLeft, templateRight)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight))
          case _ => fail
        }

        case trees.BVAShiftRight(left, right) => template match {
          case Operation(">>", Seq(templateLeft, templateRight)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight))
          case _ => fail
        }

        case trees.BVLShiftRight(left, right) => template match {
          case Operation(">>>", Seq(templateLeft, templateRight)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight))
          case _ => fail
        }

        // Tuples.

        case trees.Tuple(exprs) => template match {
          case Operation("Tuple", templates) =>
            extract(toExprObls(exprs -> templates))
          case _ => fail
        }

        case trees.TupleSelect(inner, index) => template match {
          case Selection(templateInner, TupleField(`index`)) => extract(toExprObl(inner -> templateInner))
          case _ => fail
        }

        // Sets.

        case trees.FiniteSet(elements, tpe) => template match {
          case SetConstruction(templatesElements, optTemplateType) =>
            extract(toExprObls(elements -> templatesElements), toOptTypeObl(tpe -> optTemplateType))
          case _ => fail
        }

        case trees.SetAdd(set, element) => (set.getType(symbols), template) match {
          case (trees.SetType(tpe), SetAddOperation(templateSet, templateElement, optTemplateType)) =>
            extract(toExprObl(set -> templateSet), toExprObl(element -> templateElement), toOptTypeObl(tpe -> optTemplateType))
          case _ => fail
        }

        case trees.ElementOfSet(element, set) => (set.getType(symbols), template) match {
          case (trees.SetType(tpe), ContainsOperation(templateSet, templateElement, optTemplateType)) =>
            extract(toExprObl(set -> templateSet), toExprObl(element -> templateElement), toOptTypeObl(tpe -> optTemplateType))
          case _ => fail
        }

        case trees.SubsetOf(left, right) => (left.getType(symbols), template) match {
          case (trees.SetType(tpe), SubsetOperation(templateLeft, templateRight, optTemplateType)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight), toOptTypeObl(tpe -> optTemplateType))
          case _ => fail
        }

        case trees.SetIntersection(left, right) => (left.getType(symbols), template) match {
          case (trees.SetType(tpe), SetIntersectionOperation(templateLeft, templateRight, optTemplateType)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight), toOptTypeObl(tpe -> optTemplateType))
          case _ => fail
        }

        case trees.SetDifference(left, right) => (left.getType(symbols), template) match {
          case (trees.SetType(tpe), SetDifferenceOperation(templateLeft, templateRight, optTemplateType)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight), toOptTypeObl(tpe -> optTemplateType))
          case _ => fail
        }

        // Bags.

        case trees.FiniteBag(mappings, tpe) => template match {
          case BagConstruction(Bindings(Seq(), templateMappings), optTemplateType) => {
            val (keys, values) = mappings.unzip
            val (templatesKeys, templatesValues) = templateMappings.unzip

            extract(toExprObls(keys -> templatesKeys), toExprObls(values -> templatesValues), toOptTypeObl(tpe -> optTemplateType))
          }
          case _ => fail
        }

        case trees.BagAdd(bag, element) => (bag.getType(symbols), template) match {
          case (trees.BagType(tpe), BagAddOperation(templateBag, templateElement, optTemplateType)) =>
            extract(toExprObl(bag -> templateBag), toExprObl(element -> templateElement), toOptTypeObl(tpe -> optTemplateType))
          case _ => fail
        }

        case trees.MultiplicityInBag(element, bag) => (bag.getType, template) match {
          case (trees.BagType(tpe), BagMultiplicityOperation(templateBag, templateElement, optTemplateType)) =>
            extract(toExprObl(element -> templateElement), toExprObl(bag -> templateBag), toOptTypeObl(tpe -> optTemplateType))
          case _ => fail
        }

        case trees.BagIntersection(left, right) => (left.getType, template) match {
          case (trees.BagType(tpe), BagIntersectionOperation(templateLeft, templateRight, optTemplateType)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight), toOptTypeObl(tpe -> optTemplateType))
          case _ => fail
        }

        case trees.BagUnion(left, right) => (left.getType, template) match {
          case (trees.BagType(tpe), BagUnionOperation(templateLeft, templateRight, optTemplateType)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight), toOptTypeObl(tpe -> optTemplateType))
          case _ => fail
        }

        case trees.BagDifference(left, right) => (left.getType, template) match {
          case (trees.BagType(tpe), BagDifferenceOperation(templateLeft, templateRight, optTemplateType)) =>
            extract(toExprObl(left -> templateLeft), toExprObl(right -> templateRight), toOptTypeObl(tpe -> optTemplateType))
          case _ => fail
        }

        // Maps.

        case trees.FiniteMap(pairs, default, keyType, valueType) => template match {
          case MapConstruction(templateDefault, Bindings(Seq(), templatesPairs), optTemplatesTypes) => {

            val (optTemplateKeyType, optTemplateValueType) = optTemplatesTypes match {
              case Some(Right((k, v))) => (Some(k), Some(v))
              case Some(Left(k)) => (Some(k), None)
              case None => (None, None)
            }

            val (keys, values) = pairs.unzip
            val (templatesKeys, templatesValues) = templatesPairs.unzip

            extract(toExprObls(keys -> templatesKeys), toExprObls(values -> templatesValues),
              toOptTypeObl(keyType -> optTemplateKeyType), toOptTypeObl(valueType -> optTemplateValueType), toExprObl(default -> templateDefault))
          }
          case _ => fail
        }

        case trees.MapApply(map, key) => (map.getType, template) match {
          case (trees.MapType(keyType, valueType), MapApplyOperation(templateMap, templateKey, optTemplatesTypes)) => {
            val (optTemplateKeyType, optTemplateValueType) = optTemplatesTypes match {
              case Some((k, v)) => (Some(k), Some(v))
              case None => (None, None)
            }

            extract(toExprObl(map -> templateMap), toExprObl(key -> templateKey),
              toOptTypeObl(keyType -> optTemplateKeyType), toOptTypeObl(valueType -> optTemplateValueType))
          }
          case _ => fail
        }

        case trees.MapUpdated(map, key, value) => (map.getType, template) match {
          case (trees.MapType(keyType, valueType), MapUpdatedOperation(templateMap, templateKey, templateValue, optTemplatesTypes)) => {
            val (optTemplateKeyType, optTemplateValueType) = optTemplatesTypes match {
              case Some((k, v)) => (Some(k), Some(v))
              case None => (None, None)
            }

            extract(toExprObl(map -> templateMap), toExprObl(key -> templateKey), toOptTypeObl(keyType -> optTemplateKeyType),
              toExprObl(value -> templateValue), toOptTypeObl(valueType -> optTemplateValueType))
          }
          case _ => fail
        }

        case _ => fail
      }
    }
  }
}
