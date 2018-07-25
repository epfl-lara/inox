/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

trait TypeExtractors { self: Interpolator =>

  trait TypeExtractor extends Extractor { self0: Elaborator =>

    import TypeIR._

    def extractSeq(tpes: Seq[trees.Type], templates: Seq[Expression]): Option[Match] = (tpes, templates) match {
      case (Seq(), Seq()) => Some(empty)
      case (Seq(), _) => None
      case (_, Seq()) => None
      case (_, Seq(TypeSeqHole(i), templateRest @ _*)) =>
        val n = tpes.length - templateRest.length
        if (n < 0) None else {
          val (matches, rest) = tpes.splitAt(n)
          extractSeq(rest, templateRest) map (_ ++ matching(i, matches))
        }
      case (Seq(tpe, tpeRest @ _*), Seq(template, templateRest @ _*)) =>
        for {
          matchingsHead <- extract(tpe, template)
          matchingsRest <- extractSeq(tpeRest, templateRest)
        } yield matchingsHead ++ matchingsRest
    }

    def extractSeq(vds: Seq[trees.ValDef], templates: Seq[Expression])(implicit dummy: DummyImplicit): Option[Match] =
      (vds, templates) match {
        case (Seq(), Seq()) => Some(empty)
        case (Seq(), _) => None
        case (_, Seq()) => None
        case (_, Seq(TypeSeqHole(i), templateRest @ _*)) =>
          val n = vds.length - templateRest.length
          if (n < 0) None else {
            val (matches, rest) = vds.splitAt(n)
            extractSeq(rest, templateRest) map (_ ++ matching(i, matches))
          }
        case (Seq(vd, vdRest @ _*), Seq(template, templateRest @ _*)) =>
          for {
            matchingsHead <- extract(vd, template)
            matchingsRest <- extractSeq(vdRest, templateRest)
          } yield matchingsHead ++ matchingsRest
      }

    def extract(vd: trees.ValDef, template: Expression): Option[Match] = template match {
      case TypeBinding(id, tpe) =>
        for {
          matchingsId <- toIdObl(vd.id, id)
          matchingsTpe <- extract(vd.tpe, tpe)
        } yield matchingsId ++ matchingsTpe
      case _ => fail
    }

    def extract(tpe: trees.Type, template: Expression): Option[Match] = (template, tpe) match {
      case (TypeHole(i), _) => Some(matching(i, tpe))
      case (_, trees.Untyped) => fail
      case (Literal(Name(BVType(templateSize))), trees.BVType(size)) => if (templateSize == size) success else fail
      case (Literal(name), _) if (basic.get(name) == Some(tpe)) => success
      case (Operation(Tuple, templates), trees.TupleType(tpes)) => extractSeq(tpes, templates)
      case (Operation(Sigma, templatesFroms :+ templateTo), trees.SigmaType(params, to)) =>
        for {
          matchingsParams <- extractSeq(params, templatesFroms)
          matchingsTo <- extract(to, templateTo)
        } yield matchingsParams ++ matchingsTo
      case (Operation(Arrow, Seq(Operation(Group, templatesFroms), templateTo)), trees.FunctionType(froms, to)) =>
        for {
          matchingsFroms <- extractSeq(froms, templatesFroms)
          matchingsTo <- extract(to, templateTo)
        } yield matchingsFroms ++ matchingsTo
      case (Operation(Pi, Seq(Operation(Group, templatesFroms), templateTo)), trees.PiType(params, to)) =>
        for {
          matchingsFroms <- extractSeq(params, templatesFroms)
          matchingsTo <- extract(to, templateTo)
        } yield matchingsFroms ++ matchingsTo
      case (Application(Literal(Name("Set")), templatesElems), trees.SetType(elem)) => extractSeq(Seq(elem), templatesElems)
      case (Application(Literal(Name("Bag")), templatesElems), trees.BagType(elem)) => extractSeq(Seq(elem), templatesElems)
      case (Application(Literal(Name("Map")), templatesElems), trees.MapType(key, value)) => extractSeq(Seq(key, value), templatesElems)
      case (Application(NameHole(index), templates), trees.ADTType(id, tpes)) =>
        for (matchings <- extractSeq(tpes, templates)) yield matchings ++ matching(index, id)
      case (Application(Literal(Name(name)), templates), trees.ADTType(id, tpes)) if (id.name == name) => extractSeq(tpes, templates)
      case (Refinement(templateId, templateType, templatePred), trees.RefinementType(vd, pred)) =>
        for {
          matchingsIdent <- templateId.map(ident => toIdObl(vd.id -> ident)).getOrElse(success)
          matchingsType <- extract(vd.tpe, templateType)
          matchingsPred <- extract(pred, templatePred)
        } yield matchingsIdent ++ matchingsType ++ matchingsPred
      case (_, _) => fail
    }
  }
}
