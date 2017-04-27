package inox
package parsing

trait ExpressionDeconstructors { self: Interpolator =>

  trait ExpressionDeconstructor { inner: ExprIR.type =>

    object TupleField {
      def unapply(field: Field): Option[Int] = field match {
        case FieldName(name) if name.startsWith("_") => scala.util.Try(name.tail.toInt).toOption.filter(_ >= 1)
        case _ => None 
      }
    }

    object Field {

      lazy val allFields = symbols.adts.toSeq.flatMap({
        case (_, c: trees.ADTConstructor) => c.fields.map((vd: trees.ValDef) => (c, vd))
        case _ => Seq()
      })

      lazy val fieldsById = allFields.groupBy(_._2.id)
      lazy val fieldsByName = allFields.groupBy(_._2.id.name)

      def unapplySeq(field: Field): Option[Seq[(trees.ADTConstructor, trees.ValDef)]] = field match {
        case FieldName(name) => fieldsByName.get(name)
        case FieldIdentifier(id) => fieldsById.get(id)
        case _ => None
      }
    }

    object FunDef {

      lazy val functionsByName = symbols.functions.toSeq.map(_._2).groupBy(_.id.name)

      def unapplySeq(expression: Expression): Option[Seq[trees.FunDef]] = expression match {
        case Literal(EmbeddedIdentifier(identifier)) => symbols.functions.get(identifier).map(Seq(_))
        case Literal(Name(string)) => functionsByName.get(string)
        case _ => None
      }
    }

    object TypedFunDef {
      def unapply(expression: Expression): Option[(trees.FunDef, Option[Seq[Type]])] = expression match {
        case TypeApplication(FunDef(fd), targs) => Some((fd, Some(targs)))
        case FunDef(fd) => Some((fd, None))
        case _ => None
      }
    }

    object ConsDef {

      lazy val allConstructors = symbols.adts.toSeq.flatMap({
        case (_, c: trees.ADTConstructor) => Some(c)
        case _ => None
      })

      lazy val consById = allConstructors.groupBy(_.id)
      lazy val consByName = allConstructors.groupBy(_.id.name)

      def unapplySeq(expression: Expression): Option[Seq[trees.ADTConstructor]] = expression match {
        case Literal(EmbeddedIdentifier(identifier)) => consById.get(identifier)
        case Literal(Name(string)) => consByName.get(string)
        case _ => None
      }
    }

    object TypedConsDef {
      def unapply(expression: Expression): Option[(trees.ADTConstructor, Option[Seq[Type]])] = expression match {
        case TypeApplication(ConsDef(cons), targs) => Some((cons, Some(targs)))
        case ConsDef(cons) => Some((cons, None))
        case _ => None
      }
    }

    object NumericBinOp {
      def unapply(string: String): Option[(trees.Expr, trees.Expr) => trees.Expr] = string match {
        case "+" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.Plus(lhs, rhs) })
        case "-" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.Minus(lhs, rhs) })
        case "*" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.Times(lhs, rhs) })
        case "/" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.Division(lhs, rhs) })
        case _ => None
      }
    }

    object IntegralBinOp {
      def unapply(string: String): Option[(trees.Expr, trees.Expr) => trees.Expr] = string match {
        case "%" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.Remainder(lhs, rhs) })
        case "mod" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.Modulo(lhs, rhs) })
        case _ => None
      }
    }

    object ComparableBinOp {
      def unapply(string: String): Option[(trees.Expr, trees.Expr) => trees.Expr] = string match {
        case "<=" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.LessEquals(lhs, rhs) })
        case "<" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.LessThan(lhs, rhs) })
        case ">=" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.GreaterEquals(lhs, rhs) })
        case ">" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.GreaterThan(lhs, rhs) })
        case _ => None
      }
    }

    object BooleanBinOp {
      def unapply(string: String): Option[(trees.Expr, trees.Expr) => trees.Expr] = string match {
        case "==>" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.Implies(lhs, rhs) })
        case _ => None
      }
    }

    object BooleanAndOperation {
      def unapply(expr: Expression): Option[Seq[Expression]] = expr match {
        case Operation("&&", expressions) => Some(expressions)
        case PrimitiveFunction(bi.BooleanAnd, _, expressions, None) => Some(expressions)
        case _ => None
      }
    }

    object BooleanOrOperation {
      def unapply(expr: Expression): Option[Seq[Expression]] = expr match {
        case Operation("||", expressions) => Some(expressions)
        case PrimitiveFunction(bi.BooleanOr, _, expressions, None) => Some(expressions)
        case _ => None
      }
    }

    object BooleanNAryOperation {
      def unapply(expr: Expression): Option[(Seq[trees.Expr] => trees.Expr, Seq[Expression])] = expr match {
        case BooleanAndOperation(expressions) => Some(({ (exprs: Seq[trees.Expr]) => trees.And(exprs) }, expressions))
        case BooleanOrOperation(expressions) => Some(({ (exprs: Seq[trees.Expr]) => trees.Or(exprs) }, expressions))
        case _ => None
      }
    }

    object BitVectorBinOp {
      def unapply(string: String): Option[(trees.Expr, trees.Expr) => trees.Expr] = string match {
        case "|" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.BVOr(lhs, rhs) })
        case "&" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.BVAnd(lhs, rhs) })
        case "^" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.BVXor(lhs, rhs) })
        case "<<" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.BVShiftLeft(lhs, rhs) })
        case ">>" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.BVAShiftRight(lhs, rhs) })
        case ">>>" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.BVLShiftRight(lhs, rhs) })
        case _ => None
      }
    }

    object PrimitiveFunction {
      def unapply(expr: Expression): Option[(bi.BuiltIn, String, Seq[Expression], Option[Seq[Type]])] = expr match {
        case Application(TypeApplication(Literal(Name(name@bi.BuiltIn(builtIn))), tpes), args) =>
          Some((builtIn, name, args, Some(tpes)))
        case Application(Literal(Name(name@bi.BuiltIn(builtIn))), args) =>
          Some((builtIn, name, args, None))
        case _ => None
      }
    }

    object SetConstruction {
      def unapply(expr: Expression): Option[(Seq[Expression], Option[Type])] = expr match {
        case PrimitiveFunction(bi.SetConstructor, f, es, otpes) if (otpes.isEmpty || otpes.get.length == 1) =>
          Some((es, otpes.map(_.head)))
        case Operation("Set", es@Bindings(_, Seq())) => 
          Some((es, None))
        case _ => None
      }
    }

    object SetUnionOperation {
      def unapply(expr: Expression): Option[(Expression, Expression, Option[Type])] = expr match {
        case PrimitiveFunction(bi.SetUnion, _, Seq(set1, set2), otpes) if (otpes.isEmpty || otpes.get.length == 1) =>
          Some((set1, set2, otpes.map(_.head)))
        case Operation("∪", Seq(set1, set2)) =>
          Some((set1, set2, None))
        case _ => None
      }
    }

    object SetIntersectionOperation {
      def unapply(expr: Expression): Option[(Expression, Expression, Option[Type])] = expr match {
        case PrimitiveFunction(bi.SetIntersection, _, Seq(set1, set2), otpes) if (otpes.isEmpty || otpes.get.length == 1) =>
          Some((set1, set2, otpes.map(_.head)))
        case Operation("∩", Seq(set1, set2)) =>
          Some((set1, set2, None))
        case _ => None
      }
    }

    object SetDifferenceOperation {
      def unapply(expr: Expression): Option[(Expression, Expression, Option[Type])] = expr match {
        case PrimitiveFunction(bi.SetDifference, _, Seq(set1, set2), otpes) if (otpes.isEmpty || otpes.get.length == 1) =>
          Some((set1, set2, otpes.map(_.head)))
        case Operation("∖", Seq(set1, set2)) =>
          Some((set1, set2, None))
        case _ => None
      }
    }

    object SetBinaryOperation {
      def unapply(expr: Expression): Option[(Expression, Expression, (trees.Expr, trees.Expr) => trees.Expr, Option[Type])] = expr match {
        case SetUnionOperation(set1, set2, otpe) => Some((set1, set2, { (lhs: trees.Expr, rhs: trees.Expr) => trees.SetUnion(lhs, rhs) }, otpe))
        case SetIntersectionOperation(set1, set2, otpe) => Some((set1, set2, { (lhs: trees.Expr, rhs: trees.Expr) => trees.SetIntersection(lhs, rhs) }, otpe))
        case SetUnionOperation(set1, set2, otpe) => Some((set1, set2, { (lhs: trees.Expr, rhs: trees.Expr) => trees.SetDifference(lhs, rhs) }, otpe))
        case _ => None
      }
    }

    object SubsetOperation {
      def unapply(expr: Expression): Option[(Expression, Expression, Option[Type])] = expr match {
        case PrimitiveFunction(bi.SetSubset, _, Seq(set1, set2), otpes) if (otpes.isEmpty || otpes.get.length == 1) =>
          Some((set1, set2, otpes.map(_.head)))
        case Operation("⊆", Seq(set1, set2)) =>
          Some((set1, set2, None))
        case _ => None
      }
    }

    object ContainsOperation {
      def unapply(expr: Expression): Option[(Expression, Expression, Option[Type])] = expr match {
        case PrimitiveFunction(bi.SetContains, _, Seq(set, elem), otpes) if (otpes.isEmpty || otpes.get.length == 1) =>
          Some((set, elem, otpes.map(_.head)))
        case Operation("∈", Seq(elem, set)) =>
          Some((set, elem, None))
        case _ => None
      }
    }

    object SetAddOperation {
      def unapply(expr: Expression): Option[(Expression, Expression, Option[Type])] = expr match {
        case PrimitiveFunction(bi.SetAdd, _, Seq(set, elem), otpes) if (otpes.isEmpty || otpes.get.length == 1) => Some((set, elem, otpes.map(_.head)))
        case _ => None
      }
    }

    object StringLengthOperation {
      def unapply(expr: Expression): Option[Expression] = expr match {
        case PrimitiveFunction(bi.StringLength, _, Seq(str), None) => {
          Some((str))
        }
        case _ => None
      }
    }

    object ConcatenateOperation {
      def unapply(expr: Expression): Option[(Expression, Expression)] = expr match {
        case PrimitiveFunction(bi.StringConcatenate, _, Seq(str1, str2), None) => {
          Some((str1, str2))
        }
        case Operation("++", Seq(str1, str2)) =>
          Some((str1, str2))
        case _ => None
      }
    }

    object SubstringOperation {
      def unapply(expr: Expression): Option[(Expression, Expression, Expression)] = expr match {
        case PrimitiveFunction(bi.StringSubstring, _, Seq(str, start, end), None) => {
          Some((str, start, end))
        }
        case _ => None
      }
    }

    object Binding {
      def unapply(expr: Expression): Option[(Expression, Expression)] = expr match {
        case Operation("->", Seq(a, b)) => Some((a, b))
        case _ => None
      }
    }

    object Bindings {
      def unapply(exprs: Seq[Expression]): Option[(Seq[Expression], Seq[(Expression, Expression)])] = {
        Some(Utils.classify(exprs) {
          case Binding(x, y) => Right((x, y))
          case x => Left(x)
        })
      }
    }

    object BagConstruction {
      def unapply(expr: Expression): Option[(Seq[Expression], Option[Type])] = expr match {
        case PrimitiveFunction(bi.BagConstructor, _, args, otpes) if (otpes.isEmpty || otpes.get.length == 1) => 
          Some((args, otpes.map(_.head)))
        case Operation("Set", es@Bindings(Seq(), _)) => 
          Some((es, None))
        case _ => None
      }
    }

    object BagMultiplicityOperation {
      def unapply(expr: Expression): Option[(Expression, Expression, Option[Type])] = expr match {
        case PrimitiveFunction(bi.BagMultiplicity, _, Seq(bag, elem), otpes) if (otpes.isEmpty || otpes.get.length == 1) => 
          Some((bag, elem, otpes.map(_.head)))
        case _ => None
      }
    }

    object BagAddOperation {
      def unapply(expr: Expression): Option[(Expression, Expression, Option[Type])] = expr match {
        case PrimitiveFunction(bi.BagAdd, _, Seq(bag, elem), otpes) if (otpes.isEmpty || otpes.get.length == 1) => 
          Some((bag, elem, otpes.map(_.head)))
        case _ => None
      }
    }

    object BagUnionOperation {
      def unapply(expr: Expression): Option[(Expression, Expression, Option[Type])] = expr match {
        case PrimitiveFunction(bi.BagUnion, _, Seq(bag1, bag2), otpes) if (otpes.isEmpty || otpes.get.length == 1) =>
          Some((bag1, bag2, otpes.map(_.head)))
        case _ => None
      }
    }

    object BagIntersectionOperation {
      def unapply(expr: Expression): Option[(Expression, Expression, Option[Type])] = expr match {
        case PrimitiveFunction(bi.BagIntersection, _, Seq(bag1, bag2), otpes) if (otpes.isEmpty || otpes.get.length == 1) =>
          Some((bag1, bag2, otpes.map(_.head)))
        case _ => None
      }
    }

    object BagDifferenceOperation {
      def unapply(expr: Expression): Option[(Expression, Expression, Option[Type])] = expr match {
        case PrimitiveFunction(bi.BagDifference, _, Seq(bag1, bag2), otpes) if (otpes.isEmpty || otpes.get.length == 1) =>
          Some((bag1, bag2, otpes.map(_.head)))
        case _ => None
      }
    }

    object BagBinaryOperation {

      def unapply(expr: Expression): Option[(Expression, Expression, (trees.Expr, trees.Expr) => trees.Expr, Option[Type])] = expr match {
        case BagUnionOperation(bag1, bag2, otpe) =>
          Some((bag1, bag2, { (b1: trees.Expr, b2: trees.Expr) => trees.BagUnion(b1, b2) }, otpe))
        case BagIntersectionOperation(bag1, bag2, otpe) =>
          Some((bag1, bag2, { (b1: trees.Expr, b2: trees.Expr) => trees.BagIntersection(b1, b2) }, otpe))
        case BagDifferenceOperation(bag1, bag2, otpe) =>
          Some((bag1, bag2, { (b1: trees.Expr, b2: trees.Expr) => trees.BagDifference(b1, b2) }, otpe))
        case _ => None
      }
    }

    object MapConstruction {
      def unapply(expr: Expression): Option[(Expression, Seq[Expression], Option[Either[Type, (Type, Type)]])] = expr match {
        case PrimitiveFunction(bi.MapConstructor, _, Seq(e, es @ _*), otpes) if (otpes.isEmpty || otpes.get.length == 2) =>
          Some((e, es, otpes.map({ case Seq(t1, t2) => Right((t1, t2))})))
        case TypeApplication(Operation("Map", Seq(e, es @ _*)), Seq(t)) => 
          Some((e, es, Some(Left(t))))
        case Operation("Map", Seq(e, es @ _*)) => 
          Some((e, es, None))
        case _ => None
      }
    }

    object MapApplyOperation {
      def unapply(expr: Expression): Option[(Expression, Expression, Option[(Type, Type)])] = expr match {
        case PrimitiveFunction(bi.MapApply, _, Seq(map, key), otpes) if (otpes.isEmpty || otpes.get.length == 2) =>
          Some((map, key, otpes.map({ case Seq(t1, t2) => (t1, t2)})))
        case _ => None
      }
    }

    object MapUpdatedOperation {
      def unapply(expr: Expression): Option[(Expression, Expression, Expression, Option[(Type, Type)])] = expr match {
        case PrimitiveFunction(bi.MapUpdated, _, Seq(map, key, value), otpes) if (otpes.isEmpty || otpes.get.length == 2) =>
          Some((map, key, value, otpes.map({ case Seq(t1, t2) => (t1, t2)})))
        case _ => None
      }
    }

    object AsInstanceOfOperation {
      def unapply(expr: Expression): Option[(Expression, Type)] = expr match {
        case PrimitiveFunction(bi.AsInstanceOf, _, Seq(expr), Some(Seq(tpe))) => Some((expr, tpe))
        case _ => None
      }
    }

    object IsInstanceOfOperation {
      def unapply(expr: Expression): Option[(Expression, Type)] = expr match {
        case PrimitiveFunction(bi.IsInstanceOf, _, Seq(expr), Some(Seq(tpe))) => Some((expr, tpe))
        case _ => None
      }
    }

    object TypeAnnotationOperation {
      def unapply(expr: Expression): Option[(Expression, Type)] = expr match {
        case TypeApplication(Operation("TypeAnnotation", Seq(expr)), Seq(tpe))  => Some((expr, tpe))
        case _ => None
      }
    }
  }
}