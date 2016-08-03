
package inox
package ast

trait TreeOps { self: Trees =>

  trait TreeTransformer {
    def transform(id: Identifier, tpe: Type): (Identifier, Type) = (id, transform(tpe))

    def transform(v: Variable): Variable = {
      val (id, tpe) = transform(v.id, v.tpe)
      if ((id ne v.id) || (tpe ne v.tpe)) {
        Variable(id, tpe).copiedFrom(v)
      } else {
        v
      }
    }

    def transform(vd: ValDef): ValDef = {
      val (id, tpe) = transform(vd.id, vd.tpe)
      if ((id ne vd.id) || (tpe ne vd.tpe)) {
        ValDef(id, tpe).copiedFrom(vd)
      } else {
        vd
      }
    }

    @inline
    private def transformValDefs(vds: Seq[ValDef]): (Seq[ValDef], Boolean) = {
      var changed = false
      val newVds = vds.map { vd =>
        val newVd = transform(vd)
        if (vd ne newVd) changed = true
        newVd
      }

      (newVds, changed)
    }

    @inline
    private def transformExprs(args: Seq[Expr]): (Seq[Expr], Boolean) = {
      var changed = false
      val newArgs = args.map { arg =>
        val newArg = transform(arg)
        if (arg ne newArg) changed = true
        newArg
      }

      (newArgs, changed)
    }

    @inline
    private def transformTypes(tps: Seq[Type]): (Seq[Type], Boolean) = {
      var changed = false
      val newTps = tps.map { tp =>
        val newTp = transform(tp)
        if (tp ne newTp) changed = true
        newTp
      }

      (newTps, changed)
    }

    def transform(e: Expr): Expr = e match {
      case v: Variable => transform(v)

      case Lambda(args, body) =>
        val (newArgs, changedArgs) = transformValDefs(args)
        val newBody = transform(body)
        if (changedArgs || (body ne newBody)) {
          Lambda(newArgs, newBody).copiedFrom(e)
        } else {
          e
        }

      case Forall(args, body) =>
        val (newArgs, changedArgs) = transformValDefs(args)
        val newBody = transform(body)
        if (changedArgs || (body ne newBody)) {
          Forall(newArgs, newBody).copiedFrom(e)
        } else {
          e
        }

      case Let(vd, expr, body) =>
        val newVd = transform(vd)
        val newExpr = transform(expr)
        val newBody = transform(body)
        if ((vd ne newVd) || (expr ne newExpr) || (body ne newBody)) {
          Let(newVd, newExpr, newBody).copiedFrom(e)
        } else {
          e
        }

      case CaseClass(ct, args) =>
        val newCt = transform(ct)
        val (newArgs, changedArgs) = transformExprs(args)
        if ((ct ne newCt) || changedArgs) {
          CaseClass(newCt.asInstanceOf[ClassType], newArgs).copiedFrom(e)
        } else {
          e
        }

      case CaseClassSelector(cc, selector) =>
        val newCc = transform(cc)
        if (cc ne newCc) {
          CaseClassSelector(cc, selector).copiedFrom(e)
        } else {
          e
        }

      case FunctionInvocation(id, tps, args) =>
        val (newTps, changedTps) = transformTypes(tps)
        val (newArgs, changedArgs) = transformExprs(args)
        if (changedTps || changedArgs) {
          FunctionInvocation(id, newTps, newArgs).copiedFrom(e)
        } else {
          e
        }

      case IsInstanceOf(expr, ct) =>
        val newExpr = transform(expr)
        val newCt = transform(ct)
        if ((expr ne newExpr) || (ct ne newCt)) {
          IsInstanceOf(newExpr, newCt.asInstanceOf[ClassType]).copiedFrom(e)
        } else {
          e
        }

      case AsInstanceOf(expr, ct) => 
        val newExpr = transform(expr)
        val newCt = transform(ct)
        if ((expr ne newExpr) || (ct ne newCt)) {
          AsInstanceOf(newExpr, newCt.asInstanceOf[ClassType]).copiedFrom(e)
        } else {
          e
        }

      case FiniteSet(es, tpe) =>
        val (newArgs, changed) = transformExprs(es)
        val newTpe = transform(tpe)
        if (changed || (tpe ne newTpe)) {
          FiniteSet(newArgs, newTpe).copiedFrom(e)
        } else {
          e
        }

      case FiniteBag(es, tpe) =>
        var changed = false
        val newEs = es.map { case (k, v) =>
          val newK = transform(k)
          if (k ne newK) changed = true
          newK -> v
        }
        val newTpe = transform(tpe)
        if (changed || (tpe ne newTpe)) {
          FiniteBag(newEs, newTpe).copiedFrom(e)
        } else {
          e
        }

      case FiniteMap(pairs, from, to) =>
        var changed = false
        val newPairs = pairs.map { case (k, v) =>
          val newK = transform(k)
          val newV = transform(v)
          if ((k ne newK) || (v ne newV)) changed = true
          newK -> newV
        }
        val newFrom = transform(from)
        val newTo = transform(to)
        if (changed || (from ne newFrom) || (to ne newTo)) {
          FiniteMap(newPairs, newFrom, newTo).copiedFrom(e)
        } else {
          e
        }

      case Operator(es, builder) =>
        val newEs = es map transform
        if ((newEs zip es).exists { case (bef, aft) => aft ne bef }) {
          builder(newEs).copiedFrom(e)
        } else {
          e
        }

      case e => e
    }

    def transform(tpe: Type): Type = tpe match {
      case NAryType(ts, builder) =>
        val newTs = ts map transform
        if ((newTs zip ts).exists { case (bef, aft) => aft ne bef }) {
          builder(ts map transform).copiedFrom(tpe)
        } else {
          tpe
        }
    }
  }

  trait TreeTraverser {
    def traverse(e: Expr): Unit = e match {
      case Variable(_, tpe) =>
        traverse(tpe)

      case Lambda(args, body) =>
        args foreach (vd => traverse(vd.tpe))
        traverse(body)

      case Forall(args, body) =>
        args foreach (vd => traverse(vd.tpe))
        traverse(body)

      case Let(a, expr, body) =>
        traverse(expr)
        traverse(body)

      case CaseClass(cct, args) =>
        traverse(cct)
        args foreach traverse

      case CaseClassSelector(caseClass, selector) =>
        traverse(caseClass)

      case FunctionInvocation(id, tps, args) =>
        tps foreach traverse
        args foreach traverse

      case IsInstanceOf(expr, ct) =>
        traverse(expr)
        traverse(ct)

      case AsInstanceOf(expr, ct) => 
        traverse(expr)
        traverse(ct)

      case FiniteSet(es, tpe) =>
        es foreach traverse
        traverse(tpe)

      case FiniteBag(es, tpe) =>
        es foreach { case (k, _) => traverse(k) }
        traverse(tpe)

      case FiniteMap(pairs, from, to) =>
        pairs foreach { case (k, v) => traverse(k); traverse(v) }
        traverse(from)
        traverse(to)

      case Operator(es, builder) =>
        es foreach traverse

      case e =>
    }

    def traverse(tpe: Type): Unit = tpe match {
      case NAryType(ts, builder) =>
        ts foreach traverse
    }
  }
}
