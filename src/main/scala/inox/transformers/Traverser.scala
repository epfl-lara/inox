/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package transformers

trait Traverser {
  val trees: ast.Trees
  import trees._

  type Env
  def initEnv: Env

  def traverse(id: Identifier, env: Env): Unit = {
    ()
  }

  def traverse(vd: ValDef, env: Env): Unit = {
    traverse(vd.tpe, env)
    vd.flags.foreach(traverse(_, env))
  }

  def traverse(tpd: TypeParameterDef, env: Env): Unit = {
    traverse(tpd.tp, env)
  }

  def traverse(e: Expr, env: Env): Unit = {
    val (ids, vs, es, tps, flags, _) = deconstructor.deconstruct(e)
    ids.foreach(traverse(_, env))
    vs.foreach(v => traverse(v.toVal, env))
    es.foreach(traverse(_, env))
    tps.foreach(traverse(_, env))
    flags.foreach(traverse(_, env))
  }

  def traverse(tpe: Type, env: Env): Unit = {
    val (ids, vs, es, tps, flags, _) = deconstructor.deconstruct(tpe)
    ids.foreach(traverse(_, env))
    vs.foreach(v => traverse(v.toVal, env))
    es.foreach(traverse(_, env))
    tps.foreach(traverse(_, env))
    flags.foreach(traverse(_, env))
  }

  def traverse(flag: Flag, env: Env): Unit = {
    val (ids, es, tps, _) = deconstructor.deconstruct(flag)
    ids.foreach(traverse(_, env))
    es.foreach(traverse(_, env))
    tps.foreach(traverse(_, env))
  }

  def traverse(fd: FunDef): Unit = {
    val env = initEnv

    traverse(fd.id, env)
    fd.tparams.foreach(traverse(_, env))
    fd.params.foreach(traverse(_, env))
    traverse(fd.returnType, env)
    traverse(fd.fullBody, env)
    fd.flags.foreach(traverse(_, env))
  }

  def traverse(sort: ADTSort): Unit = {
    val env = initEnv

    traverse(sort.id, env)
    sort.tparams.foreach(traverse(_, env))
    sort.constructors.foreach { cons =>
      traverse(cons.id, env)
      traverse(cons.sort, env)
      cons.fields.foreach(traverse(_, env))
    }
    sort.flags.foreach(traverse(_, env))
  }
}

trait TreeTraverser extends Traverser {
  override final type Env = Unit
  override final val initEnv: Unit = ()

  import trees._

  def traverse(id: Identifier): Unit = super.traverse(id, ())
  override final def traverse(id: Identifier, env: Env): Unit = traverse(id)

  def traverse(vd: ValDef): Unit = super.traverse(vd, ())
  override final def traverse(vd: ValDef, env: Env): Unit = traverse(vd)

  def traverse(e: Expr): Unit = super.traverse(e, ())
  override final def traverse(e: Expr, env: Env): Unit = traverse(e)

  def traverse(tpe: Type): Unit = super.traverse(tpe, ())
  override final def traverse(tpe: Type, env: Env): Unit = traverse(tpe)

  def traverse(flag: Flag): Unit = super.traverse(flag, ())
  override final def traverse(flag: Flag, env: Env): Unit = traverse(flag)
}

