/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

import inox.parsing.Interpolator
import inox.utils._

import scala.collection.concurrent.{Map => ConcurrentMap}
import scala.collection.JavaConverters._
import scala.util.Try

/** Provides types that describe Inox definitions. */
trait Definitions { self: Trees =>

  /** The base trait for Inox definitions */
  trait Definition extends Tree {
    def id: Identifier
    def flags: Seq[Flag]

    override def equals(that: Any): Boolean = that match {
      case d: Definition => id == d.id
      case _=> false
    }

    override def hashCode = id.hashCode
  }

  abstract class LookupException(id: Identifier, what: String)
    extends Exception("Lookup failed for " + what + " with symbol `" + id.uniqueName + "`")
  case class FunctionLookupException(id: Identifier) extends LookupException(id, "function")
  case class ADTLookupException(id: Identifier) extends LookupException(id, "adt")

  case class NotWellFormedException(d: Definition, info: Option[String] = None)
    extends Exception(s"Not well formed definition $d" + (info map { i => s" \n\tbecause $i" } getOrElse ""))

  /** Common super-type for [[ValDef]] and [[Expressions.Variable Variable]].
    *
    * Both types share much in common and being able to reason about them
    * in a uniform manner can be useful in certain cases.
    */
  protected[ast] trait VariableSymbol extends Tree with Typed {
    def id: Identifier
    def tpe: Type
    def flags: Seq[Flag]

    def getType(implicit s: Symbols): Type = tpe.getType

    def to[A <: VariableSymbol](implicit ev: VariableConverter[A]): A = ev.convert(this)

    override def equals(that: Any): Boolean = that match {
      case vs: VariableSymbol => id == vs.id && tpe == vs.tpe && flags == vs.flags
      case _ => false
    }

    override def hashCode: Int = 61 * id.hashCode + 31 * tpe.hashCode + flags.hashCode
  }

  implicit def variableSymbolOrdering[VS <: VariableSymbol]: Ordering[VS] =
    Ordering.by(e => e.id)

  abstract class VariableConverter[B <: VariableSymbol] {
    def convert(a: VariableSymbol): B
  }

  implicit def convertToVal = new VariableConverter[ValDef] {
    def convert(vs: VariableSymbol): ValDef = vs match {
      case v: ValDef => v
      case _ => ValDef(vs.id, vs.tpe, vs.flags).copiedFrom(vs)
    }
  }

  implicit def convertToVariable = new VariableConverter[Variable] {
    def convert(vs: VariableSymbol): Variable = vs match {
      case v: Variable => v
      case _ => Variable(vs.id, vs.tpe, vs.flags).copiedFrom(vs)
    }
  }

  /**
    * A ValDef declares a formal parameter (with symbol [[id]]) to be of a certain type.
    */
  sealed class ValDef(v: Variable) extends Definition with VariableSymbol {
    @inline def id = v.id
    @inline def tpe = v.tpe
    @inline def flags = v.flags

    override def setPos(pos: Position): ValDef.this.type = {
      v.setPos(pos)
      super.setPos(pos)
    }

    /** Transform this [[ValDef]] into a [[Expressions.Variable Variable]] */
    @inline def toVariable: Variable = v
    @inline def freshen: ValDef = new ValDef(v.freshen).copiedFrom(this)

    override def equals(that: Any): Boolean = super[VariableSymbol].equals(that)
    override def hashCode: Int = super[VariableSymbol].hashCode

    override def toString: String = s"ValDef($id, $tpe, $flags)"

    def copy(id: Identifier = id, tpe: Type = tpe, flags: Seq[Flag] = flags): ValDef =
      new ValDef(v.copy(id = id, tpe = tpe, flags = flags)).copiedFrom(this)
  }

  object ValDef {
    def fresh(name: String, tpe: Type, alwaysShowUniqueID: Boolean = false) =
      ValDef(FreshIdentifier(name, alwaysShowUniqueID), tpe)
    def apply(id: Identifier, tpe: Type, flags: Seq[Flag] = Seq.empty) = new ValDef(Variable(id, tpe, flags))
    def unapply(vd: ValDef): Option[(Identifier, Type, Seq[Flag])] = Some((vd.id, vd.tpe, vd.flags))
  }

  type Symbols >: Null <: AbstractSymbols

  val NoSymbols: Symbols

  /** Provides the class and function definitions of a program and lookups on them */
  trait AbstractSymbols
     extends Printable
        with TypeOps
        with SymbolOps
        with CallGraph
        with DependencyGraph
        with Paths { self0: Symbols =>

    val sorts: Map[Identifier, ADTSort]
    val functions: Map[Identifier, FunDef]

    @inline def constructors: Map[Identifier, ADTConstructor] = _constructors.get
    private[this] val _constructors: Lazy[Map[Identifier, ADTConstructor]] =
      Lazy(sorts.values.flatMap(_.constructors.map(cons => cons.id -> cons)).toMap)

    protected val trees: self.type = self
    protected val symbols: this.type = this

    type Semantics = inox.Semantics {
      val trees: self0.trees.type
      val symbols: self0.symbols.type
    }

    // @nv: this is a hack to reinject `this` into the set of implicits
    // in scope when using the pattern:
    // {{{
    //    implicit val symbols: Symbols
    //    import symbols._
    // }}}
    // which seems to remove `symbols` from the set of current implicits
    // for some mysterious reason.
    implicit def implicitSymbols: this.type = this

    private[this] val typedSortCache: ConcurrentMap[(Identifier, Seq[Type]), Option[TypedADTSort]] =
      new java.util.concurrent.ConcurrentHashMap[(Identifier, Seq[Type]), Option[TypedADTSort]].asScala
    def lookupSort(id: Identifier): Option[ADTSort] = sorts.get(id)
    def lookupSort(id: Identifier, tps: Seq[Type]): Option[TypedADTSort] =
      typedSortCache.getOrElseUpdate(id -> tps, lookupSort(id).map(TypedADTSort(_, tps)))

    def getSort(id: Identifier): ADTSort =
      lookupSort(id).getOrElse(throw ADTLookupException(id))
    def getSort(id: Identifier, tps: Seq[Type]): TypedADTSort =
      lookupSort(id, tps).getOrElse(throw ADTLookupException(id))

    private[this] val typedConstructorCache: ConcurrentMap[(Identifier, Seq[Type]), Option[TypedADTConstructor]] =
      new java.util.concurrent.ConcurrentHashMap[(Identifier, Seq[Type]), Option[TypedADTConstructor]].asScala
    def lookupConstructor(id: Identifier): Option[ADTConstructor] = constructors.get(id)
    def lookupConstructor(id: Identifier, tps: Seq[Type]): Option[TypedADTConstructor] =
      typedConstructorCache.getOrElseUpdate(id -> tps, constructors.get(id).flatMap { cons =>
        lookupSort(cons.sort, tps).flatMap(_.constructors.collectFirst {
          case tcons if tcons.id == id => tcons
        })
      })

    def getConstructor(id: Identifier): ADTConstructor =
      lookupConstructor(id).getOrElse(throw ADTLookupException(id))
    def getConstructor(id: Identifier, tps: Seq[Type]): TypedADTConstructor =
      lookupConstructor(id, tps).getOrElse(throw ADTLookupException(id))

    private[this] val typedFunctionCache: ConcurrentMap[(Identifier, Seq[Type]), Option[TypedFunDef]] =
      new java.util.concurrent.ConcurrentHashMap[(Identifier, Seq[Type]), Option[TypedFunDef]].asScala
    def lookupFunction(id: Identifier): Option[FunDef] = functions.get(id)
    def lookupFunction(id: Identifier, tps: Seq[Type]): Option[TypedFunDef] =
      typedFunctionCache.getOrElseUpdate(id -> tps, lookupFunction(id).map(TypedFunDef(_, tps)))

    def getFunction(id: Identifier): FunDef =
      lookupFunction(id).getOrElse(throw FunctionLookupException(id))
    def getFunction(id: Identifier, tps: Seq[Type]): TypedFunDef =
      lookupFunction(id, tps).getOrElse(throw FunctionLookupException(id))

    override def toString: String = asString(PrinterOptions.fromSymbols(this, Context.printNames))
    override def asString(implicit opts: PrinterOptions): String = {
      sorts.map(p => prettyPrint(p._2, opts)).mkString("\n\n") +
      "\n\n-----------\n\n" +
      functions.map(p => prettyPrint(p._2, opts)).mkString("\n\n")
    }

    def transform(t: TreeTransformer { val s: self.type }): t.t.Symbols = SymbolTransformer(t).transform(this)

    /** Makes sure these symbols pass a certain number of well-formedness checks, such as
      * - function definition bodies satisfy the declared return types
      * - adt sorts and constructors point to each other correctly
      * - each adt type has at least one instance
      * - adt type parameter flags match between children and parents
      * - every variable is available in the scope of its usage
      */
    @inline def ensureWellFormed: Unit = _tryWF.get.get
    private[this] val _tryWF: Lazy[Try[Unit]] = Lazy(Try({
      for ((_, fd) <- functions) ensureWellFormedFunction(fd)
      for ((_, sort) <- sorts) ensureWellFormedAdt(sort)
      ()
    }))

    protected def ensureWellFormedFunction(fd: FunDef) = {
      typeCheck(fd.fullBody, fd.getType)

      val unbound: Seq[Variable] = collectWithPC(fd.fullBody, Path.empty withBounds fd.params) {
        case (v: Variable, path) if !(path isBound v.id) => v
      }

      if (unbound.nonEmpty) {
        throw NotWellFormedException(fd, Some("Unknown variables: " + (unbound map { _.id.uniqueName } mkString ", ")))
      }
    }

    protected def ensureWellFormedAdt(sort: ADTSort) = {
      if (!sort.isWellFormed) throw NotWellFormedException(sort)
      if (!(sort.constructors forall (cons => cons.sort == sort.id))) throw NotWellFormedException(sort)
      if (sort.constructors.flatMap(_.fields).groupBy(_.id).exists(_._2.size > 1)) throw NotWellFormedException(sort)
    }

    override def equals(that: Any): Boolean = that match {
      case sym: AbstractSymbols => functions == sym.functions && sorts == sym.sorts
      case _ => false
    }

    override def hashCode: Int = functions.hashCode * 61 + sorts.hashCode

    def withFunctions(functions: Seq[FunDef]): Symbols
    def withSorts(sorts: Seq[ADTSort]): Symbols
  }

  sealed class TypeParameterDef(val tp: TypeParameter) extends Definition {
    @inline def id = tp.id
    @inline def flags = tp.flags

    @inline def freshen = new TypeParameterDef(tp.freshen)

    override def equals(that: Any): Boolean = that match {
      case tpd: TypeParameterDef => tp == tpd.tp
      case _ => false
    }

    override def hashCode: Int = tp.hashCode

    override def toString: String = s"TypeParameterDef($tp)"
  }

  object TypeParameterDef {
    def fresh(name: String, flags: Seq[Flag] = Seq.empty) = TypeParameterDef(FreshIdentifier(name), flags)
    def apply(tp: TypeParameter) = new TypeParameterDef(tp)
    def apply(id: Identifier, flags: Seq[Flag] = Seq.empty) = new TypeParameterDef(TypeParameter(id, flags))
    def unapply(tpd: TypeParameterDef): Option[(Identifier, Seq[Flag])] = Some((tpd.id, tpd.flags))
  }


  /** Represents source code annotations and some other meaningful flags.
    *
    * In order to enable transformations on [[Flag]] instances, there is an
    * implicit contract on `args` such that for each argument, either
    * {{{arg: Expr | Type}}}, or there exists no [[Expressions.Expr Expr]]
    * or [[Types.Type Type]] instance within arg. */
  abstract class Flag(val name: String, args: Seq[Any]) extends Printable {
    def asString(implicit opts: PrinterOptions): String = name + (if (args.isEmpty) "" else {
      args.map(arg => self.asString(arg)(opts)).mkString("(", ", ", ")")
    })
  }

  /** Denotes that this adt is refined by invariant ''id'' */
  sealed case class HasADTInvariant(id: Identifier) extends Flag("invariant", Seq(id))

  /** Denotes that this adt has an overriden equality relation given by ''id'' */
  sealed case class HasADTEquality(id: Identifier) extends Flag("equality", Seq(id))

  /** Compiler annotations given in the source code as @annot.
    *
    * @see [[Flag]] for some notes on the actual type of [[args]]. */
  sealed case class Annotation(override val name: String, val args: Seq[Any]) extends Flag(name, args)

  /** Algebraic datatype sort definition.
    * An ADT sort is linked to a series of constructors ([[ADTConstructor]]) for this particular sort. */
  class ADTSort(val id: Identifier,
                val tparams: Seq[TypeParameterDef],
                val constructors: Seq[ADTConstructor],
                val flags: Seq[Flag]) extends Definition {
    def typeArgs = tparams.map(_.tp)

    def isInductive(implicit s: Symbols): Boolean = {
      val base = typed

      def rec(sort: TypedADTSort, seen: Set[TypedADTSort], first: Boolean = false): Boolean = {
        if (!first && sort == base) true
        else if (seen(sort)) false
        else sort.constructors.exists(_.fields.exists(vd => typeOps.exists {
          case t: ADTType => rec(t.getSort, seen + sort)
          case _ => false
        } (vd.getType)))
      }

      rec(base, Set.empty, first = true)
    }

    def isWellFormed(implicit s: Symbols): Boolean = {
      def flatten(s: Seq[Type]): Seq[Type] = s match {
        case Nil => Nil
        case (head: TupleType) +: tail => flatten(head.bases ++ tail)
        case (head: MapType) +: tail => flatten(head.to +: tail) // Because Map has a default.
        case head +: tail => head +: flatten(tail)
      }

      def rec(sort: TypedADTSort, seen: Set[TypedADTSort]): Boolean = {
        if (seen(sort)) false
        else sort.constructors.exists(cons => flatten(cons.fields.map(_.getType)).forall {
          case t: ADTType => rec(t.getSort, seen + sort)
          case _ => true
        })
      }

      rec(typed, Set.empty)
    }

    /** An invariant that refines this [[ADTSort]] */
    def invariant(implicit s: Symbols): Option[FunDef] = 
      flags.collectFirst { case HasADTInvariant(id) => s.getFunction(id) }

    def hasInvariant(implicit s: Symbols): Boolean = invariant.isDefined

    /** An equality relation defined on this [[ADTSort]] */
    def equality(implicit s: Symbols): Option[FunDef] =
      flags.collectFirst { case HasADTEquality(id) => s.getFunction(id) }

    def hasEquality(implicit s: Symbols): Boolean = equality.isDefined

    /** Wraps this [[ADTSort]] in a in [[TypedADTSort]] with its own type parameters */
    def typed(implicit s: Symbols): TypedADTSort = typed(tparams.map(_.tp))

    /** Wraps this [[ADTSort]] in a in [[TypedADTSort]] with the specified type parameters */
    def typed(tps: Seq[Type])(implicit s: Symbols): TypedADTSort = s.getSort(id, tps)

    def copy(id: Identifier = id,
             tparams: Seq[TypeParameterDef] = tparams,
             constructors: Seq[ADTConstructor] = constructors,
             flags: Seq[Flag] = flags): ADTSort = new ADTSort(id, tparams, constructors, flags)
  }

  /** Case classes/ ADT constructors. For single-case classes these may coincide
    *
    * @param id      -- The identifier that refers to this ADT constructor.
    * @param fields  -- The fields of this constructor (types may depend on sorts type params).
    */
  class ADTConstructor(
    val id: Identifier,
    val sort: Identifier,
    val fields: Seq[ValDef],
    val flags: Seq[Flag] = Seq.empty
  ) extends Definition {

    def getSort(implicit s: Symbols): ADTSort = s.getSort(sort)

    /** Returns the index of the field with the specified id */
    def selectorID2Index(id: Identifier) : Int = {
      val index = fields.indexWhere(_.id == id)

      if (index < 0) {
        scala.sys.error(
          "Could not find '"+id+"' ("+id.uniqueName+") within "+
          fields.map(_.id.uniqueName).mkString(", ")
        )
      } else index
    }

    /** Wraps this [[ADTConstructor]] in a in [[TypedADTConstructor]] with its sort's type parameters */
    def typed(implicit s: Symbols): TypedADTConstructor = typed(getSort.typeArgs)

    /** Wraps this [[ADTConstructor]] in a in [[TypedADTConstructor]] with the specified type parameters */
    def typed(tps: Seq[Type])(implicit s: Symbols): TypedADTConstructor = s.getConstructor(id, tps)

    def copy(id: Identifier = id,
             sort: Identifier = sort,
             fields: Seq[ValDef] = fields): ADTConstructor = new ADTConstructor(id, sort, fields)
  }

  /** Represents an [[ADTSort]] whose type parameters have been instantiated to ''tps'' */
  case class TypedADTSort private(definition: ADTSort, tps: Seq[Type])(implicit val symbols: Symbols) extends Tree {
    require(tps.length == definition.tparams.length)
    copiedFrom(definition)

    @inline def id: Identifier = definition.id

    @inline def invariant: Option[TypedFunDef] = _invariant.get
    private[this] val _invariant = Lazy(definition.invariant.map(_.typed(tps)))

    @inline def hasInvariant: Boolean = invariant.isDefined

    @inline def equality: Option[TypedFunDef] = _equality.get
    private[this] val _equality = Lazy(definition.equality.map(_.typed(tps)))

    @inline def hasEquality: Boolean = equality.isDefined

    @inline def tpSubst: Map[TypeParameter, Type] = _tpSubst.get
    private[this] val _tpSubst = Lazy((definition.typeArgs zip tps).toMap.filter(tt => tt._1 != tt._2))

    /** A [[Types.Type Type]] instantiated with this [[TypedADTSort]]'s type instantiation */
    def instantiate(t: Type): Type = typeOps.instantiateType(t, tpSubst)

    /** A [[Expressions.Expr Expr]] instantiated with this [[TypedADTSort]]'s type instantiation */
    def instantiate(e: Expr): Expr = typeOps.instantiateType(e, tpSubst)

    /** A [[Definitions.Flag Flag]] instantiated with this [[TypedADTSort]]'s type instantiation */
    def instantiate(f: Flag): Flag = {
      val (ids, exprs, types, recons) = deconstructor.deconstruct(f)
      recons(ids, exprs.map(instantiate), types.map(instantiate))
    }

    /** The flags of the respective [[ADTSort]] instantiated with the real type parameters */
    @inline def flags: Seq[Flag] = _flags.get
    private[this] val _flags = Lazy(definition.flags.map(instantiate))

    val constructors: Seq[TypedADTConstructor] =
      definition.constructors map (TypedADTConstructor(_, this))
  }

  /** Represents an [[ADTConstructor]] whose type parameters have been instantiated to ''tps'' */
  case class TypedADTConstructor private(definition: ADTConstructor, sort: TypedADTSort) extends Tree {
    copiedFrom(definition)

    @inline def id: Identifier = definition.id
    @inline def tps: Seq[Type] = sort.tps

    @inline def fields: Seq[ValDef] = _fields.get
    private[this] val _fields = Lazy({
      if (sort.tpSubst.isEmpty) definition.fields
      else definition.fields.map(vd => vd.copy(
        tpe = sort.instantiate(vd.tpe),
        flags = vd.flags.map(sort.instantiate)
      ))
    })
  }


  /** Function definition
    *
    * @param id         -- The identifier which will refer to this function.
    * @param tparams    -- The type parameters this function takes.
    * @param params     -- The functions formal arguments (types may depend on [[tparams]]).
    * @param returnType -- The function's return type (may depend on [[tparams]]).
    * @param fullBody   -- The body of this function.
    * @param flags      -- Flags that annotate this function with attributes.
    */
  class FunDef(
    val id: Identifier,
    val tparams: Seq[TypeParameterDef],
    val params: Seq[ValDef],
    val returnType: Type,
    val fullBody: Expr,
    val flags: Seq[Flag]
  ) extends Definition {

    /** Wraps this [[FunDef]] in a in [[TypedFunDef]] with its own type parameters */
    def typed(implicit s: Symbols): TypedFunDef = typed(tparams.map(_.tp))

    /** Wraps this [[FunDef]] in a in [[TypedFunDef]] with the specified type parameters */
    def typed(tps: Seq[Type])(implicit s: Symbols): TypedFunDef = s.getFunction(id, tps)

    /* Auxiliary methods */

    def isRecursive(implicit s: Symbols) = s.isRecursive(id)

    @inline def typeArgs: Seq[TypeParameter] = _typeArgs.get
    private[this] val _typeArgs = Lazy(tparams.map(_.tp))

    /** Applies this function on its formal parameters */
    @inline def applied = FunctionInvocation(id, typeArgs, params map (_.toVariable))

    /** The (non-dependent) return type of this function definition */
    def getType(implicit s: Symbols) = returnType.getType

    def copy(
      id: Identifier = this.id,
      tparams: Seq[TypeParameterDef] = this.tparams,
      params: Seq[ValDef] = this.params,
      returnType: Type = this.returnType,
      fullBody: Expr = this.fullBody,
      flags: Seq[Flag] = this.flags
    ): FunDef = new FunDef(id, tparams, params, returnType, fullBody, flags).copiedFrom(this)
  }


  /** Represents a [[FunDef]] whose type parameters have been instantiated with the specified types */
  case class TypedFunDef private(fd: FunDef, tps: Seq[Type])(implicit val symbols: Symbols) extends Tree {
    require(tps.length == fd.tparams.length)
    copiedFrom(fd)

    val id = fd.id

    def signature = {
      if (tps.nonEmpty) {
        id.toString+tps.mkString("[", ", ", "]")
      } else {
        id.toString
      }
    }

    @inline def tpSubst: Map[TypeParameter, Type] = _tpSubst.get
    private[this] val _tpSubst = Lazy((fd.typeArgs zip tps).toMap.filter(tt => tt._1 != tt._2))

    /** A [[Types.Type Type]] instantiated with this [[TypedFunDef]]'s type instantiation */
    def instantiate(t: Type): Type = typeOps.instantiateType(t, tpSubst)

    /** A [[Expressions.Expr Expr]] instantiated with this [[TypedFunDef]]'s type instantiation */
    def instantiate(e: Expr): Expr = typeOps.instantiateType(e, tpSubst)

    /** A [[Definitions.Flag Flag]] instantiated with this [[TypedFunDef]]'s type instantiation */
    def instantiate(f: Flag): Flag = {
      val (ids, exprs, types, recons) = deconstructor.deconstruct(f)
      recons(ids, exprs.map(instantiate), types.map(instantiate))
    }

    /** A mapping from this [[TypedFunDef]]'s formal parameters to real arguments
      *
      * @param realArgs The arguments to which the formal arguments are mapped
      */
    def paramSubst(realArgs: Seq[Expr]) = {
      require(realArgs.size == params.size)
      (params zip realArgs).toMap
    }

    /** Substitute this [[TypedFunDef]]'s formal parameters with real arguments in some expression
     *
     * @param realArgs The arguments to which the formal argumentas are mapped
     * @param e The expression in which the substitution will take place
     */
    def withParamSubst(realArgs: Seq[Expr], e: Expr) = {
      exprOps.replaceFromSymbols(paramSubst(realArgs), e)
    }

    /** Apply this [[inox.ast.Definitions.TypedFunDef]] on specified arguments */
    def applied(realArgs: Seq[Expr]): FunctionInvocation = {
      FunctionInvocation(id, tps, realArgs)
    }

    /** Apply this [[inox.ast.Definitions.TypedFunDef]] on its formal parameters */
    @inline def applied: FunctionInvocation = applied(params map { _.toVariable })

    /** The paremeters of the respective [[FunDef]] instantiated with the real type parameters */
    @inline def params: Seq[ValDef] = _params.get
    private[this] val _params = Lazy({
      if (tpSubst.isEmpty) fd.params
      else fd.params.map(vd => vd.copy(
        tpe = instantiate(vd.tpe),
        flags = vd.flags.map(instantiate)
      ))
    })

    /** The function type corresponding to this [[TypedFunDef]]'s arguments and return type */
    @inline def functionType: FunctionType = FunctionType(params.map(_.tpe), returnType)

    /** The return type of the respective [[FunDef]] instantiated with the real type parameters */
    @inline def returnType: Type = _returnType.get
    private[this] val _returnType = Lazy(instantiate(fd.returnType))

    /** The (non-dependent) return type of this typed function definition */
    def getType = returnType.getType

    /** The body of the respective [[FunDef]] instantiated with the real type parameters */
    @inline def fullBody: Expr = _fullBody.get
    private[this] val _fullBody = Lazy(instantiate(fd.fullBody))

    /** The flags of the respective [[FunDef]] instantiated with the real type parameters */
    @inline def flags: Seq[Flag] = _flags.get
    private[this] val _flags = Lazy(fd.flags.map(instantiate))
  }
}
