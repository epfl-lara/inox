/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

import inox.parsing.Interpolator
import inox.transformers._
import inox.utils._

import scala.collection.concurrent.{Map => ConcurrentMap}
import scala.jdk.CollectionConverters._
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
    extends Exception(s"Not well formed definition $d" + (info map { i => s"\n\tbecause $i" } getOrElse ""))

  /** Common super-type for [[ValDef]] and [[Expressions.Variable Variable]].
    *
    * Both types share much in common and being able to reason about them
    * in a uniform manner can be useful in certain cases.
    */
  protected[ast] trait VariableSymbol extends Tree with Typed {
    def id: Identifier
    def tpe: Type
    def flags: Seq[Flag]

    def getTpe(stripRefinements: Boolean)(using Symbols): Type = tpe.getTpe(stripRefinements)

    def to[A <: VariableSymbol](using ev: VariableConverter[A]): A = ev.convert(this)

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

  implicit def convertToVal: VariableConverter[ValDef] = new VariableConverter[ValDef] {
    def convert(vs: VariableSymbol): ValDef = vs match {
      case v: ValDef => v
      case _ => ValDef(vs.id, vs.tpe, vs.flags).copiedFrom(vs)
    }
  }

  implicit def convertToVariable: VariableConverter[Variable] = new VariableConverter[Variable] {
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
    @inline def toVariable: Variable = v.copy().copiedFrom(v)
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
    def unapply(vd: ValDef): (Identifier, Type, Seq[Flag]) = (vd.id, vd.tpe, vd.flags)
  }

  type Symbols >: Null <: AbstractSymbols

  val NoSymbols: Symbols

  /** Provides the class and function definitions of a program and lookups on them */
  trait AbstractSymbols
    extends Printable
      with TypeOps
      with SymbolOps
      with CallGraph
      with DependencyGraph { self0: Symbols =>

    // The only value that can be assigned to `trees`, but that has to be
    // done in a concrete class explicitly overriding `trees`
    // Otherwise, we can run into initialization issue.
    protected val trees: self.type
    // More or less the same here
    protected val symbols: this.type

    given givenSymbols: symbols.type = symbols

    /** Identifies this symbol table in the type caches of the trees (see `CachingTyped`).
      *
      * A tree caches its type together with this object, and not with the symbol table that the type
      * was computed with. Otherwise, a tree shared by two programs would keep alive the symbol table
      * of the last program that typed it, such as the encoded program of a solver that was freed.
      */
    private[ast] final val typingKey: AnyRef = new AnyRef

    val sorts: Map[Identifier, ADTSort]
    val functions: Map[Identifier, FunDef]

    /** The modes that the typing of trees depends on under these symbols.
      *
      * Symbols that support other modes than the default ones keep them and override this,
      * along with [[withModes]]. */
    def modes: TypingModes = TypingModes()

    @inline def constructors: Map[Identifier, ADTConstructor] = _constructors.get
    private val _constructors: Lazy[Map[Identifier, ADTConstructor]] =
      Lazy(sorts.values.flatMap(_.constructors.map(cons => cons.id -> cons)).toMap)


    type Semantics = inox.Semantics {
      val trees: self0.trees.type
      val symbols: self0.symbols.type
    }

    private val typedSortCache: ConcurrentMap[(Identifier, Seq[Type]), Option[TypedADTSort]] =
      new java.util.concurrent.ConcurrentHashMap[(Identifier, Seq[Type]), Option[TypedADTSort]].asScala
    def lookupSort(id: Identifier): Option[ADTSort] = sorts.get(id)
    def lookupSort(id: Identifier, tps: Seq[Type]): Option[TypedADTSort] = {
      typedSortCache.getOrElse(id -> tps, {
        val res = lookupSort(id).map(TypedADTSort(_, tps))
        typedSortCache(id -> tps) = res
        res
      })
    }

    def getSort(id: Identifier): ADTSort =
      lookupSort(id).getOrElse(throw ADTLookupException(id))
    def getSort(id: Identifier, tps: Seq[Type]): TypedADTSort =
      lookupSort(id, tps).getOrElse(throw ADTLookupException(id))

    private val typedConstructorCache: ConcurrentMap[(Identifier, Seq[Type]), Option[TypedADTConstructor]] =
      new java.util.concurrent.ConcurrentHashMap[(Identifier, Seq[Type]), Option[TypedADTConstructor]].asScala
    def lookupConstructor(id: Identifier): Option[ADTConstructor] = constructors.get(id)
    def lookupConstructor(id: Identifier, tps: Seq[Type]): Option[TypedADTConstructor] =
      typedConstructorCache.getOrElse(id -> tps, {
        val res = constructors.get(id).flatMap { cons =>
          lookupSort(cons.sort, tps).flatMap(_.constructors.collectFirst {
            case tcons if tcons.id == id => tcons
          })
        }
        typedConstructorCache(id -> tps) = res
        res
      })

    def getConstructor(id: Identifier): ADTConstructor =
      lookupConstructor(id).getOrElse(throw ADTLookupException(id))
    def getConstructor(id: Identifier, tps: Seq[Type]): TypedADTConstructor =
      lookupConstructor(id, tps).getOrElse(throw ADTLookupException(id))

    private val typedFunctionCache: ConcurrentMap[(Identifier, Seq[Type]), Option[TypedFunDef]] =
      new java.util.concurrent.ConcurrentHashMap[(Identifier, Seq[Type]), Option[TypedFunDef]].asScala
    def lookupFunction(id: Identifier): Option[FunDef] = functions.get(id)
    def lookupFunction(id: Identifier, tps: Seq[Type]): Option[TypedFunDef] =
      typedFunctionCache.getOrElse(id -> tps, {
        val res = lookupFunction(id).map(TypedFunDef(_, tps))
        typedFunctionCache(id -> tps) = res
        res
      })

    def getFunction(id: Identifier): FunDef =
      lookupFunction(id).getOrElse(throw FunctionLookupException(id))
    def getFunction(id: Identifier, tps: Seq[Type]): TypedFunDef =
      lookupFunction(id, tps).getOrElse(throw FunctionLookupException(id))

    override def toString: String = asString(using PrinterOptions(symbols = Some(this)))
    override def asString(using opts: PrinterOptions): String = {
      sorts.map(p => prettyPrint(p._2, opts)).mkString("\n\n") +
      "\n\n-----------\n\n" +
      functions.map(p => prettyPrint(p._2, opts)).mkString("\n\n")
    }

    def transform(t: DefinitionTransformer { val s: self.type }): t.t.Symbols = {
      SymbolTransformer(t).transform(this)
    }

    /** Makes sure these symbols pass a certain number of well-formedness checks, such as
      * - function definition bodies satisfy the declared return types
      * - adt sorts and constructors point to each other correctly
      * - each adt type has at least one instance
      * - adt type parameter flags match between children and parents
      * - every variable is available in the scope of its usage
      */
    @inline def ensureWellFormed: Unit = _tryWF.get.get
    private val _tryWF: Lazy[Try[Unit]] = Lazy(Try(ensureWellFormedSymbols))

    protected def ensureWellFormedSymbols: Unit = {
      // the other checks unfold the field types of sorts, which doesn't terminate on sorts that
      // recurse non-uniformly
      ensureUniformRecursion
      for ((_, fd) <- functions) ensureWellFormedFunction(fd)
      for ((_, sort) <- sorts) ensureWellFormedSort(sort)
    }

    /** Makes sure that no sort recurses through a larger instance of itself, as the nested
      * datatype `Nest[A] = Leaf(a: A) | Node(n: Nest[List[A]])` does: its values hold values of
      * `Nest[List[A]]`, `Nest[List[List[A]]]`, and so on. These infinitely many types can't be
      * declared to an SMT solver, and unfolding their fields doesn't terminate.
      *
      * The type parameter `i` of a sort flows into the type argument `j` of a sort type in one of
      * its fields when that argument mentions it, and grows when the argument isn't the type
      * parameter itself. A sort recurses through larger instances of itself iff a growing flow
      * lies on a cycle of flows, possibly through other sorts.
      */
    protected def ensureUniformRecursion: Unit = {
      type Param = (Identifier, Int)
      // the sort types in `tpe`, including the types of the bound variables of dependent types,
      // which the type deconstructor doesn't return
      def sortTypes(tpe: Type): Seq[ADTType] = tpe match {
        case RefinementType(vd, _) => sortTypes(vd.tpe)
        case PiType(params, to) => params.flatMap(vd => sortTypes(vd.tpe)) ++ sortTypes(to)
        case SigmaType(params, to) => params.flatMap(vd => sortTypes(vd.tpe)) ++ sortTypes(to)
        case adt @ ADTType(_, tps) => adt +: tps.flatMap(sortTypes)
        case NAryType(tps, _) => tps.flatMap(sortTypes)
      }

      val flows: Seq[(Param, Param, Boolean, ADTSort, Type)] = for {
        sort <- sorts.values.toSeq
        cons <- sort.constructors
        vd <- cons.fields
        ADTType(id, args) <- sortTypes(vd.tpe).distinct
        (arg, j) <- args.zipWithIndex
        (tp, i) <- sort.typeArgs.zipWithIndex
        if typeOps.typeParamsOf(arg).contains(tp)
      } yield ((sort.id, i), (id, j), arg != tp, sort, vd.tpe)

      val successors: Map[Param, Seq[Param]] = flows.groupBy(_._1).view.mapValues(_.map(_._2)).toMap
      def reaches(from: Param, to: Param): Boolean = {
        val seen = scala.collection.mutable.Set.empty[Param]
        def rec(p: Param): Boolean = p == to || (seen.add(p) && successors.getOrElse(p, Seq()).exists(rec))
        rec(from)
      }

      for ((from, to, grows, sort, tpe) <- flows if grows && reaches(to, from)) {
        throw NotWellFormedException(sort, Some(
          s"it recurses through larger instances of itself, as its field of type ${tpe.asString(using PrinterOptions(symbols = Some(this)))} does"))
      }
    }

    protected def ensureWellFormedFunction(fd: FunDef) = {
      typeCheck(fd.fullBody, fd.getType)

      if (!fd.getType.isTyped) throw NotWellFormedException(fd)
      if (!(fd.params forall (_.isTyped))) throw NotWellFormedException(fd)

      val unbound: Seq[Variable] = collectWithPC(fd.fullBody, Path.empty `withBounds` fd.params) {
        case (v: Variable, path) if !(path `isBound` v) => v
      }

      if (unbound.nonEmpty) {
        throw NotWellFormedException(fd, Some("Unknown variables: " + (unbound map { _.id.uniqueName } mkString ", ")))
      }
    }

    protected def ensureWellFormedSort(sort: ADTSort) = {
      if (!sort.isWellFormed) throw NotWellFormedException(sort)
      if (!(sort.constructors forall (cons => cons.sort == sort.id))) throw NotWellFormedException(sort)
      if (!(sort.constructors forall (_.fields forall (_.isTyped)))) throw NotWellFormedException(sort)
      if (sort.constructors.flatMap(_.fields).groupBy(_.id).exists(_._2.size > 1)) throw NotWellFormedException(sort)
      ensureStratifiedInvariant(sort)
    }

    /** Makes sure that the invariant of `sort` and the refinements of its field types don't
      * quantify over values that depend on the values of `sort`, directly or in the functions they
      * call. A sort's values depend on another sort's values when they can hold them, or when its
      * invariant or field refinements quantify over them, directly or through other sorts. An
      * uninterpreted call quantifies over the values of its type, as it stands for some value of
      * that type (Stainless's `choose` becomes one). A sort that quantifies over its own values
      * can be paradoxical: the invariant `forall((t: T) => false)` of a sort `T` holds iff `T`
      * has no value, and so does the invariant `forall((b: B) => false)` of a sort `A` whose
      * values are not held by `B`, if the invariant of `B` is that some `A` exists.
      */
    protected def ensureStratifiedInvariant(sort: ADTSort): Unit = {
      // the sorts whose values the values of `tpe` can hold, as fields, elements, arguments,
      // results, type arguments, and so on
      def sortsOf(tpe: Type): Set[Identifier] = typeOps.collect[Identifier] {
        case ADTType(id, _) => Set(id)
        case _ => Set()
      }(tpe)

      // the sorts that `e` quantifies over directly
      def boundSorts(e: Expr): Set[Identifier] = exprOps.collect[Identifier] {
        case Forall(params, _) => params.flatMap(vd => sortsOf(vd.getType)).toSet
        case UninterpretedCall(_, _, _, FunctionType(_, to)) => sortsOf(to)
        case UninterpretedCall(_, _, _, PiType(_, to)) => sortsOf(to)
        case _ => Set()
      }(e)

      // whether the function `id`, or a function it calls, has a quantifier
      def quantifies(id: Identifier): Boolean =
        (transitiveCallees(id) + id).exists(callee => exprOps.exists {
          case _: Forall | _: UninterpretedCall => true
          case _ => false
        }(getFunction(callee).fullBody))

      // the sorts that `e` quantifies over, directly or in the functions it calls, where a
      // function that quantifies could quantify over the sorts it is given as type arguments
      def quantifiedSortsIn(e: Expr): Set[Identifier] = {
        val called = exprOps.functionCallsOf(e).map(_.id)
        (Seq(e) ++ (called ++ transitiveCallees(called)).toSeq.map(getFunction(_).fullBody)).flatMap { body =>
          boundSorts(body) ++ exprOps.collect[Identifier] {
            case FunctionInvocation(callee, tps, _) if quantifies(callee) => tps.flatMap(sortsOf).toSet
            case _ => Set()
          }(body)
        }.toSet
      }

      // the refinements of the field types of `other`
      def fieldRefinements(other: ADTSort): Seq[Expr] =
        other.constructors.flatMap(_.fields).flatMap(vd => typeOps.collect[Expr] {
          case RefinementType(_, pred) => Set(pred)
          case _ => Set()
        }(vd.tpe))

      // the sorts that the invariant and the field refinements of the sort `id` quantify over
      def quantifiedSorts(id: Identifier): Set[Identifier] = {
        val other = getSort(id)
        (other.invariant.map(_.fullBody).toSeq ++ fieldRefinements(other)).flatMap(quantifiedSortsIn).toSet
      }

      // whether the values of the sort `from` depend on the values of `sort`
      def dependsOnSort(from: Identifier): Boolean = {
        val seen = scala.collection.mutable.Set.empty[Identifier]
        def rec(id: Identifier): Boolean = id == sort.id || (seen.add(id) && (lookupSort(id) match {
          case Some(other) =>
            (other.constructors.flatMap(_.fields).flatMap(vd => sortsOf(vd.getType)).toSet ++
              quantifiedSorts(id)).exists(rec)
          case None => false
        }))
        rec(from)
      }

      def check(what: String, es: Seq[Expr]): Unit =
        for (quantified <- es.flatMap(quantifiedSortsIn).find(dependsOnSort)) {
          throw NotWellFormedException(sort, Some(
            s"$what quantifies over the values of $quantified, which depend on those of ${sort.id}"))
        }

      check("its invariant", sort.invariant.map(_.fullBody).toSeq)
      check("the refinement of one of its field types", fieldRefinements(sort))
    }

    // Cheap by design: definitions are equal by identifier, so two tables holding the same
    // identifiers are equal even when their bodies differ. A cache keyed by symbols can
    // therefore return results computed for a table with other bodies under the same identifiers.
    override def equals(that: Any): Boolean = that match {
      case sym: AbstractSymbols =>
        functions == sym.functions && sorts == sym.sorts && modes == sym.modes
      case _ => false
    }

    override def hashCode: Int = (functions.hashCode * 61 + sorts.hashCode) * 61 + modes.hashCode

    def withFunctions(functions: Seq[FunDef]): Symbols
    def withSorts(sorts: Seq[ADTSort]): Symbols

    /** These symbols under other typing modes. */
    def withModes(modes: TypingModes): Symbols =
      if (modes == this.modes) this
      else throw new UnsupportedOperationException(s"These symbols don't support the typing modes $modes")

    def withQuantifiers(quantifiers: QuantifierMode): Symbols =
      withModes(modes.copy(quantifiers = quantifiers))
  }

  sealed class TypeParameterDef(val tp: TypeParameter) extends Definition {
    copiedFrom(tp)

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
    def asString(using PrinterOptions): String = name + (if (args.isEmpty) "" else {
      args.map(arg => self.asString(arg)).mkString("(", ", ", ")")
    })
  }

  /** Denotes that this adt is refined by invariant ''id'' */
  sealed case class HasADTInvariant(id: Identifier) extends Flag("invariant", Seq(id))

  /** Denotes that this adt has an overriden equality relation given by ''id'' */
  sealed case class HasADTEquality(id: Identifier) extends Flag("equality", Seq(id))

  /** Compiler annotations given in the source code as @annot, with their arguments. */
  sealed case class Annotation(override val name: String, val args: Seq[Expr]) extends Flag(name, args)

  /** Algebraic datatype sort definition.
    * An ADT sort is linked to a series of constructors ([[ADTConstructor]]) for this particular sort. */
  class ADTSort(val id: Identifier,
                val tparams: Seq[TypeParameterDef],
                val constructors: Seq[ADTConstructor],
                val flags: Seq[Flag]) extends Definition {
    def typeArgs = tparams.map(_.tp)

    def isInductive(using Symbols): Boolean = {
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

    def isWellFormed(using Symbols): Boolean = {
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
    def invariant(using s: Symbols): Option[FunDef] =
      flags.collectFirst { case HasADTInvariant(id) => s.getFunction(id) }

    def hasInvariant(using Symbols): Boolean = invariant.isDefined

    /** An equality relation defined on this [[ADTSort]] */
    def equality(using s: Symbols): Option[FunDef] =
      flags.collectFirst { case HasADTEquality(id) => s.getFunction(id) }

    def hasEquality(using Symbols): Boolean = equality.isDefined

    /** Wraps this [[ADTSort]] in a in [[TypedADTSort]] with its own type parameters */
    def typed(using Symbols): TypedADTSort = typed(tparams.map(_.tp))

    /** Wraps this [[ADTSort]] in a in [[TypedADTSort]] with the specified type parameters */
    def typed(tps: Seq[Type])(using s: Symbols): TypedADTSort = s.getSort(id, tps)

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
    val fields: Seq[ValDef]) extends Tree {

    def getSort(using s: Symbols): ADTSort = s.getSort(sort)

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
    def typed(using Symbols): TypedADTConstructor = typed(getSort.typeArgs)

    /** Wraps this [[ADTConstructor]] in a in [[TypedADTConstructor]] with the specified type parameters */
    def typed(tps: Seq[Type])(using s: Symbols): TypedADTConstructor = s.getConstructor(id, tps)

    def copy(id: Identifier = id,
             sort: Identifier = sort,
             fields: Seq[ValDef] = fields): ADTConstructor = new ADTConstructor(id, sort, fields)

    override def equals(that: Any): Boolean = that match {
      case c: ADTConstructor => id == c.id
      case _ => false
    }

    override def hashCode: Int = id.hashCode
  }

  /** Represents an [[ADTSort]] whose type parameters have been instantiated to ''tps'' */
  case class TypedADTSort(definition: ADTSort, tps: Seq[Type])(using val symbols: Symbols) extends Tree {
    require(tps.length == definition.tparams.length)
    copiedFrom(definition)

    @inline def id: Identifier = definition.id

    @inline def invariant: Option[TypedFunDef] = _invariant.get
    private val _invariant = Lazy(definition.invariant.map(_.typed(tps)))

    @inline def hasInvariant: Boolean = invariant.isDefined

    @inline def equality: Option[TypedFunDef] = _equality.get
    private val _equality = Lazy(definition.equality.map(_.typed(tps)))

    @inline def hasEquality: Boolean = equality.isDefined

    @inline def tpSubst: Map[TypeParameter, Type] = _tpSubst.get
    private val _tpSubst = Lazy((definition.typeArgs zip tps).toMap.filter(tt => tt._1 != tt._2))

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
    private val _flags = Lazy(definition.flags.map(instantiate))

    val constructors: Seq[TypedADTConstructor] =
      definition.constructors map (TypedADTConstructor(_, this))
  }

  /** Represents an [[ADTConstructor]] whose type parameters have been instantiated to ''tps'' */
  case class TypedADTConstructor(definition: ADTConstructor, sort: TypedADTSort) extends Tree {
    copiedFrom(definition)

    @inline def id: Identifier = definition.id
    @inline def tps: Seq[Type] = sort.tps

    @inline def fields: Seq[ValDef] = _fields.get
    private val _fields = Lazy({
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
    def typed(using Symbols): TypedFunDef = typed(tparams.map(_.tp))

    /** Wraps this [[FunDef]] in a in [[TypedFunDef]] with the specified type parameters */
    def typed(tps: Seq[Type])(using s: Symbols): TypedFunDef = s.getFunction(id, tps)

    /* Auxiliary methods */

    def isRecursive(using s: Symbols) = s.isRecursive(id)

    @inline def typeArgs: Seq[TypeParameter] = _typeArgs.get
    private val _typeArgs = Lazy(tparams.map(_.tp))

    /** Applies this function on its formal parameters */
    @inline def applied = FunctionInvocation(id, typeArgs, params map (_.toVariable))

    /** The (non-dependent) return type of this function definition */
    def getType(using Symbols) = returnType.getType
    def getTpe(stripRefinements: Boolean)(using Symbols) = if stripRefinements then returnType.getType else returnType

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
  case class TypedFunDef(fd: FunDef, tps: Seq[Type])(using val symbols: Symbols) extends Tree {
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
    private val _tpSubst = Lazy((fd.typeArgs zip tps).toMap.filter(tt => tt._1 != tt._2))

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
    private val _params = Lazy({
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
    private val _returnType = Lazy(instantiate(fd.returnType))

    /** The (non-dependent) return type of this typed function definition */
    def getType = returnType.getType
    def getTpe(stripRefinements: Boolean) = if stripRefinements then returnType.getType else returnType

    /** The body of the respective [[FunDef]] instantiated with the real type parameters */
    @inline def fullBody: Expr = _fullBody.get
    private val _fullBody = Lazy(instantiate(fd.fullBody))

    /** The flags of the respective [[FunDef]] instantiated with the real type parameters */
    @inline def flags: Seq[Flag] = _flags.get
    private val _flags = Lazy(fd.flags.map(instantiate))
  }
}
