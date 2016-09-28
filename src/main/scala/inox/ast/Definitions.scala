/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

import scala.collection.mutable.{Map => MutableMap}

/** Provides types that describe Inox definitions. */
trait Definitions { self: Trees =>

  /** The base trait for Inox definitions */
  trait Definition extends Tree {
    val id: Identifier

    override def equals(that: Any): Boolean = that match {
      case d: Definition => id == d.id
      case _=> false
    }

    override def hashCode = id.hashCode
  }

  abstract class LookupException(id: Identifier, what: String)
    extends Exception("Lookup failed for " + what + " with symbol " + id)
  case class FunctionLookupException(id: Identifier) extends LookupException(id, "function")
  case class ADTLookupException(id: Identifier) extends LookupException(id, "adt")

  case class NotWellFormedException(id: Identifier, s: Symbols)
    extends Exception(s"$id not well formed in $s")

  /** Common super-type for [[ValDef]] and [[Expressions.Variable]].
    *
    * Both types share much in common and being able to reason about them
    * in a uniform manner can be useful in certain cases.
    */
  protected[ast] trait VariableSymbol extends Typed {
    val id: Identifier
    val tpe: Type

    def getType(implicit s: Symbols): Type = tpe

    def to[A <: VariableSymbol](implicit ev: VariableConverter[A]): A = ev.convert(this)

    override def equals(that: Any): Boolean = that match {
      case vs: VariableSymbol => id == vs.id && tpe == vs.tpe
      case _ => false
    }

    override def hashCode: Int = 61 * id.hashCode + tpe.hashCode
  }

  implicit def variableSymbolOrdering[VS <: VariableSymbol]: Ordering[VS] =
    Ordering.by(e => e.id)

  abstract class VariableConverter[B <: VariableSymbol] {
    def convert(a: VariableSymbol): B
  }

  implicit def convertToVal = new VariableConverter[ValDef] {
    def convert(vs: VariableSymbol): ValDef = vs match {
      case v: ValDef => v
      case _ => ValDef(vs.id, vs.tpe)
    }
  }

  implicit def convertToVariable = new VariableConverter[Variable] {
    def convert(vs: VariableSymbol): Variable = vs match {
      case v: Variable => v
      case _ => Variable(vs.id, vs.tpe)
    }
  }

  /** 
    * A ValDef declares a formal parameter (with symbol [[id]]) to be of a certain type.
    */
  case class ValDef(id: Identifier, tpe: Type) extends Definition with VariableSymbol {
    /** Transform this [[ValDef]] into a [[Expressions.Variable Variable]] */
    def toVariable: Variable = to[Variable]
    def freshen: ValDef = ValDef(id.freshen, tpe).copiedFrom(this)

    val flags: Set[Flag] = Set.empty

    override def equals(that: Any): Boolean = super[VariableSymbol].equals(that)
    override def hashCode: Int = super[VariableSymbol].hashCode
  }

  type Symbols >: Null <: AbstractSymbols

  val NoSymbols: Symbols

  /** Provides the class and function definitions of a program and lookups on them */
  trait AbstractSymbols
     extends Printable
        with TypeOps
        with SymbolOps
        with CallGraph
        with Constructors
        with Paths { self0: Symbols =>

    val adts: Map[Identifier, ADTDefinition]
    val functions: Map[Identifier, FunDef]

    protected val trees: self.type = self
    protected val symbols: this.type = this

    // @nv: this is a hack to reinject `this` into the set of implicits
    // in scope when using the pattern:
    // {{{
    //    implicit val symbols: Symbols
    //    import symbols._
    // }}}
    // which seems to remove `symbols` from the set of current implicits
    // for some mysterious reason.
    implicit def implicitSymbols: this.type = this

    private val typedADTCache: MutableMap[(Identifier, Seq[Type]), Option[TypedADTDefinition]] = MutableMap.empty
    def lookupADT(id: Identifier): Option[ADTDefinition] = adts.get(id)
    def lookupADT(id: Identifier, tps: Seq[Type]): Option[TypedADTDefinition] =
      typedADTCache.getOrElseUpdate(id -> tps, lookupADT(id).map(_.typed(tps)))

    def getADT(id: Identifier): ADTDefinition = lookupADT(id).getOrElse(throw ADTLookupException(id))
    def getADT(id: Identifier, tps: Seq[Type]): TypedADTDefinition = lookupADT(id, tps).getOrElse(throw ADTLookupException(id))

    private val typedFunctionCache: MutableMap[(Identifier, Seq[Type]), Option[TypedFunDef]] = MutableMap.empty
    def lookupFunction(id: Identifier): Option[FunDef] = functions.get(id)
    def lookupFunction(id: Identifier, tps: Seq[Type]): Option[TypedFunDef] =
      typedFunctionCache.getOrElseUpdate(id -> tps, lookupFunction(id).map(_.typed(tps)(this)))

    def getFunction(id: Identifier): FunDef = lookupFunction(id).getOrElse(throw FunctionLookupException(id))
    def getFunction(id: Identifier, tps: Seq[Type]): TypedFunDef = lookupFunction(id, tps).getOrElse(throw FunctionLookupException(id))

    override def toString: String = asString(PrinterOptions.fromSymbols(this, InoxContext.printNames))
    override def asString(implicit opts: PrinterOptions): String = {
      adts.map(p => prettyPrint(p._2, opts)).mkString("\n\n") +
      "\n\n-----------\n\n" +
      functions.map(p => prettyPrint(p._2, opts)).mkString("\n\n")
    }

    def transform(t: TreeTransformer): Symbols = NoSymbols.withFunctions {
      functions.values.toSeq.map(fd => new FunDef(
        fd.id,
        fd.tparams, // type parameters can't be transformed!
        fd.params.map(vd => t.transform(vd)),
        t.transform(fd.returnType),
        t.transform(fd.fullBody),
        fd.flags))
    }.withADTs {
      adts.values.toSeq.map {
        case sort: ADTSort => sort
        case cons: ADTConstructor => new ADTConstructor(
          cons.id,
          cons.tparams,
          cons.sort,
          cons.fields.map(t.transform),
          cons.flags)
      }
    }

    override def equals(that: Any): Boolean = that match {
      case sym: AbstractSymbols => functions == sym.functions && adts == sym.adts
      case _ => false
    }

    override def hashCode: Int = functions.hashCode * 61 + adts.hashCode

    def withFunctions(functions: Seq[FunDef]): Symbols
    def withADTs(adts: Seq[ADTDefinition]): Symbols
  }

  case class TypeParameterDef(tp: TypeParameter) extends Definition {
    def freshen = TypeParameterDef(tp.freshen)
    val id = tp.id
  }

  /** Represents source code annotations and some other meaningful flags. */
  abstract class Flag(name: String, args: Seq[Any]) extends Printable {
    def asString(implicit opts: PrinterOptions): String = name + (if (args.isEmpty) "" else {
      args.map(arg => self.asString(arg)(opts)).mkString("(", ", ", ")")
    })
  }

  /** Denotes that this adt is refined by invariant ''id'' */
  case class HasADTInvariant(id: Identifier) extends Flag("invariant", Seq(id))

  // Compiler annotations given in the source code as @annot
  case class Annotation(val name: String, val args: Seq[Any]) extends Flag(name, args)

  def extractFlag(name: String, args: Seq[Any]): Flag = (name, args) match {
    case ("invariant", id: Identifier) => HasADTInvariant(id)
    case _ => Annotation(name, args)
  }

  /** Represents an ADT definition (either the ADT sort or a constructor). */
  sealed trait ADTDefinition extends Definition {
    val id: Identifier
    val tparams: Seq[TypeParameterDef]
    val flags: Set[Flag]

    /** The root of the class hierarchy */
    def root(implicit s: Symbols): ADTDefinition

    /** An invariant that refines this [[ADTDefinition]] */
    def invariant(implicit s: Symbols): Option[FunDef] = {
      val rt = root
      if (rt ne this) rt.invariant
      else flags.collect { case HasADTInvariant(id) => id }.headOption.map(s.getFunction)
    }

    def hasInvariant(implicit s: Symbols): Boolean = invariant.isDefined

    val isSort: Boolean

    def typeArgs = tparams map (_.tp)

    def typed(tps: Seq[Type])(implicit s: Symbols): TypedADTDefinition
    def typed(implicit s: Symbols): TypedADTDefinition
  }

  /** Algebraic datatype sort definition.
    * An ADT sort is linked to a series of constructors ([[ADTConstructor]]) for this particular sort. */
  class ADTSort(val id: Identifier,
                val tparams: Seq[TypeParameterDef],
                val cons: Seq[Identifier],
                val flags: Set[Flag]) extends ADTDefinition {
    val isSort = true

    def constructors(implicit s: Symbols): Seq[ADTConstructor] = cons
      .map(id => s.getADT(id) match {
        case cons: ADTConstructor => cons
        case _ => throw NotWellFormedException(id, s)
      })

    def isInductive(implicit s: Symbols): Boolean = {
      def induct(tpe: Type, seen: Set[ADTDefinition]): Boolean = tpe match {
        case adt: ADTType =>
          val tadt = adt.lookupADT.getOrElse(throw ADTLookupException(adt.id))
          val root = tadt.definition.root
          seen(root) || {
            val constructors = root match {
              case tcons: ADTConstructor => Seq(tcons)
              case tsort: ADTSort => tsort.constructors
            }

            constructors.exists(tcons => tcons.fields.exists(vd => induct(vd.tpe, seen + root)))
          }

        case TupleType(tpes) =>
          tpes.exists(tpe => induct(tpe, seen))

        case _ => false
      }

      if (this == root && !this.isSort) false
      else constructors.exists { cons =>
        cons.fields.exists(vd => induct(vd.getType, Set(root)))
      }
    }

    def root(implicit s: Symbols): ADTDefinition = this

    def typed(implicit s: Symbols): TypedADTSort = typed(tparams.map(_.tp))
    def typed(tps: Seq[Type])(implicit s: Symbols): TypedADTSort = {
      require(tps.length == tparams.length)
      TypedADTSort(this, tps)
    }
  }

  /** Case classes/ ADT constructors. For single-case classes these may coincide
    *
    * @param id      -- The identifier that refers to this ADT constructor.
    * @param tparams -- The type parameters taken by this constructor.
    *                   Note that these MUST match the type parameters taken by [[sort]] when it is defined.
    * @param sort    -- The base sort of this constructor (corresponds to the abstract parent class).
    * @param fields  -- The fields of this constructor (types may depend on [[tparams]]).
    * @param flags   -- The Flags that annotate this constructor.
    */
  class ADTConstructor(val id: Identifier,
                       val tparams: Seq[TypeParameterDef],
                       val sort: Option[Identifier],
                       val fields: Seq[ValDef],
                       val flags: Set[Flag]) extends ADTDefinition {

    val isSort = false
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

    def root(implicit s: Symbols): ADTDefinition = sort.map(id => s.getADT(id).root).getOrElse(this)

    def typed(implicit s: Symbols): TypedADTConstructor = typed(tparams.map(_.tp))
    def typed(tps: Seq[Type])(implicit s: Symbols): TypedADTConstructor = {
      require(tps.length == tparams.length)
      TypedADTConstructor(this, tps)
    }
  }

  /** Represents an [[ADTDefinition]] whose type parameters have been instantiated to ''tps'' */
  sealed abstract class TypedADTDefinition extends Tree {
    val definition: ADTDefinition
    val tps: Seq[Type]
    implicit val symbols: Symbols

    lazy val id: Identifier = definition.id
    /** The root of the class hierarchy */
    lazy val root: TypedADTDefinition = definition.root.typed(tps)
    lazy val invariant: Option[TypedFunDef] = definition.invariant.map(_.typed(tps))
    lazy val hasInvariant: Boolean = invariant.isDefined

    def toType = ADTType(definition.id, tps)

    def toConstructor = this match {
      case tcons: TypedADTConstructor => tcons
      case _ => throw NotWellFormedException(definition.id, symbols)
    }

    def toSort = this match {
      case tsort: TypedADTSort => tsort
      case _ => throw NotWellFormedException(definition.id, symbols)
    }
  }

  /** Represents an [[ADTSort]] whose type parameters have been instantiated to ''tps'' */
  case class TypedADTSort(definition: ADTSort, tps: Seq[Type])(implicit val symbols: Symbols) extends TypedADTDefinition {
    lazy val constructors: Seq[TypedADTConstructor] = definition.constructors.map(_.typed(tps))
  }

  /** Represents an [[ADTConstructor]] whose type parameters have been instantiated to ''tps'' */
  case class TypedADTConstructor(definition: ADTConstructor, tps: Seq[Type])(implicit val symbols: Symbols) extends TypedADTDefinition {
    lazy val fields: Seq[ValDef] = {
      val tmap = (definition.typeArgs zip tps).toMap
      if (tmap.isEmpty) definition.fields
      else definition.fields.map(vd => vd.copy(tpe = symbols.instantiateType(vd.tpe, tmap)))
    }

    lazy val fieldsTypes = fields.map(_.tpe)

    lazy val sort: Option[TypedADTSort] = definition.sort.map(id => symbols.getADT(id) match {
      case sort: ADTSort => TypedADTSort(sort, tps)
      case _ => throw NotWellFormedException(id, symbols)
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
    val flags: Set[Flag]
  ) extends Definition {

    /** Wraps this [[FunDef]] in a in [[TypedFunDef]] with the specified type parameters */
    def typed(tps: Seq[Type])(implicit s: Symbols): TypedFunDef = {
      assert(tps.size == tparams.size)
      TypedFunDef(this, tps)
    }

    /** Wraps this [[FunDef]] in a in [[TypedFunDef]] with its own type parameters */
    def typed(implicit s: Symbols): TypedFunDef = typed(tparams.map(_.tp))

    /* Auxiliary methods */

    def isRecursive(implicit s: Symbols) = s.transitiveCallees(this) contains this

    def typeArgs = tparams map (_.tp)

    /** Applies this function on some arguments; type parameters are inferred. */
    def applied(args: Seq[Expr])(implicit s: Symbols): FunctionInvocation = s.functionInvocation(this, args)
    /** Applies this function on its formal parameters */
    def applied = FunctionInvocation(id, typeArgs, params map (_.toVariable))
  }


  /** Represents a [[FunDef]] whose type parameters have been instantiated with the specified types */
  case class TypedFunDef(fd: FunDef, tps: Seq[Type])(implicit symbols: Symbols) extends Tree {
    val id = fd.id

    def signature = {
      if (tps.nonEmpty) {
        id.toString+tps.mkString("[", ", ", "]")
      } else {
        id.toString
      }
    }

    private lazy val typesMap: Map[TypeParameter, Type] = {
      (fd.typeArgs zip tps).toMap.filter(tt => tt._1 != tt._2)
    }

    /** A [[Type]] instantiated with this [[TypedFunDef]]'s type instantiation */
    def instantiate(t: Type): Type = symbols.instantiateType(t, typesMap)

    /** A [[Expr]] instantiated with this [[TypedFunDef]]'s type instantiation */
    def instantiate(e: Expr): Expr = symbols.instantiateType(e, typesMap)

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
    def applied: FunctionInvocation = applied(params map { _.toVariable })

    /** The paremeters of the respective [[FunDef]] instantiated with the real type parameters */
    lazy val params: Seq[ValDef] = {
      if (typesMap.isEmpty) {
        fd.params
      } else {
        fd.params.map(vd => vd.copy(tpe = instantiate(vd.getType)))
      }
    }

    /** The function type corresponding to this [[TypedFunDef]]'s arguments and return type */
    lazy val functionType = FunctionType(params.map(_.getType).toList, returnType)

    /** The return type of the respective [[FunDef]] instantiated with the real type parameters */
    lazy val returnType: Type = instantiate(fd.returnType)

    /** The body of the respective [[FunDef]] instantiated with the real type parameters */
    lazy val fullBody = instantiate(fd.fullBody)
  }
}
