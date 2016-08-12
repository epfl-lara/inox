/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

import scala.collection.mutable.{Map => MutableMap}

/** Provides types that describe Inox definitions. */
trait Definitions { self: Trees =>

  /** The base trait for Inox definitions */
  sealed trait Definition extends Tree {
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
  case class ClassLookupException(id: Identifier) extends LookupException(id, "class")

  case class NotWellFormedException(id: Identifier, s: Symbols)
    extends Exception(s"$id not well formed in $s")

  /** Common super-type for [[ValDef]] and [[Expressions.Variable]].
    *
    * Both types share much in common and being able to reason about them
    * in a uniform manner can be useful in certain cases.
    */
  private[ast] trait VariableSymbol extends Typed {
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

  sealed abstract class VariableConverter[B <: VariableSymbol] {
    def convert(a: VariableSymbol): B
  }

  implicit def convertToVal = new VariableConverter[ValDef] {
    def convert(vs: VariableSymbol): ValDef = vs match {
      case v: ValDef => v
      case _ => ValDef(vs.id, vs.tpe)
    }
  }

  implicit def convertToVar = new VariableConverter[Variable] {
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

    override def equals(that: Any): Boolean = super[VariableSymbol].equals(that)
    override def hashCode: Int = super[VariableSymbol].hashCode
  }

  type Symbols >: Null <: AbstractSymbols

  /** Provides the class and function definitions of a program and lookups on them */
  trait AbstractSymbols
     extends Printable
        with TypeOps
        with SymbolOps
        with CallGraph
        with Constructors
        with Paths { self0: Symbols =>

    val classes: Map[Identifier, ClassDef]
    val functions: Map[Identifier, FunDef]

    private[ast] val trees: self.type = self
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

    private val typedClassCache: MutableMap[(Identifier, Seq[Type]), Option[TypedClassDef]] = MutableMap.empty
    def lookupClass(id: Identifier): Option[ClassDef] = classes.get(id)
    def lookupClass(id: Identifier, tps: Seq[Type]): Option[TypedClassDef] =
      typedClassCache.getOrElseUpdate(id -> tps, lookupClass(id).map(_.typed(tps)))

    def getClass(id: Identifier): ClassDef = lookupClass(id).getOrElse(throw ClassLookupException(id))
    def getClass(id: Identifier, tps: Seq[Type]): TypedClassDef = lookupClass(id, tps).getOrElse(throw ClassLookupException(id))

    private val typedFunctionCache: MutableMap[(Identifier, Seq[Type]), Option[TypedFunDef]] = MutableMap.empty
    def lookupFunction(id: Identifier): Option[FunDef] = functions.get(id)
    def lookupFunction(id: Identifier, tps: Seq[Type]): Option[TypedFunDef] =
      typedFunctionCache.getOrElseUpdate(id -> tps, lookupFunction(id).map(_.typed(tps)(this)))

    def getFunction(id: Identifier): FunDef = lookupFunction(id).getOrElse(throw FunctionLookupException(id))
    def getFunction(id: Identifier, tps: Seq[Type]): TypedFunDef = lookupFunction(id, tps).getOrElse(throw FunctionLookupException(id))

    override def toString: String = asString(PrinterOptions.fromSymbols(this, InoxContext.printNames))
    override def asString(implicit opts: PrinterOptions): String = {
      classes.map(p => PrettyPrinter(p._2, opts)).mkString("\n\n") +
      "\n\n-----------\n\n" +
      functions.map(p => PrettyPrinter(p._2, opts)).mkString("\n\n")
    }

    def transform(t: TreeTransformer): Symbols
    def extend(functions: Seq[FunDef] = Seq.empty, classes: Seq[ClassDef] = Seq.empty): Symbols
  }

  case class TypeParameterDef(tp: TypeParameter) extends Definition {
    def freshen = TypeParameterDef(tp.freshen)
    val id = tp.id
  }
 
  /** A trait that represents flags that annotate a ClassDef with different attributes */
  sealed trait ClassFlag

  object ClassFlag {
    def fromName(name: String, args: Seq[Option[Any]]): ClassFlag = Annotation(name, args)
  }

  /** A trait that represents flags that annotate a FunDef with different attributes */
  sealed trait FunctionFlag

  object FunctionFlag {
    def fromName(name: String, args: Seq[Option[Any]]): FunctionFlag = name match {
      case "inline" => IsInlined
      case _ => Annotation(name, args)
    }
  }

  // Compiler annotations given in the source code as @annot
  case class Annotation(annot: String, args: Seq[Option[Any]]) extends FunctionFlag with ClassFlag
  /** Denotes that this class is refined by invariant ''id'' */
  case class HasADTInvariant(id: Identifier) extends ClassFlag
  // Is inlined
  case object IsInlined extends FunctionFlag

  /** Represents a class definition (either an abstract- or a case-class).
    * In functional terms, abstract classes are ADTs and case classes are ADT constructors.
    */
  sealed trait ClassDef extends Definition {
    val id: Identifier
    val tparams: Seq[TypeParameterDef]
    val flags: Set[ClassFlag]

    def annotations: Set[String] = extAnnotations.keySet
    def extAnnotations: Map[String, Seq[Option[Any]]] = flags.collect { case Annotation(s, args) => s -> args }.toMap

    /** The root of the class hierarchy */
    def root(implicit s: Symbols): ClassDef

    /** An invariant that refines this [[ClassDef]] */
    def invariant(implicit s: Symbols): Option[FunDef] = {
      val rt = root
      if (rt ne this) rt.invariant
      else flags.collect { case HasADTInvariant(id) => id }.headOption.map(s.getFunction)
    }

    def hasInvariant(implicit s: Symbols): Boolean = invariant.isDefined

    val isAbstract: Boolean

    def typeArgs = tparams map (_.tp)

    def typed(tps: Seq[Type])(implicit s: Symbols): TypedClassDef
    def typed(implicit s: Symbols): TypedClassDef
  }

  /** Abstract classes / ADTs */
  class AbstractClassDef(val id: Identifier,
                         val tparams: Seq[TypeParameterDef],
                         val children: Seq[Identifier],
                         val flags: Set[ClassFlag]) extends ClassDef {
    val isAbstract = true

    def descendants(implicit s: Symbols): Seq[CaseClassDef] = children
      .map(id => s.getClass(id) match {
        case ccd: CaseClassDef => ccd
        case _ => throw NotWellFormedException(id, s)
      })

    def isInductive(implicit s: Symbols): Boolean = {
      def induct(tpe: Type, seen: Set[ClassDef]): Boolean = tpe match {
        case ct: ClassType =>
          val tcd = ct.lookupClass.getOrElse(throw ClassLookupException(ct.id))
          val root = tcd.cd.root
          seen(root) || (tcd match {
            case tccd: TypedCaseClassDef =>
              tccd.fields.exists(vd => induct(vd.getType, seen + root))
            case _ => false
          })
        case TupleType(tpes) =>
          tpes.exists(tpe => induct(tpe, seen))
        case _ => false
      }

      if (this == root && !this.isAbstract) false
      else descendants.exists { ccd =>
        ccd.fields.exists(vd => induct(vd.getType, Set(root)))
      }
    }

    def root(implicit s: Symbols): ClassDef = this

    def typed(implicit s: Symbols): TypedAbstractClassDef = typed(tparams.map(_.tp))
    def typed(tps: Seq[Type])(implicit s: Symbols): TypedAbstractClassDef = {
      require(tps.length == tparams.length)
      TypedAbstractClassDef(this, tps)
    }
  }

  /** Case classes/ ADT constructors. For single-case classes these may coincide
    *
    * @param id
    * @param tparams
    * @param parent
    * @param fields
    * @param flags
    */
  class CaseClassDef(val id: Identifier,
                     val tparams: Seq[TypeParameterDef],
                     val parent: Option[Identifier],
                     val fields: Seq[ValDef],
                     val flags: Set[ClassFlag]) extends ClassDef {

    val isAbstract = false
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

    def root(implicit s: Symbols): ClassDef = parent.map(id => s.getClass(id).root).getOrElse(this)

    def typed(implicit s: Symbols): TypedCaseClassDef = typed(tparams.map(_.tp))
    def typed(tps: Seq[Type])(implicit s: Symbols): TypedCaseClassDef = {
      require(tps.length == tparams.length)
      TypedCaseClassDef(this, tps)
    }
  }

  /** Represents a [[ClassDef]] whose type parameters have been instantiated to ''tps'' */
  sealed abstract class TypedClassDef extends Tree {
    val cd: ClassDef
    val tps: Seq[Type]
    implicit val symbols: Symbols

    val id: Identifier = cd.id
    /** The root of the class hierarchy */
    lazy val root: TypedClassDef = cd.root.typed(tps)
    lazy val invariant: Option[TypedFunDef] = cd.invariant.map(_.typed(tps))
    lazy val hasInvariant: Boolean = invariant.isDefined

    def toType = ClassType(cd.id, tps)

    def toCase = this match {
      case tccd: TypedCaseClassDef => tccd
      case _ => throw NotWellFormedException(cd.id, symbols)
    }

    def toAbstract = this match {
      case accd: TypedAbstractClassDef => accd
      case _ => throw NotWellFormedException(cd.id, symbols)
    }
  }

  /** Represents an [[AbstractClassDef]] whose type parameters have been instantiated to ''tps'' */
  case class TypedAbstractClassDef(cd: AbstractClassDef, tps: Seq[Type])(implicit val symbols: Symbols) extends TypedClassDef {
    def descendants: Seq[TypedCaseClassDef] = cd.descendants.map(_.typed(tps))
  }

  /** Represents a [[CaseClassDef]] whose type parameters have been instantiated to ''tps'' */
  case class TypedCaseClassDef(cd: CaseClassDef, tps: Seq[Type])(implicit val symbols: Symbols) extends TypedClassDef {
    lazy val fields: Seq[ValDef] = {
      val tmap = (cd.typeArgs zip tps).toMap
      if (tmap.isEmpty) cd.fields
      else cd.fields.map(vd => vd.copy(tpe = symbols.instantiateType(vd.getType, tmap)))
    }

    lazy val fieldsTypes = fields.map(_.tpe)

    lazy val parent: Option[TypedAbstractClassDef] = cd.parent.map(id => symbols.getClass(id) match {
      case acd: AbstractClassDef => TypedAbstractClassDef(acd, tps)
      case _ => throw NotWellFormedException(id, symbols)
    })
  }


  /** Function definition
    *
    * @param id The identifier which will refer to this function.
    * @param body The optional body of this function. Empty body functions are treated as uninterpreted
    * @param flags Flags that annotate this function with attributes.
    */
  class FunDef(
    val id: Identifier,
    val tparams: Seq[TypeParameterDef],
    val params: Seq[ValDef],
    val returnType: Type,
    val fullBody: Expr,
    val flags: Set[FunctionFlag]
  ) extends Definition {

    def annotations: Set[String] = extAnnotations.keySet
    def extAnnotations: Map[String, Seq[Option[Any]]] = flags.collect {
      case Annotation(s, args) => s -> args
    }.toMap

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
