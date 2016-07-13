/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import scala.collection.mutable.{Map => MutableMap}

trait Definitions { self: Trees =>

  sealed trait Definition extends Tree {
    val id: Identifier

    override def equals(that: Any): Boolean = that match {
      case d: Definition => id == d.id
      case _=> false
    }

    override def hashCode = id.hashCode
  }

  abstract class LookupException(id: Identifier, what: String) extends Exception("Lookup failed for " + what + " with symbol " + id)
  case class FunctionLookupException(id: Identifier) extends LookupException(id, "function")
  case class ClassLookupException(id: Identifier) extends LookupException(id, "class")

  /** 
   *  A ValDef declares a formal parameter (with symbol [[id]]) to be of a certain type.
   */
  case class ValDef(id: Identifier, tpe: Type) extends Definition with Typed {
    def getType(implicit p: Program): Type = tpe

    /** Transform this [[ValDef]] into a [[Expressions.Variable Variable]] */
    def toVariable: Variable = Variable(id, tpe)
  }

  /** A wrapper for a program. For now a program is simply a single object. */
  case class Program(classes: Map[Identifier, ClassDef], functions: Map[Identifier, FunDef]) extends Tree {
    lazy val callGraph = new CallGraph(this)

    private val typedClassCache: MutableMap[(Identifier, Seq[Type]), TypedClassDef] = MutableMap.empty
    def lookupClass(id: Identifier): Option[ClassDef] = classes.get(id)
    def lookupClass(id: Identifier, tps: Seq[Type]): Option[TypedClassDef] =
      typedClassCache.getOrElseUpdated(id -> tps, lookupClass(id).typed(tps))

    def getClass(id: Identifier): ClassDef = lookupClass(id).getOrElse(throw ClassLookupException(id))
    def getClass(id: Identifier, tps: Seq[Type]): TypedClassDef = lookupClass(id, tps).getOrElse(throw ClassLookupException(id))

    private val typedFunctionCache: MutableMap[(Identifier, Seq[Type]), TypedFunDef] = MutableMap.empty
    def lookupFunction(id: Identifier): Option[FunDef] = functions.get(id)
    def lookupFunction(id: Identifier, tps: Seq[Type]): Option[TypedFunDef] =
      typedFunctionCache.getOrElseUpdated(id -> tps, lookupFunction(id).typed(tps))

    def getFunction(id: Identifier): FunDef = lookupFunction(id).getOrElse(throw FunctionLookupException(id))
    def getFunction(id: Identifier, tps: Seq[Type]): TypedFunDef = lookupFunction(id, tps).getOrElse(throw FunctionLookupException(id))
  }

  object Program {
    lazy val empty: Program = Program(Nil)
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
  // Class has ADT invariant method
  case class HasADTInvariant(id: Identifier) extends ClassFlag
  // Is inlined
  case object IsInlined extends FunctionFlag

  /** Represents a class definition (either an abstract- or a case-class) */
  sealed trait ClassDef extends Definition {
    val id: Identifier
    val tparams: Seq[TypeParameterDef]
    val fields: Seq[ValDef]
    val flags: Set[ClassFlag]

    val parent: Option[Identifier]
    val children: Seq[Identifier]

    def hasParent = parent.isDefined

    def invariant(implicit p: Program): Option[FunDef] =
      flags.collect { case HasADTInvariant(id) => id }.map(p.getFunction)

    def annotations: Set[String] = extAnnotations.keySet
    def extAnnotations: Map[String, Seq[Option[Any]]] = flags.collect { case Annotation(s, args) => s -> args }.toMap

    def ancestors(implicit p: Program): Seq[ClassDef] = parent
      .map(p.getClass).toSeq
      .flatMap(parentCls => parentCls +: parentCls.ancestors)

    def root(implicit p: Program) = ancestors.lastOption.getOrElse(this)

    def descendants(implicit p: Program): Seq[ClassDef] = children
      .map(p.getClass)
      .flatMap(cd => cd +: cd.descendants)

    def ccDescendants(implicit p: Program): Seq[CaseClassDef] =
      descendants collect { case ccd: CaseClassDef => ccd }

    def isInductive(implicit p: Program): Boolean = {
      def induct(tpe: Type, seen: Set[ClassDef]): Boolean = tpe match {
        case ct: ClassType =>
          val tcd = ct.lookupClass.getOrElse(throw ClassLookupException(ct.id))
          val root = tcd.cd.root
          seen(root) || tcd.fields.forall(vd => induct(vd.getType, seen + root))
        case TupleType(tpes) =>
          tpes.forall(tpe => induct(tpe, seen))
        case _ => true
      }

      if (this == root && !this.isAbstract) false
      else if (this != root) root.isInductive
      else ccDescendants.forall { ccd =>
        ccd.fields.forall(vd => induct(vd.getType, Set(root)))
      }
    }

    val isAbstract: Boolean

    def typeArgs = tparams map (_.tp)

    def typed(tps: Seq[Type]): TypedClassDef
    def typed: TypedClassDef
  }

  /** Abstract classes. */
  class AbstractClassDef(val id: Identifier,
                         val tparams: Seq[TypeParameterDef],
                         val parent: Option[Identifier],
                         val children: Seq[Identifier],
                         val flags: Set[Flag]) extends ClassDef {

    val fields = Nil
    val isAbstract = true

    def typed: TypedAbstractClassDef = typed(tparams.map(_.tp))
    def typed(tps: Seq[Type]): TypedAbstractClassDef = {
      require(tps.length == tparams.length)
      TypedAbstractClassDef(this, tps)
    }
  }

  /** Case classes/ case objects. */
  class CaseClassDef(val id: Identifier,
                     val tparams: Seq[TypeParameterDef],
                     val parent: Option[Identifier],
                     val fields: Seq[ValDef],
                     val flags: Set[Flag]) extends ClassDef {

    val children = Nil
    val isAbstract = false

    def selectorID2Index(id: Identifier) : Int = {
      val index = fields.indexWhere(_.id == id)

      if (index < 0) {
        scala.sys.error(
          "Could not find '"+id+"' ("+id.uniqueName+") within "+
          fields.map(_.id.uniqueName).mkString(", ")
        )
      } else index
    }

    def typed: TypedCaseClassDef = typed(tparams.map(_.tp))
    def typed(tps: Seq[Type]): TypedCaseClassDef = {
      require(tps.length == tparams.length)
      TypedCaseClassDef(this, tps)
    }
  }

  sealed abstract class TypedClassDef extends Tree {
    val cd: ClassDef
    val tps: Seq[Type]
    implicit val program: Program

    val id: Identifier = cd.id
    lazy val fields: Seq[ValDef] = {
      val tmap = (cd.typeArgs zip tps).toMap
      if (tmap.isEmpty) cd.fields
      else classDef.fields.map(vd => vd.copy(tpe = instantiateType(vd.getType, tmap)))
    }

    lazy val parent: Option[TypedAbstractClassDef] = cd.parent.map(id => p.getClass(id) match {
      case acd: AbstractClassDef => TypedAbstractClassDef(acd, tps)
      case _ => scala.sys.error("Expected parent to be an AbstractClassDef")
    })

    lazy val invariant: Option[TypedFunDef] = cd.invariant.map { fd =>
      TypedFunDef(fd, tps)
    }

    lazy val root = parent.map(_.root).getOrElse(this)

    def descendants: Seq[TypedClassDef] = cd.descendants.map(_.typed(tps))
    def ccDescendants: Seq[TypedCaseClassDef] = cd.ccDescendants.map(_.typed(tps))
  }

  case class TypedAbstractClassDef(cd: AbstractClassDef, tps: Seq[Type])(implicit program: Program) extends TypedClassDef
  case class TypedCaseClassDef(cd: AbstractClassDef, tps: Seq[Type])(implicit program: Program) extends TypedClassDef


  /** Function/method definition.
    *
    *  This class represents methods or fields of objects or classes. By "fields" we mean
    *  fields defined in the body of a class/object, not the constructor arguments of a case class
    *  (those are accessible through [[leon.purescala.Definitions.ClassDef.fields]]).
    *
    *  When it comes to verification, all are treated the same (as functions).
    *  They are only differentiated when it comes to code generation/ pretty printing.
    *  By default, the FunDef represents a function/method as opposed to a field,
    *  unless otherwise specified by its flags.
    *
    *  Bear in mind that [[id]] will not be consistently typed.
    */
  class FunDef(
    val id: Identifier,
    val tparams: Seq[TypeParameterDef],
    val params: Seq[ValDef],
    val returnType: Type,
    val fullBody: Expr,
    val flags: Set[Flag]
  ) extends Definition {

    /* Body manipulation */

    lazy val body: Option[Expr] = withoutSpec(fullBody)
    lazy val precondition = preconditionOf(fullBody)
    lazy val precOrTrue = precondition getOrElse BooleanLiteral(true)

    lazy val postcondition = postconditionOf(fullBody)
    lazy val postOrTrue = postcondition getOrElse {
      val arg = ValDef(FreshIdentifier("res", returnType, alwaysShowUniqueID = true))
      Lambda(Seq(arg), BooleanLiteral(true))
    }

    def hasBody          = body.isDefined
    def hasPrecondition  = precondition.isDefined
    def hasPostcondition = postcondition.isDefined

    def annotations: Set[String] = extAnnotations.keySet
    def extAnnotations: Map[String, Seq[Option[Any]]] = flags.collect {
      case Annotation(s, args) => s -> args
    }.toMap

    def canBeLazyField    = flags.contains(IsField(true))  && params.isEmpty && tparams.isEmpty
    def canBeStrictField  = flags.contains(IsField(false)) && params.isEmpty && tparams.isEmpty
    def canBeField        = canBeLazyField || canBeStrictField
    def isRealFunction    = !canBeField
    def isInvariant       = flags contains IsADTInvariant

    /* Wrapping in TypedFunDef */

    def typed(tps: Seq[Type]): TypedFunDef = {
      assert(tps.size == tparams.size)
      TypedFunDef(this, tps)
    }

    def typed: TypedFunDef = typed(tparams.map(_.tp))

    /* Auxiliary methods */

    def isRecursive(implicit p: Program) = p.callGraph.transitiveCallees(this) contains this

    def paramIds = params map { _.id }

    def typeArgs = tparams map (_.tp)

    def applied(args: Seq[Expr]): FunctionInvocation = Constructors.functionInvocation(this, args)
    def applied = FunctionInvocation(this.typed, this.paramIds map Variable)
  }


  // Wrapper for typing function according to valuations for type parameters
  case class TypedFunDef(fd: FunDef, tps: Seq[Type])(implicit program: Program) extends Tree {
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

    def translated(t: Type): Type = instantiateType(t, typesMap)

    def translated(e: Expr): Expr = instantiateType(e, typesMap, paramsMap)

    /** A mapping from this [[TypedFunDef]]'s formal parameters to real arguments
      *
      * @param realArgs The arguments to which the formal argumentas are mapped
      * */
    def paramSubst(realArgs: Seq[Expr]) = {
      require(realArgs.size == params.size)
      (paramIds zip realArgs).toMap
    }

    /** Substitute this [[TypedFunDef]]'s formal parameters with real arguments in some expression
     *
     * @param realArgs The arguments to which the formal argumentas are mapped
     * @param e The expression in which the substitution will take place
     */
    def withParamSubst(realArgs: Seq[Expr], e: Expr) = {
      replaceFromIDs(paramSubst(realArgs), e)
    }

    def applied(realArgs: Seq[Expr]): FunctionInvocation = {
      FunctionInvocation(fd, tps, realArgs)
    }

    def applied: FunctionInvocation =
      applied(params map { _.toVariable })

    /** 
     *  Params will return ValDefs instantiated with the correct types
     *  For such a ValDef(id,tp) it may hold that (id.getType != tp)  
     */
    lazy val (params: Seq[ValDef], paramsMap: Map[Identifier, Identifier]) = {
      if (typesMap.isEmpty) {
        (fd.params, Map())
      } else {
        val newParams = fd.params.map { vd =>
          val newTpe = translated(vd.getType)
          val newId = FreshIdentifier(vd.id.name, newTpe, true).copiedFrom(vd.id)
          vd.copy(id = newId).setPos(vd)
        }

        val paramsMap: Map[Identifier, Identifier] = (fd.params zip newParams).map { case (vd1, vd2) => vd1.id -> vd2.id }.toMap

        (newParams, paramsMap)
      }
    }

    lazy val functionType = FunctionType(params.map(_.getType).toList, returnType)

    lazy val returnType: Type = translated(fd.returnType)

    lazy val paramIds = params map { _.id }

    lazy val fullBody      = translated(fd.fullBody)
    lazy val body          = fd.body map translated
    lazy val precondition  = fd.precondition map translated
    lazy val precOrTrue    = translated(fd.precOrTrue)
    lazy val postcondition = fd.postcondition map translated
    lazy val postOrTrue    = translated(fd.postOrTrue)

    def hasImplementation = body.isDefined
    def hasBody           = hasImplementation
    def hasPrecondition   = precondition.isDefined
    def hasPostcondition  = postcondition.isDefined
  }
}
