/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package utils

import java.io.{OutputStream, InputStream}

import scala.reflect._
import scala.reflect.runtime._
import scala.reflect.runtime.universe._

import scala.annotation.switch

case class SerializationError(obj: Any, msg: String) extends Exception(s"Failed to serialize $obj[${obj.getClass}]: $msg")
case class DeserializationError(byte: Byte, msg: String) extends Exception(s"Failed to deserialize [$byte,...]: $msg")

/** A generic serialization/deserialization API for Inox ASTs. */
trait Serializer { self =>
  val trees: ast.Trees
  import trees._


  /* -- Serializable/Deserializable Type Class --
   *
   * In order to provide type-safe serialization/deserialization for the set of types for
   * which serialization is supported, we use a type classes [[Serializable]].
   */

  /** Type class that marks a type as serializable. */
  class Serializable[-T]

  implicit def identIsSerializable = new Serializable[Identifier]

  implicit def tuple2IsSerializable[T1: Serializable, T2: Serializable] = new Serializable[(T1, T2)]
  implicit def tuple3IsSerializable[T1: Serializable, T2: Serializable, T3: Serializable] = new Serializable[(T1, T2, T3)]
  implicit def tuple4IsSerializable[T1: Serializable, T2: Serializable, T3: Serializable, T4: Serializable] = new Serializable[(T1, T2, T3, T4)]

  implicit def seqIsSerializable[T: Serializable] = new Serializable[Seq[T]]
  implicit def setIsSerializable[T: Serializable] = new Serializable[Set[T]]
  implicit def mapIsSerializable[T1: Serializable, T2: Serializable] = new Serializable[Map[T1, T2]]

  implicit def resultIsSerializable = new Serializable[SerializationResult]

  implicit object boolIsSerializable   extends Serializable[Boolean]
  implicit object charIsSerializable   extends Serializable[Char]
  implicit object byteIsSerializable   extends Serializable[Byte]
  implicit object shortIsSerializable  extends Serializable[Short]
  implicit object intIsSerializable    extends Serializable[Int]
  implicit object longIsSerializable   extends Serializable[Long]
  implicit object floatIsSerializable  extends Serializable[Float]
  implicit object doubleIsSerializable extends Serializable[Double]
  implicit object stringIsSerializable extends Serializable[String]
  implicit object bigIntIsSerializable extends Serializable[BigInt]

  // This has to be the last implicit for some reason, otherwise implicit expansion diverges
  // for `Serializable[Expr]` when using Scala 2.12
  implicit def treeIsSerializable = new Serializable[Tree]

  protected def writeObject(obj: Any, out: OutputStream): Unit
  protected def readObject(in: InputStream): Any


  class SerializationResult private[utils](val bytes: Array[Byte]) {
    override def equals(that: Any): Boolean = that match {
      case s: SerializationResult => java.util.Arrays.equals(bytes, s.bytes)
      case _ => false
    }

    override val hashCode: Int = java.util.Arrays.hashCode(bytes)
  }


  /* -- Serialization/Deserialization Procedures --
   *
   * An unfortunate limitation of the above type class is that it cannot handle serialization
   * through a mapping into a serializable type.
   *
   * For example, we would like to provide a serialization procedure for [[Definitions.Symbols]]
   * by mapping into {{{(Seq[FunDef], Seq[ADTSort])}}} (which is serializable). However, this
   * must of course be done **before** entering the serializer.
   *
   * To enable this feature, we provide the [[SerializationProcedure]] interface that can be
   * used to define serialization through mappings into serializable types.
   */

  /** Base trait that enables serialization of some type `T` into `SerializationResult`. */
  sealed trait SerializationProcedure[-T] {
    def serialize(e: T): SerializationResult
    def deserialize(in: SerializationResult): T @scala.annotation.unchecked.uncheckedVariance
  }

  // Reduce priority of SerializationProcedure implicits (for Scala 2.12)
  object SerializationProcedure {

    /** Everything that is serializable implies the existence of a corresponding serialization
      * procedure that simply calls the serializer. */
    implicit def serializableProcedure[T: Serializable] = new SerializationProcedure[T] {
      def serialize(e: T): SerializationResult = {
        val out = new java.io.ByteArrayOutputStream
        writeObject(e, out)
        new SerializationResult(out.toByteArray)
      }
      def deserialize(in: SerializationResult): T = {
        readObject(new java.io.ByteArrayInputStream(in.bytes)).asInstanceOf[T]
      }
    }

    protected def mappingProcedure[T1, T2: Serializable](f1: T1 => T2)(f2: T2 => T1) = new SerializationProcedure[T1] {
      override def serialize(e: T1): SerializationResult = {
        val out = new java.io.ByteArrayOutputStream
        writeObject(f1(e), out)
        new SerializationResult(out.toByteArray)
      }
      override def deserialize(in: SerializationResult): T1 = {
        f2(readObject(new java.io.ByteArrayInputStream(in.bytes)).asInstanceOf[T2])
      }
    }

    implicit def tuple2Procedure[T1, T2](
      implicit p1: SerializationProcedure[T1], p2: SerializationProcedure[T2]) =
        mappingProcedure((p: (T1, T2)) => (p1.serialize(p._1), p2.serialize(p._2)))(
          p => (p1.deserialize(p._1), p2.deserialize(p._2)))

    implicit def tuple3Procedure[T1, T2, T3](
      implicit p1: SerializationProcedure[T1], p2: SerializationProcedure[T2], p3: SerializationProcedure[T3]) =
        mappingProcedure((p: (T1, T2, T3)) => (p1.serialize(p._1), p2.serialize(p._2), p3.serialize(p._3)))(
          p => (p1.deserialize(p._1), p2.deserialize(p._2), p3.deserialize(p._3)))

    implicit def tuple4Procedure[T1, T2, T3, T4](
      implicit p1: SerializationProcedure[T1], p2: SerializationProcedure[T2], p3: SerializationProcedure[T3], p4: SerializationProcedure[T4]) =
        mappingProcedure((p: (T1, T2, T3, T4)) => (p1.serialize(p._1), p2.serialize(p._2), p3.serialize(p._3), p4.serialize(p._4)))(
          p => (p1.deserialize(p._1), p2.deserialize(p._2), p3.deserialize(p._3), p4.deserialize(p._4)))

    implicit def seqProcedure[T](implicit p: SerializationProcedure[T]) =
      mappingProcedure((seq: Seq[T]) => seq.map(p.serialize))(seq => seq.map(p.deserialize))

    implicit def setProcedure[T](implicit p: SerializationProcedure[T]) =
      mappingProcedure((set: Set[T]) => set.map(p.serialize))(set => set.map(p.deserialize))

    implicit def mapProcedure[T1, T2](implicit p1: SerializationProcedure[T1], p2: SerializationProcedure[T2]) =
      mappingProcedure((map: Map[T1, T2]) => map.map(p => p1.serialize(p._1) -> p2.serialize(p._2)))(
        map => map.map(p => p1.deserialize(p._1) -> p2.deserialize(p._2)))

    implicit def symbolsProcedure: SerializationProcedure[Symbols] = mappingProcedure(
      (s: Symbols) => (s.functions.values.toSeq.sortBy(_.id), s.sorts.values.toSeq.sortBy(_.id)))(
        p => NoSymbols.withFunctions(p._1).withSorts(p._2))
  }


  // Using the companion object here makes the `fromProcedure` implicit have lower priority
  object SerializableOrProcedure {
    implicit def fromProcedure[T](implicit ev: SerializationProcedure[T]) = SerializableOrProcedure(Right(ev))
  }
  implicit def fromSerializable[T](implicit ev: Serializable[T]) = SerializableOrProcedure(Left(ev))
  case class SerializableOrProcedure[T](e: Either[Serializable[T], SerializationProcedure[T]])


  final def serialize[T](e: T)(implicit p: SerializationProcedure[T]): SerializationResult = p.serialize(e)
  final def deserialize[T](result: SerializationResult)(implicit p: SerializationProcedure[T]): T = p.deserialize(result)

  final def serialize[T](e: T, out: OutputStream)(implicit p: SerializableOrProcedure[T]): Unit = p.e match {
    case Left(_) => writeObject(e, out)
    case Right(p) => writeObject(p.serialize(e), out)
  }

  final def deserialize[T](in: InputStream)(implicit p: SerializableOrProcedure[T]): T = p.e match {
    case Left(_) => readObject(in).asInstanceOf[T]
    case Right(p) => p.deserialize(readObject(in).asInstanceOf[SerializationResult])
  }
}

/** Serialization utilities for Inox trees
  *
  * NOTE the serializer mostly uses runtime information to serialize classes and their fields
  *      even though much of this information is known at compile time.
  *      Changing this behavior could be a useful extension.
  */
class InoxSerializer(val trees: ast.Trees, serializeProducts: Boolean = false) extends Serializer { self =>
  import trees._

  private def writeId(id: Int, out: OutputStream): Unit = {
    // We optimize here for small ids, which corresponds to few registered serializers.
    // We assume this number shouldn't be larger than 255 anyway.
    var currId = id
    while (currId >= 255) {
      out.write(255.toByte)
      currId -= 255
    }
    out.write(currId)
  }

  private def readId(in: InputStream): Int = {
    val read = in.read()
    if (read == 255) 255 + readId(in)
    else read
  }

  // A serializer for small-ish integers that should rearely go over 255
  // but shouldn't take huge amounts of space if they do (unlike in the `writeId` case).
  private def writeSmallish(i: Int, out: OutputStream): Unit = {
    if (i >= 0 && i < 255) {
      out.write(i)
    } else {
      out.write(255)
      writeObject(i, out)
    }
  }

  private def readSmallish(in: InputStream): Int = {
    val i = in.read()
    if (i < 255) i else readObject(in).asInstanceOf[Int]
  }

  protected abstract class Serializer[T](val id: Int) {
    final def apply(element: T, out: OutputStream): Unit = serialize(element, out)

    /** Writes the provided input element into the `out` byte stream. */
    final def serialize(element: T, out: OutputStream): Unit = {
      writeId(id, out)
      write(element, out)
    }

    /** Reads an instance of `T` from the `in` byte stream.
      * Note that one should not try to consume the `id` bytes here as they have already
      * been consumed in order to dispatch into this serializer! */
    final def deserialize(in: InputStream): T = read(in)

    protected def write(element: T, out: OutputStream): Unit
    protected def read(in: InputStream): T
  }

  protected class ClassSerializer[T: ClassTag](id: Int) extends Serializer[T](id) {
    private val tag = classTag[T]
    private val runtimeClass = tag.runtimeClass
    private val rootMirror = scala.reflect.runtime.universe.runtimeMirror(runtimeClass.getClassLoader)
    private val classSymbol = rootMirror.classSymbol(runtimeClass)

    if (
      !classSymbol.isStatic &&
      !(classSymbol.owner.isClass && classSymbol.owner.asClass.selfType <:< typeOf[ast.Trees])
    ) throw SerializationError(runtimeClass, "Unexpected inner type")

    private val constructorSymbol = classSymbol.toType.members
      .filter(_.isMethod).map(_.asMethod).filter(m => m.isConstructor && m.isPrimaryConstructor)
      .iterator.next

    private val fields = {
      val paramNames = constructorSymbol.paramLists.flatten.map(_.name)
      classSymbol.toType.decls
        .filter(d => d.isTerm && d.isPublic && !d.isSynthetic)
        .map(_.asTerm)
        .filter(_.isStable)
        .filter(s => paramNames contains s.name)
    }

    override protected def write(element: T, out: OutputStream): Unit = {
      val elementMirror = rootMirror.reflect(element)
      for (fd <- fields) {
        val fieldValue = try {
          elementMirror.reflectField(fd).get
        } catch {
          // Scala case class constructor arguments that are super-class field overrides are not
          // represented as Java fields, so we invoke their getter instead to get their value
          case _: ScalaReflectionException => elementMirror.reflectMethod(fd.asMethod)()
        }
        writeObject(fieldValue, out)
      }
    }

    private val instantiator: Seq[Any] => Any = {
      if (classSymbol.isStatic) {
        val constructor = currentMirror.reflectClass(classSymbol).reflectConstructor(
          classSymbol.toType.members
            .filter(_.isMethod).map(_.asMethod).filter(m => m.isConstructor && m.isPrimaryConstructor)
            .iterator.next)
        (fieldObjs: Seq[Any]) => constructor(fieldObjs: _*)
      } else {
        // XXX @nv: Scala has a bug with nested class constructors (https://github.com/scala/bug/issues/9528)
        //          so we use the more crude Java reflection instead.
        val constructors = runtimeClass.getConstructors()
        if (constructors.size != 1) throw SerializationError(classSymbol, "Cannot identify constructor")
        (fieldObjs: Seq[Any]) => constructors(0).newInstance(trees +: fieldObjs.map(_.asInstanceOf[AnyRef]) : _*)
      }
    }

    override protected def read(in: InputStream): T = {
      val fieldObjs = for (fd <- fields.toSeq) yield readObject(in)
      instantiator(fieldObjs).asInstanceOf[T]
    }
  }

  protected final def classSerializer[T: ClassTag](id: Int): (Class[_], ClassSerializer[T]) = {
    classTag[T].runtimeClass -> new ClassSerializer[T](id)
  }


  protected class MappingSerializer[T, U](id: Int, f: T => U, fInv: U => T) extends Serializer[T](id) {
    override protected def write(element: T, out: OutputStream): Unit = writeObject(f(element), out)
    override protected def read(in: InputStream): T = fInv(readObject(in).asInstanceOf[U])
  }

  protected class MappingSerializerConstructor[T](id: Int) {
    def apply[U](f: T => U)(fInv: U => T)(implicit ev: ClassTag[T]): (Class[_], MappingSerializer[T, U]) =
      classTag[T].runtimeClass -> new MappingSerializer[T,U](id, f, fInv)
  }

  protected final def mappingSerializer[T](id: Int): MappingSerializerConstructor[T] = {
    new MappingSerializerConstructor[T](id)
  }

  // Products are marked with id=0
  protected final object ProductSerializer extends Serializer[Product](0) {
    override protected def write(element: Product, out: OutputStream): Unit = {
      writeObject(element.getClass.getName, out)
      out.write(element.productArity)
      for (e <- element.productIterator) writeObject(e, out)
    }
    override protected def read(in: InputStream): Product = {
      val className = readObject(in).asInstanceOf[String]
      val size = in.read()
      val fieldObjs = for (i <- 0 until size) yield readObject(in).asInstanceOf[AnyRef]

      val runtimeClass = Class.forName(className)
      val classSymbol = currentMirror.classSymbol(runtimeClass)

      if (classSymbol.isStatic) {
        currentMirror.reflectClass(classSymbol).reflectConstructor(
          classSymbol.toType.members
            .filter(_.isMethod).map(_.asMethod).filter(m => m.isConstructor && m.isPrimaryConstructor)
            .iterator.next
        )(fieldObjs: _*).asInstanceOf[Product]
      } else {
        if (!classSymbol.owner.isType || !(classSymbol.owner.asClass.selfType <:< typeOf[ast.Trees]))
          throw SerializationError(classSymbol, "Unexpected inner class")
        // XXX @nv: Scala has a bug with nested class constructors (https://github.com/scala/bug/issues/9528)
        //          so we use the more crude Java reflection instead.
        val constructors = runtimeClass.getConstructors()
        if (constructors.size != 1) throw SerializationError(classSymbol, "Cannot identify constructor")
        constructors(0).newInstance(trees +: fieldObjs.map(_.asInstanceOf[AnyRef]) : _*).asInstanceOf[Product]
      }
    }
  }

  // Option is marked with id=1
  protected final object OptionSerializer extends Serializer[Option[_]](1) {
    override protected def write(element: Option[_], out: OutputStream): Unit = {
      out.write(if (element.isDefined) 1 else 0)
      if (element.isDefined) writeObject(element.get, out)
    }
    override protected def read(in: InputStream): Option[_] = {
      val defined = in.read()
      if (defined == 1) Some(readObject(in))
      else if (defined == 0) None
      else throw DeserializationError(defined.toByte, "Option must be defined(=1) or not(=0)")
    }
  }

  // Seq is marked with id=2
  protected final object SeqSerializer extends Serializer[Seq[_]](2) {
    override protected def write(element: Seq[_], out: OutputStream): Unit = {
      writeSmallish(element.size, out)
      for (e <- element) writeObject(e, out)
    }
    override protected def read(in: InputStream): Seq[_] = {
      val size = readSmallish(in)
      (for (i <- 0 until size) yield readObject(in)).toSeq
    }
  }


  protected implicit final object LexicographicOrder extends scala.math.Ordering[Array[Byte]] {
    override def compare(a1: Array[Byte], a2: Array[Byte]): Int = {
      def rec(i: Int): Int =
        if (i >= a1.size || i >= a2.size) {
          Ordering.Int.compare(a1.size, a2.size)
        } else {
          val cmp = Ordering.Byte.compare(a1(i), a2(i))
          if (cmp != 0) cmp else rec(i + 1)
        }
      rec(0)
    }
  }

  protected final def serializeToBytes(element: Any): Array[Byte] = {
    val bytes = new java.io.ByteArrayOutputStream
    writeObject(element, bytes)
    bytes.toByteArray
  }

  // Set is marked with id=3
  protected final object SetSerializer extends Serializer[Set[_]](3) {
    override protected def write(element: Set[_], out: OutputStream): Unit = {
      writeSmallish(element.size, out)
      element.toSeq.map(serializeToBytes).sorted.foreach(out.write(_))
    }
    override protected def read(in: InputStream): Set[_] = {
      val size = readSmallish(in)
      (for (i <- 0 until size) yield readObject(in)).toSet
    }
  }

  // Map is marked with id=4
  protected final object MapSerializer extends Serializer[Map[_, _]](4) {
    override protected def write(element: Map[_, _], out: OutputStream): Unit = {
      writeSmallish(element.size, out)
      for ((k, v) <- element.toSeq.map { case (k, v) => serializeToBytes(k) -> v }.sortBy(_._1)) {
        out.write(k)
        writeObject(v, out)
      }
    }
    override protected def read(in: InputStream): Map[_, _] = {
      val size = readSmallish(in)
      (for (i <- 0 until size) yield (readObject(in), readObject(in))).toMap
    }
  }

  // Types that are serialized with Java's serializer are prefixed with id=5
  protected final object JavaSerializer extends Serializer[AnyRef](5) {
    override protected def write(element: AnyRef, out: OutputStream): Unit =
      new java.io.ObjectOutputStream(out).writeObject(element)
    override protected def read(in: InputStream): AnyRef =
      new java.io.ObjectInputStream(in).readObject()
  }

  private final val javaClasses: Set[Class[_]] = Set(
    // Primitive types
    classOf[Boolean],
    classOf[Char],
    classOf[Byte],
    classOf[Short],
    classOf[Int],
    classOf[Long],
    classOf[Float],
    classOf[Double],

    classOf[String],
    classOf[BigInt],

    // Java boxed types
    classOf[java.lang.Boolean],
    classOf[java.lang.Character],
    classOf[java.lang.Byte],
    classOf[java.lang.Short],
    classOf[java.lang.Integer],
    classOf[java.lang.Long],
    classOf[java.lang.Float],
    classOf[java.lang.Double]
  )


  // Tuples id=6
  protected final object TupleSerializer extends Serializer[Product](6) {
    override protected def write(element: Product, out: OutputStream): Unit = {
      out.write(element.productArity)
      for (e <- element.productIterator) writeObject(e, out)
    }
    override protected def read(in: InputStream): Product = {
      val size = in.read()
      val fields = for (i <- 0 until size) yield readObject(in).asInstanceOf[AnyRef]
      tupleSizeToClass(size).getConstructors()(0).newInstance(fields: _*).asInstanceOf[Product]
    }
  }

  private final val tupleSizeToClass: Map[Int, Class[_]] =
    (2 to 22).map(i => i -> Class.forName(s"scala.Tuple$i")).toMap

  private final val tupleClasses: Set[Class[_]] = tupleSizeToClass.values.toSet


  // SerializationResult id=7
  protected final object ResultSerializer extends Serializer[SerializationResult](7) {
    override protected def write(element: SerializationResult, out: OutputStream): Unit = {
      writeObject(element.bytes.size, out)
      out.write(element.bytes)
    }
    override protected def read(in: InputStream): SerializationResult = {
      val size = readObject(in).asInstanceOf[Int]
      val bytes = new Array[Byte](size)

      var read = 0
      while (read < size) read += in.read(bytes, read, size - read)
      new SerializationResult(bytes)
    }
  }


  override protected def writeObject(obj: Any, out: OutputStream): Unit = {
    val runtimeClass = obj.getClass
    classToSerializer.get(runtimeClass)
      .collect { case (s: Serializer[t]) => s(obj.asInstanceOf[t], out) }
      .orElse(if (javaClasses(runtimeClass)) Some(JavaSerializer(obj.asInstanceOf[AnyRef], out)) else None)
      .orElse(if (tupleClasses(runtimeClass)) Some(TupleSerializer(obj.asInstanceOf[Product], out)) else None)
      .getOrElse(obj match {
        case (opt: Option[_]) => OptionSerializer(opt, out)
        case (seq: Seq[_]) => SeqSerializer(seq, out)
        case (set: Set[_]) => SetSerializer(set, out)
        case (map: Map[_, _]) => MapSerializer(map, out)
        case p: Product if serializeProducts => ProductSerializer(p, out)
        case _ => throw SerializationError(obj, "Unexpected input to serializer")
      })
  }

  override protected def readObject(in: InputStream): Any = {
    readId(in) match {
      case -1 => throw new java.io.EOFException()
      case ProductSerializer.id => ProductSerializer.deserialize(in)
      case OptionSerializer.id => OptionSerializer.deserialize(in)
      case SeqSerializer.id => SeqSerializer.deserialize(in)
      case SetSerializer.id => SetSerializer.deserialize(in)
      case MapSerializer.id => MapSerializer.deserialize(in)
      case JavaSerializer.id => JavaSerializer.deserialize(in)
      case TupleSerializer.id => TupleSerializer.deserialize(in)
      case ResultSerializer.id => ResultSerializer.deserialize(in)
      case i => idToSerializer.get(i).map(_.deserialize(in)).getOrElse(
        throw DeserializationError(i.toByte, "No class serializer found for given id"))
    }
  }

  private[this] val classToSerializer: Map[Class[_], Serializer[_]] = classSerializers
  private[this] val idToSerializer: Map[Int, Serializer[_]] =
    classToSerializer.values.filter(_.id >= 10).map(s => s.id -> (s: Serializer[_])).toMap

  /** A mapping from `Class[_]` to `Serializer[_]` for classes that commonly
    * occur within Stainless programs.
    *
    * The `Serializer[_]` identifiers in this mapping range from 10 to 105
    * (ignoring special identifiers that are smaller than 10).
    *
    * NEXT ID: 106
    */
  protected def classSerializers: Map[Class[_], Serializer[_]] = Map(
    // Inox Expressions
    classSerializer[Assume]            (10),
    classSerializer[Variable]          (11),
    classSerializer[Let]               (12),
    classSerializer[Application]       (13),
    classSerializer[Lambda]            (14),
    classSerializer[Forall]            (15),
    classSerializer[Choose]            (16),
    classSerializer[FunctionInvocation](17),
    classSerializer[IfExpr]            (18),
    classSerializer[CharLiteral]       (19),
    // BVLiteral id=20
    // Bitvector literals are treated specially to avoid having to serialize BitSets
    mappingSerializer[BVLiteral](20)(bv => (bv.signed, bv.toBigInt, bv.size))(p => BVLiteral(p._1, p._2, p._3)),
    classSerializer[IntegerLiteral]    (21),
    classSerializer[FractionLiteral]   (22),
    classSerializer[BooleanLiteral]    (23),
    classSerializer[StringLiteral]     (24),
    classSerializer[UnitLiteral]       (25),
    classSerializer[GenericValue]      (26),
    classSerializer[ADT]               (27),
    classSerializer[IsConstructor]     (28),
    classSerializer[ADTSelector]       (29),
    classSerializer[Equals]            (30),
    classSerializer[And]               (31),
    classSerializer[Or]                (32),
    classSerializer[Implies]           (99),
    classSerializer[Not]               (33),
    classSerializer[StringConcat]      (34),
    classSerializer[SubString]         (35),
    classSerializer[StringLength]      (36),
    classSerializer[Plus]              (37),
    classSerializer[Minus]             (38),
    classSerializer[UMinus]            (39),
    classSerializer[Times]             (40),
    classSerializer[Division]          (41),
    classSerializer[Remainder]         (42),
    classSerializer[Modulo]            (43),
    classSerializer[LessThan]          (44),
    classSerializer[GreaterThan]       (45),
    classSerializer[LessEquals]        (46),
    classSerializer[GreaterEquals]     (47),
    classSerializer[BVNot]             (48),
    classSerializer[BVAnd]             (49),
    classSerializer[BVOr]              (50),
    classSerializer[BVXor]             (51),
    classSerializer[BVShiftLeft]       (52),
    classSerializer[BVAShiftRight]     (53),
    classSerializer[BVLShiftRight]     (54),
    classSerializer[BVNarrowingCast]   (55),
    classSerializer[BVWideningCast]    (56),
    classSerializer[Tuple]             (57),
    classSerializer[TupleSelect]       (58),
    classSerializer[FiniteSet]         (59),
    classSerializer[SetAdd]            (60),
    classSerializer[ElementOfSet]      (61),
    classSerializer[SubsetOf]          (62),
    classSerializer[SetIntersection]   (63),
    classSerializer[SetUnion]          (64),
    classSerializer[SetDifference]     (65),
    classSerializer[FiniteBag]         (66),
    classSerializer[BagAdd]            (67),
    classSerializer[MultiplicityInBag] (68),
    classSerializer[BagIntersection]   (69),
    classSerializer[BagUnion]          (70),
    classSerializer[BagDifference]     (71),
    classSerializer[FiniteMap]         (72),
    classSerializer[MapApply]          (73),
    classSerializer[MapUpdated]        (74),
    classSerializer[BVUnsignedToSigned](104),
    classSerializer[BVSignedToUnsigned](105),

    // Inox Types
    classSerializer[Untyped.type] (75),
    classSerializer[BooleanType]  (76),
    classSerializer[UnitType]     (77),
    classSerializer[CharType]     (78),
    classSerializer[IntegerType]  (79),
    classSerializer[RealType]     (80),
    classSerializer[StringType]   (81),
    classSerializer[BVType]       (82),
    classSerializer[TypeParameter](83),
    classSerializer[TupleType]    (84),
    classSerializer[SetType]      (85),
    classSerializer[BagType]      (86),
    classSerializer[MapType]      (87),
    classSerializer[FunctionType] (88),
    classSerializer[ADTType]      (89),

    classSerializer[RefinementType](100),
    classSerializer[PiType]        (101),
    classSerializer[SigmaType]     (102),

    // Identifier
    mappingSerializer[Identifier](90)
      (id => (id.name, id.globalId, id.id))
      (p => new Identifier(p._1, p._2, p._3)),

    // Inox Flags
    classSerializer[HasADTInvariant](91),
    classSerializer[HasADTEquality] (92),
    classSerializer[Annotation]     (93),

    // Inox Definitions
    mappingSerializer[ValDef](94)(_.toVariable)(_.toVal),
    mappingSerializer[TypeParameterDef](95)(_.tp)(TypeParameterDef(_)),
    classSerializer[ADTSort]       (96),
    classSerializer[ADTConstructor](97),
    classSerializer[FunDef]        (98),
    classSerializer[MapMerge]      (103),

    classOf[SerializationResult] -> ResultSerializer
  )
}

object Serializer {
  def apply(t: ast.Trees, serializeProducts: Boolean = false): Serializer { val trees: t.type } =
    new InoxSerializer(t).asInstanceOf[Serializer { val trees: t.type }]
}
