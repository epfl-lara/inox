/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package utils

import java.io.{OutputStream, InputStream}
import java.nio.charset.StandardCharsets

import scala.reflect._

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

  given identIsSerializable: Serializable[Identifier] = new Serializable[Identifier]

  given tuple2IsSerializable[T1: Serializable, T2: Serializable]: Serializable[(T1, T2)] =
    new Serializable[(T1, T2)]
  given tuple3IsSerializable[T1: Serializable, T2: Serializable, T3: Serializable]: Serializable[(T1, T2, T3)] =
    new Serializable[(T1, T2, T3)]
  given tuple4IsSerializable[T1: Serializable, T2: Serializable, T3: Serializable, T4: Serializable]: Serializable[(T1, T2, T3, T4)] =
    new Serializable[(T1, T2, T3, T4)]

  given optionIsSerializable[T: Serializable]: Serializable[Option[T]] = new Serializable[Option[T]]
  given seqIsSerializable[T: Serializable]: Serializable[Seq[T]] = new Serializable[Seq[T]]
  given setIsSerializable[T: Serializable]: Serializable[Set[T]] = new Serializable[Set[T]]
  given mapIsSerializable[T1: Serializable, T2: Serializable]: Serializable[Map[T1, T2]] = new Serializable[Map[T1, T2]]

  given resultIsSerializable: Serializable[SerializationResult] = new Serializable[SerializationResult]

  given boolIsSerializable: Serializable[Boolean] = new Serializable[Boolean]
  given charIsSerializable: Serializable[Char] = new Serializable[Char]
  given byteIsSerializable: Serializable[Byte] = new Serializable[Byte]
  given shortIsSerializable: Serializable[Short] = new Serializable[Short]
  given intIsSerializable: Serializable[Int] = new Serializable[Int]
  given longIsSerializable: Serializable[Long] = new Serializable[Long]
  given floatIsSerializable: Serializable[Float] = new Serializable[Float]
  given doubleIsSerializable: Serializable[Double] = new Serializable[Double]
  given stringIsSerializable: Serializable[String] = new Serializable[String]
  given bigIntIsSerializable: Serializable[BigInt] = new Serializable[BigInt]

  given treeIsSerializable: Serializable[Tree] = new Serializable[Tree]

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

  // Reduce priority of SerializationProcedure
  object SerializationProcedure {

    /** Everything that is serializable implies the existence of a corresponding serialization
      * procedure that simply calls the serializer. */
    given serializableProcedure[T: Serializable]: SerializationProcedure[T] = new SerializationProcedure[T] {
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

    given tuple2Procedure[T1, T2](
      using p1: SerializationProcedure[T1], p2: SerializationProcedure[T2]): SerializationProcedure[(T1, T2)] =
        mappingProcedure((p: (T1, T2)) => (p1.serialize(p._1), p2.serialize(p._2)))(
          p => (p1.deserialize(p._1), p2.deserialize(p._2)))

    given tuple3Procedure[T1, T2, T3](
      using p1: SerializationProcedure[T1], p2: SerializationProcedure[T2], p3: SerializationProcedure[T3]): SerializationProcedure[(T1, T2, T3)] =
        mappingProcedure((p: (T1, T2, T3)) => (p1.serialize(p._1), p2.serialize(p._2), p3.serialize(p._3)))(
          p => (p1.deserialize(p._1), p2.deserialize(p._2), p3.deserialize(p._3)))

    given tuple4Procedure[T1, T2, T3, T4](
      using p1: SerializationProcedure[T1], p2: SerializationProcedure[T2], p3: SerializationProcedure[T3], p4: SerializationProcedure[T4]): SerializationProcedure[(T1, T2, T3, T4)] =
        mappingProcedure((p: (T1, T2, T3, T4)) => (p1.serialize(p._1), p2.serialize(p._2), p3.serialize(p._3), p4.serialize(p._4)))(
          p => (p1.deserialize(p._1), p2.deserialize(p._2), p3.deserialize(p._3), p4.deserialize(p._4)))

    given seqProcedure[T](using p: SerializationProcedure[T]): SerializationProcedure[Seq[T]] =
      mappingProcedure((seq: Seq[T]) => seq.map(p.serialize))(seq => seq.map(p.deserialize))

    given setProcedure[T](using p: SerializationProcedure[T]): SerializationProcedure[Set[T]] =
      mappingProcedure((set: Set[T]) => set.map(p.serialize))(set => set.map(p.deserialize))

    given mapProcedure[T1, T2](using p1: SerializationProcedure[T1], p2: SerializationProcedure[T2]): SerializationProcedure[Map[T1, T2]] =
      mappingProcedure((map: Map[T1, T2]) => map.map(p => p1.serialize(p._1) -> p2.serialize(p._2)))(
        map => map.map(p => p1.deserialize(p._1) -> p2.deserialize(p._2)))

    given symbolsProcedure: SerializationProcedure[Symbols] = mappingProcedure(
      (s: Symbols) => (s.functions.values.toSeq.sortBy(_.id), s.sorts.values.toSeq.sortBy(_.id)))(
        p => NoSymbols.withFunctions(p._1).withSorts(p._2))
  }


  // Using the companion object here makes the `fromProcedure` given have lower priority
  object SerializableOrProcedure {
    given fromProcedure[T](using ev: SerializationProcedure[T]): SerializableOrProcedure[T] = SerializableOrProcedure(Right(ev))
  }
  given fromSerializable[T](using ev: Serializable[T]): SerializableOrProcedure[T] = SerializableOrProcedure(Left(ev))
  case class SerializableOrProcedure[T](e: Either[Serializable[T], SerializationProcedure[T]])


  final def serialize[T](e: T)(using p: SerializationProcedure[T]): SerializationResult = p.serialize(e)
  final def deserialize[T](result: SerializationResult)(using p: SerializationProcedure[T]): T = p.deserialize(result)

  final def serialize[T](e: T, out: OutputStream)(using p: SerializableOrProcedure[T]): Unit = p.e match {
    case Left(_) => writeObject(e, out)
    case Right(p) => writeObject(p.serialize(e), out)
  }

  final def deserialize[T](in: InputStream)(using p: SerializableOrProcedure[T]): T = p.e match {
    case Left(_) => readObject(in).asInstanceOf[T]
    case Right(p) => p.deserialize(readObject(in).asInstanceOf[SerializationResult])
  }
}

/** Serialization utilities for Inox trees */
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

  abstract class Serializer[T](val id: Int) {
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

  private inline def classSerializer[T: ClassTag](inline id: Int): (Class[?], Serializer[T]) =
    classTag[T].runtimeClass -> inoxClassSerializerMacro[T](this, id).asInstanceOf[Serializer[T]]

  protected class MappingSerializer[T, U](id: Int, f: T => U, fInv: U => T) extends Serializer[T](id) {
    override protected def write(element: T, out: OutputStream): Unit = writeObject(f(element), out)
    override protected def read(in: InputStream): T = fInv(readObject(in).asInstanceOf[U])
  }

  protected class MappingSerializerConstructor[T](id: Int) {
    def apply[U](f: T => U)(fInv: U => T)(using ev: ClassTag[T]): (Class[?], MappingSerializer[T, U]) =
      classTag[T].runtimeClass -> new MappingSerializer[T,U](id, f, fInv)
  }

  protected final def mappingSerializer[T](id: Int): MappingSerializerConstructor[T] = {
    new MappingSerializerConstructor[T](id)
  }

  // Products are marked with id=0
  protected object ProductSerializer extends Serializer[Product](0) {
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
      val constructors = runtimeClass.getConstructors()
      if (constructors.size != 1) throw SerializationError(className, "Cannot identify constructor")
      constructors(0).newInstance(trees +: fieldObjs.map(_.asInstanceOf[AnyRef])*).asInstanceOf[Product]
    }
  }

  // Option is marked with id=1
  protected object OptionSerializer extends Serializer[Option[?]](1) {
    override protected def write(element: Option[?], out: OutputStream): Unit = {
      out.write(if (element.isDefined) 1 else 0)
      if (element.isDefined) writeObject(element.get, out)
    }
    override protected def read(in: InputStream): Option[?] = {
      val defined = in.read()
      if (defined == 1) Some(readObject(in))
      else if (defined == 0) None
      else throw DeserializationError(defined.toByte, "Option must be defined(=1) or not(=0)")
    }
  }

  // Seq is marked with id=2
  protected object SeqSerializer extends Serializer[Seq[?]](2) {
    override protected def write(element: Seq[?], out: OutputStream): Unit = {
      writeSmallish(element.size, out)
      for (e <- element) writeObject(e, out)
    }
    override protected def read(in: InputStream): Seq[?] = {
      val size = readSmallish(in)
      (for (i <- 0 until size) yield readObject(in)).toSeq
    }
  }


  protected object LexicographicOrder extends scala.math.Ordering[Array[Byte]] {
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
  given LexicographicOrder.type = LexicographicOrder

  protected final def serializeToBytes(element: Any): Array[Byte] = {
    val bytes = new java.io.ByteArrayOutputStream
    writeObject(element, bytes)
    bytes.toByteArray
  }

  // Set is marked with id=3
  protected object SetSerializer extends Serializer[Set[?]](3) {
    override protected def write(element: Set[?], out: OutputStream): Unit = {
      writeSmallish(element.size, out)
      element.toSeq.map(serializeToBytes).sorted.foreach(out.write(_))
    }
    override protected def read(in: InputStream): Set[?] = {
      val size = readSmallish(in)
      (for (i <- 0 until size) yield readObject(in)).toSet
    }
  }

  // Map is marked with id=4
  protected object MapSerializer extends Serializer[Map[?, ?]](4) {
    override protected def write(element: Map[?, ?], out: OutputStream): Unit = {
      writeSmallish(element.size, out)
      for ((k, v) <- element.toSeq.map { case (k, v) => serializeToBytes(k) -> v }.sortBy(_._1)) {
        out.write(k)
        writeObject(v, out)
      }
    }
    override protected def read(in: InputStream): Map[?, ?] = {
      val size = readSmallish(in)
      (for (i <- 0 until size) yield (readObject(in), readObject(in))).toMap
    }
  }

  // Basic Java types that are serialized primitively are prefixed with id=5
  protected object PrimitiveSerializer extends Serializer[AnyRef](5) {
    override protected def write(element: AnyRef, out: OutputStream): Unit = {
      val objOut = new java.io.DataOutputStream(out)
      def writeBytes(id: Byte, bytes: Array[Byte]): Unit = {
        objOut.writeByte(id)
        objOut.writeInt(bytes.length)
        objOut.write(bytes)
      }

      element match {
        case v: java.lang.Boolean   => objOut.writeByte(0); objOut.writeBoolean(v)
        case v: java.lang.Character => objOut.writeByte(1); objOut.writeChar(v.toChar)
        case v: java.lang.Byte      => objOut.writeByte(2); objOut.writeByte(v.toByte)
        case v: java.lang.Short     => objOut.writeByte(3); objOut.writeShort(v.toShort)
        case v: java.lang.Integer   => objOut.writeByte(4); objOut.writeInt(v)
        case v: java.lang.Long      => objOut.writeByte(5); objOut.writeLong(v)
        case v: java.lang.Float     => objOut.writeByte(6); objOut.writeFloat(v)
        case v: java.lang.Double    => objOut.writeByte(7); objOut.writeDouble(v)
        case v: java.lang.String    => writeBytes(8, v.getBytes(StandardCharsets.UTF_8))
        case v: BigInt              => writeBytes(9, v.toByteArray)
      }
      objOut.flush()
    }
    override protected def read(in: InputStream): AnyRef = {
      val objIn = new java.io.DataInputStream(in)
      def readBytes(): Array[Byte] = {
        val length = objIn.readInt()
        val bytes = new Array[Byte](length)
        (0 until length).foreach { i => bytes(i) = objIn.readByte() }
        bytes
      }

      objIn.readByte() match {
        case 0 => objIn.readBoolean(): java.lang.Boolean
        case 1 => objIn.readChar(): java.lang.Character
        case 2 => objIn.readByte(): java.lang.Byte
        case 3 => objIn.readShort(): java.lang.Short
        case 4 => objIn.readInt(): java.lang.Integer
        case 5 => objIn.readLong(): java.lang.Long
        case 6 => objIn.readFloat(): java.lang.Float
        case 7 => objIn.readDouble(): java.lang.Double
        case 8 => new String(readBytes(), StandardCharsets.UTF_8)
        case 9 => BigInt(readBytes())
      }
    }
  }

  private final val primitiveClasses: Set[Class[?]] = Set(
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
  protected object TupleSerializer extends Serializer[Product](6) {
    override protected def write(element: Product, out: OutputStream): Unit = {
      out.write(element.productArity)
      for (e <- element.productIterator) writeObject(e, out)
    }
    override protected def read(in: InputStream): Product = {
      val size = in.read()
      val fields = for (i <- 0 until size) yield readObject(in).asInstanceOf[AnyRef]
      tupleSizeToClass(size).getConstructors()(0).newInstance(fields*).asInstanceOf[Product]
    }
  }

  private final val tupleSizeToClass: Map[Int, Class[?]] =
    (2 to 22).map(i => i -> Class.forName(s"scala.Tuple$i")).toMap

  private final val tupleClasses: Set[Class[?]] = tupleSizeToClass.values.toSet


  // SerializationResult id=7
  protected object ResultSerializer extends Serializer[SerializationResult](7) {
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

  override def writeObject(obj: Any, out: OutputStream): Unit = {
    val runtimeClass = obj.getClass
    classToSerializer.get(runtimeClass)
      .collect { case (s: Serializer[t]) => s(obj.asInstanceOf[t], out) }
      .orElse(if (primitiveClasses(runtimeClass)) Some(PrimitiveSerializer(obj.asInstanceOf[AnyRef], out)) else None)
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

  override def readObject(in: InputStream): Any = {
    readId(in) match {
      case -1 => throw new java.io.EOFException()
      case ProductSerializer.id => ProductSerializer.deserialize(in)
      case OptionSerializer.id => OptionSerializer.deserialize(in)
      case SeqSerializer.id => SeqSerializer.deserialize(in)
      case SetSerializer.id => SetSerializer.deserialize(in)
      case MapSerializer.id => MapSerializer.deserialize(in)
      case PrimitiveSerializer.id => PrimitiveSerializer.deserialize(in)
      case TupleSerializer.id => TupleSerializer.deserialize(in)
      case ResultSerializer.id => ResultSerializer.deserialize(in)
      case i => idToSerializer.get(i).map(_.deserialize(in)).getOrElse(
        throw DeserializationError(i.toByte, "No class serializer found for given id"))
    }
  }

  private val classToSerializer: Map[Class[?], Serializer[?]] = classSerializers
  private val idToSerializer: Map[Int, Serializer[?]] =
    classToSerializer.values.filter(_.id >= 10).map(s => s.id -> (s: Serializer[?])).toMap

  /** A mapping from `Class[_]` to `Serializer[_]` for classes that commonly
    * occur within Stainless programs.
    *
    * The `Serializer[_]` identifiers in this mapping range from 10 to 105
    * (ignoring special identifiers that are smaller than 10).
    *
    * NEXT ID: 106
    */
  protected def classSerializers: Map[Class[?], Serializer[?]] = Map(
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
