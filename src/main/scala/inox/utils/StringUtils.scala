/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package utils

import org.apache.commons.lang3.StringEscapeUtils

object StringUtils {
  def toHex(i: Int): String = {
    if (0 <= i && i <= 9) i.toString else (i + 55).toChar.toString
  }

  def fromHex(c: Char): Int = {
    if (c >= 'A' && c <= 'F') (c - 55).toInt
    else if (c >= 'a' && c <= 'f') (c - 87).toInt
    else c.toString.toInt
  }

  def encodeByte(b: Byte): String = "\\x" + toHex((b >> 4) & 0xF) + toHex(b & 0xF)
  def decodeHex(s: String): Byte = ((fromHex(s.charAt(0)) << 4) + fromHex(s.charAt(1))).toByte

  private val hex = """^\\x[0-9A-Fa-f]{2}""".r
  private val uhex1 = """(?s)^\\u\{([0-9A-Fa-f])\}(.*)""".r
  private val uhex2 = """(?s)^\\u\{([0-9A-Fa-f]{2})\}(.*)""".r

  object Hex {
    def unapply(s: String): Option[(Byte, String)] = {
      if (hex.findFirstIn(s).isDefined) {
        val (head, s2) = s.splitAt(4)
        Some((decodeHex(head.drop(2)), s2))
      } else {
        None
      }
    }
  }

  object JavaEncoded {
    def unapply(s: String): Option[(Byte, String)] = Hex.unapply(s).orElse {
      if (s.charAt(0) == '\\') {
        val Seq(b) = StringEscapeUtils.unescapeJava(s.take(2)).getBytes.toSeq
        Some((b, s.drop(2)))
      } else {
        None
      }
    }
  }

  def decode(s: String): String = if (s.isEmpty) s else (s match {
    case uhex1(head, s2) => (fromHex(head.charAt(0)) & 0xF).toChar + decode(s2)
    case uhex2(head, s2) => (decodeHex(head) & 0xFF).toChar + decode(s2)
    case JavaEncoded(b, s2) => (b & 0xFF).toChar + decode(s2)
    case _ => s.head + decode(s.tail)
  })
}
