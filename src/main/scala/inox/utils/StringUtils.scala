/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package utils

object StringUtils {
  def toHex(i: Int): String = {
    if (0 <= i && i <= 9) i.toString else (i + 55).toChar.toString
  }

  def fromHex(c: Char): Int = {
    if (c >= 'A' && c <= 'F') (c - 55).toInt
    else if (c >= 'a' && c <= 'f') (c - 87).toInt
    else c.toString.toInt
  }

  private def isHex(c: Char): Boolean =
    ('0' <= c && c <= '9') || ('a' <= c && c <= 'f') || ('A' <= c && c <= 'F')

  /** Escapes a string so that it can be used as an SMT-LIB 2.6 string literal.
    *
    * Each (UTF-16) character is mapped to a single SMT-LIB character: printable ASCII
    * characters are kept as-is (apart from the backslash which could otherwise start an
    * escape sequence) and all other characters are written as `\u{...}` escapes.
    * Note that double quotes are escaped by the SMT-LIB printer.
    */
  def encode(s: String): String = {
    val sb = new StringBuilder
    for (c <- s) {
      if (c >= 0x20 && c <= 0x7E && c != '\\') sb += c
      else sb ++= "\\u{" ++= Integer.toHexString(c.toInt) ++= "}"
    }
    sb.toString
  }

  /** Decodes the escape sequences of an SMT-LIB 2.6 string literal, namely
    * `\ud₃d₂d₁d₀` and `\u{d₀}` to `\u{d₄d₃d₂d₁d₀}`. Any other backslash is a literal
    * backslash. Code points outside of the BMP are decoded to surrogate pairs.
    */
  def decode(s: String): String = decodeImpl(s, bmpOnly = false).get

  /** Decodes an SMT-LIB 2.6 string literal like [[decode]], but returns `None` if the
    * literal contains a code point outside of the BMP. SMT-LIB characters then map
    * one-to-one to the (UTF-16) characters of the decoded string.
    */
  def decodeBMP(s: String): Option[String] = decodeImpl(s, bmpOnly = true)

  private def decodeImpl(s: String, bmpOnly: Boolean): Option[String] = {
    val sb = new StringBuilder
    var i = 0
    def append(codePoint: Int): Boolean = {
      if (codePoint > 0xFFFF && bmpOnly) false
      else { sb.appendAll(Character.toChars(codePoint)); true }
    }
    while (i < s.length) {
      val c = s.charAt(i)
      if (c == '\\' && i + 1 < s.length && s.charAt(i + 1) == 'u') {
        if (i + 2 < s.length && s.charAt(i + 2) == '{') {
          val close = s.indexOf('}', i + 3)
          val digits = if (close < 0) "" else s.substring(i + 3, close)
          if (digits.nonEmpty && digits.length <= 5 && digits.forall(isHex)) {
            if (!append(Integer.parseInt(digits, 16))) return None
            i = close + 1
          } else {
            sb += c
            i += 1
          }
        } else if (i + 6 <= s.length && s.substring(i + 2, i + 6).forall(isHex)) {
          sb += Integer.parseInt(s.substring(i + 2, i + 6), 16).toChar
          i += 6
        } else {
          sb += c
          i += 1
        }
      } else if (bmpOnly && Character.isHighSurrogate(c) && i + 1 < s.length && Character.isLowSurrogate(s.charAt(i + 1))) {
        // an unescaped character outside of the BMP
        return None
      } else {
        sb += c
        i += 1
      }
    }
    Some(sb.toString)
  }
}
