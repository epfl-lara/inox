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

  /** Escapes a sequence of characters (code points) so that it can be used as an SMT-LIB 2.6 string
    * literal: printable ASCII characters are kept as-is (apart from the backslash which could otherwise
    * start an escape sequence) and all other characters are written as `\u{...}` escapes.
    * Note that double quotes are escaped by the SMT-LIB printer.
    */
  def encode(codePoints: Seq[Int]): String = {
    val sb = new StringBuilder
    for (c <- codePoints) {
      if (c >= 0x20 && c <= 0x7E && c != '\\') sb += c.toChar
      else sb ++= "\\u{" ++= Integer.toHexString(c) ++= "}"
    }
    sb.toString
  }

  /** Decodes the characters (code points) of an SMT-LIB 2.6 string literal, with its escape sequences
    * `\ud₃d₂d₁d₀` and `\u{d₀}` to `\u{d₄d₃d₂d₁d₀}`. Any other backslash is a literal backslash. A surrogate
    * pair in the literal itself (in a file read as UTF-8, for example) is a single character.
    */
  def decode(s: String): Seq[Int] = {
    val res = Seq.newBuilder[Int]
    var i = 0
    while (i < s.length) {
      val c = s.charAt(i)
      if (c == '\\' && i + 1 < s.length && s.charAt(i + 1) == 'u') {
        if (i + 2 < s.length && s.charAt(i + 2) == '{') {
          val close = s.indexOf('}', i + 3)
          val digits = if (close < 0) "" else s.substring(i + 3, close)
          if (digits.nonEmpty && digits.length <= 5 && digits.forall(isHex)) {
            res += Integer.parseInt(digits, 16)
            i = close + 1
          } else {
            res += c
            i += 1
          }
        } else if (i + 6 <= s.length && s.substring(i + 2, i + 6).forall(isHex)) {
          res += Integer.parseInt(s.substring(i + 2, i + 6), 16)
          i += 6
        } else {
          res += c
          i += 1
        }
      } else {
        val cp = s.codePointAt(i)
        res += cp
        i += Character.charCount(cp)
      }
    }
    res.result()
  }
}
