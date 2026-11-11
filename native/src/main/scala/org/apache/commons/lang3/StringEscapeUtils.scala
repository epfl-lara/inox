package org.apache.commons.lang3

/** Minimal stand-in for the commons-lang3 method Inox's printer uses, which
  * is a Java library and so not available on Scala Native. */
object StringEscapeUtils {
  def escapeJava(s: String): String = {
    val sb = new StringBuilder
    s.foreach {
      case '"'  => sb ++= "\\\""
      case '\\' => sb ++= "\\\\"
      case '\b' => sb ++= "\\b"
      case '\n' => sb ++= "\\n"
      case '\t' => sb ++= "\\t"
      case '\f' => sb ++= "\\f"
      case '\r' => sb ++= "\\r"
      case c if c < ' ' || c > '~' => sb ++= f"\\u${c.toInt}%04X"
      case c => sb += c
    }
    sb.toString
  }
}
