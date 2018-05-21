/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package tip

import java.io._

import utils._

class PositionProvider(_reader: Reader, _file: Option[File]) {
  val (reader, file): (Reader, File) = _file match {
    case Some(file) => (_reader, file)
    case None =>
      val file = File.createTempFile("tip-input", ".smt2")
      val writer = new BufferedWriter(new FileWriter(file))
      val reader = new BufferedReader(_reader)

      val buffer = new Array[Char](1024)
      var count: Int = reader.read(buffer)
      while (count != -1) {
        writer.write(buffer, 0, count)
        count = reader.read(buffer)
      }
      writer.close()
      reader.close()

      (new BufferedReader(new FileReader(file)), file)
  }

  private val fileLines: List[String] = scala.io.Source.fromFile(file).getLines.toList

  def get(line: Int, col: Int): OffsetPosition = {
    val point = fileLines.take(line).map(_.length).sum + col
    new OffsetPosition(line, col, point, file)
  }
}

