import scala.io.Source
import scala.collection.mutable

object SysctlConfParser {
  def parse(filename: String): Map[String, String] = {
    val result = mutable.Map[String, String]()
    val lines = Source.fromFile(filename).getLines()
    var currentLine = ""
    var inMultilineValue = false
    var quoteChar: Option[Char] = None

    while (lines.hasNext) {
      val line = lines.next()
      var trimmedLine = line.trim

      val lineContinues = trimmedLine.endsWith("\\")
      if (lineContinues) {
        trimmedLine = trimmedLine.dropRight(1)
      }

      currentLine += trimmedLine

      if (lineContinues) {
        currentLine += "\n"
        
      } else {
        currentLine = removeInlineComments(currentLine)

        if (currentLine.trim.isEmpty) {
          currentLine = ""
          inMultilineValue = false
          quoteChar = None
        } else {
          val index = currentLine.indexOf('=')
          if (index == -1) {
            throw new IllegalArgumentException(s"無効な行: $currentLine")
          }

          val key = currentLine.substring(0, index).trim
          var value = currentLine.substring(index + 1).trim

          if (isQuoted(value)) {
            quoteChar = Some(value.head)
            if (value.last != quoteChar.get || value.length == 1) {
              value = value.drop(1) 
              inMultilineValue = true

              while (inMultilineValue && lines.hasNext) {
                val nextLine = lines.next()
                var nextTrimmed = nextLine.trim

                val nextLineContinues = nextTrimmed.endsWith("\\")
                if (nextLineContinues) {
                  nextTrimmed = nextTrimmed.dropRight(1)
                }

                value += "\n" + nextTrimmed

                if (!nextLineContinues && nextTrimmed.endsWith(quoteChar.get.toString)) {
                  value = value.dropRight(1) 
                  inMultilineValue = false
                } else if (!nextLineContinues) {
                  value += "\n"
                }
              }
              if (inMultilineValue) {
                throw new IllegalArgumentException("クオートが閉じられていません")
              }
            } else {
              // 一行のクオート値
              value = value.substring(1, value.length - 1)
            }
          } else {
            // クオートされていない値のコメント除去
            value = value.split("#", 2)(0).trim
          }

          result(key) = value
          currentLine = ""
        }
      }
    }

    result.toMap
  }

  private def isQuoted(s: String): Boolean = {
    (s.startsWith("\"") || s.startsWith("'")) &&
    (s.length == 1 || s.last != s.head || (s.length > 1 && s.last == s.head))
  }

  private def removeInlineComments(s: String): String = {
    val sb = new StringBuilder
    var inSingleQuote = false
    var inDoubleQuote = false
    var i = 0
    while (i < s.length) {
      val c = s.charAt(i)
      if (c == '\'' && !inDoubleQuote) {
        inSingleQuote = !inSingleQuote
      } else if (c == '"' && !inSingleQuote) {
        inDoubleQuote = !inDoubleQuote
      } else if (c == '#' && !inSingleQuote && !inDoubleQuote) {
        // コメントを無視
        return sb.toString()
      }
      sb.append(c)
      i += 1
    }
    sb.toString()
  }
}
object Main extends App {
  try {
 
    val filePath = "path/to/your/sysctl.conf" 
    val config = SysctlConfParser.parse(filePath)
    for ((key, value) <- config) {
      println(s"$key = $value")
    }
  } catch {
    case e: Exception =>
      println(s"エラー: ${e.getMessage}")
  }
}