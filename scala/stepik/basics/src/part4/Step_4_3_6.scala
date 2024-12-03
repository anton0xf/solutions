package part4

object Step_4_3_6 {
def getType(collection: Any): String = {
  collection match {
    case Seq(_: String, _*) => "Collection Of Strings"
    case Array(_: String, _*) => "Collection Of Strings"
    case Seq(_: Int, _*) => "Collection Of Ints"
    case Array(_: Int, _*) => "Collection Of Ints"
    case Seq(_: Double, _*) => "Collection Of Doubles"
    case Array(_: Double, _*) => "Collection Of Doubles"
    case _ => "Unknown type"
  }
  }
  def main(args: Array[String]): Unit = {
    println(getType(Seq(1.0, 2.0)))
  }
}