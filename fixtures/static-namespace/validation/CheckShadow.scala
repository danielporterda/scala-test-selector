package namespacecase
object CheckShadow {
  def main(args: Array[String]): Unit = {
    try { new ActiveSuite; throw new AssertionError("static shadow unexpectedly linked") }
    catch { case _: IncompatibleClassChangeError => println("shadow-static:IncompatibleClassChangeError") }
  }
}
