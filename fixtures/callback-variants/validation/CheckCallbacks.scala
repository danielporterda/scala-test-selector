package callbackcase
object CheckCallbacks {
  def main(args: Array[String]): Unit = {
    val values = Vector(
      new Lexical1Suite().observed,
      new Lexical2Suite().observed,
      new Lexical3Suite().observed,
      new Lexical4Suite().observed,
      new Lexical5Suite().observed,
      new Lexical6Suite().observed,
      new Captured1Suite().observed,
      new Captured2Suite().observed,
      new Captured3Suite().observed,
      new Captured4Suite().observed,
      new Captured5Suite().observed,
      new Captured6Suite().observed,
      new UnknownSuite().observed)
    println("values:" + values.mkString(","))
    val expected = Vector(1,2,3,4,5,args(0).toInt,10,20,30,40,50,args(0).toInt,99)
    assert(values == expected)
  }
}
