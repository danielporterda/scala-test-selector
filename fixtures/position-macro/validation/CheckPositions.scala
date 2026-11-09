package positioncase

object CheckPositions {
  def main(args: Array[String]): Unit = {
    require(Effects.hits == 0)
    val positions = new PositionSuite
    require(positions.direct.fileName == "PositionSuite.scala")
    require(positions.direct.lineNumber == 10)
    require(positions.inferred.fileName == "PositionSuite.scala")
    require(positions.inferred.lineNumber == 12)
    require(positions.before == 0 && positions.after == 0)
    println(s"direct:${positions.direct.fileName}:${positions.direct.lineNumber}")
    println(s"implicit:${positions.inferred.fileName}:${positions.inferred.lineNumber}")
    println(s"position-effects:${positions.before}:${positions.after}")
    val user = new UserMacroSuite
    require(user.before == 0 && user.after == 1 && user.value == 99)
    println(s"user-macro-effects:${user.before}:${user.after}")
    val assertion = new AssertionMacroSuite
    require(assertion.before == 1 && assertion.after == 11)
    println(s"assertion-argument-effects:${assertion.before}:${assertion.after}")
  }
}
