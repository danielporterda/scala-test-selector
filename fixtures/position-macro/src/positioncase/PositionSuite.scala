package positioncase

import org.scalactic.source.Position
import org.scalatest.funsuite.AnyFunSuite

object Effects { var hits: Int = 0 }

class PositionSuite extends AnyFunSuite {
  val before: Int = Effects.hits
  val direct: Position = Position.here
  def capture(implicit position: Position): Position = position
  val inferred: Position = capture
  val after: Int = Effects.hits
  test("position metadata") {
    require(direct.fileName == "PositionSuite.scala")
    require(direct.lineNumber == 10)
    require(inferred.fileName == "PositionSuite.scala")
    require(inferred.lineNumber == 12)
    require(before == after)
  }
}

class UserMacroSuite extends AnyFunSuite {
  val before: Int = Effects.hits
  val value: Int = UserMacros.effect()
  val after: Int = Effects.hits
  test("user macro effects") {
    require(value == 99)
    require(after == before + 1)
  }
}

class AssertionMacroSuite extends AnyFunSuite {
  val before: Int = Effects.hits
  assert({ Effects.hits += 10; true })
  val after: Int = Effects.hits
  test("assertion macro argument effects") {
    require(after == before + 10)
  }
}
