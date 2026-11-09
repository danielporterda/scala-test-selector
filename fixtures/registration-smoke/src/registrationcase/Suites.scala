package registrationcase

import org.scalatest.{BeforeAndAfterAll, Outcome}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.wordspec.AnyWordSpec

final class DirectSuite extends AnyFunSuite {
  var observed: Int = 0
  test("direct") { observed = Effects.changed() }
}
final class StoredSuite extends AnyFunSuite {
  var observed: Int = 0
  test("stored") {
    val stored = () => Effects.changed()
    observed = Effects.direct()
  }
}
final class InvokedSuite extends AnyFunSuite {
  var observed: Int = 0
  def invoke(f: () => Int): Int = f()
  test("invoked") { observed = invoke(() => Effects.changed()) }
}
final class OpaqueSuite extends AnyFunSuite {
  var observed: Int = 0
  test("opaque") {
    OpaqueSink.accept(() => Effects.changed())
    observed = Effects.direct()
  }
}
abstract class RegisteredBase extends AnyFunSuite {
  var observed: Int = 0
  protected def value(): Int = Effects.direct()
  test("inherited") { observed = value() }
}
final class InheritedSuite extends RegisteredBase {
  override protected def value(): Int = Effects.changed()
}
final class InheritedSibling extends RegisteredBase {
  override protected def value(): Int = Effects.direct()
}
abstract class HookBase extends AnyFunSuite with BeforeAndAfterAll {
  var observed: Int = 0
  override protected def beforeAll(): Unit = { observed = Effects.changed() }
  test("hooked") { Effects.direct() }
}
final class HookSuite extends HookBase
final class HookSibling extends HookBase {
  override protected def beforeAll(): Unit = { observed = Effects.direct() }
}
final class FixtureSuite extends AnyFunSuite {
  var observed: Int = 0
  override protected def withFixture(test: NoArgTest): Outcome = {
    observed = Effects.changed()
    super.withFixture(test)
  }
  test("fixture") { Effects.direct() }
}
final class WordSuite extends AnyWordSpec {
  var observed: Int = 0
  "case" in { observed = Effects.changed() }
}
final class NestedWordSuite extends AnyWordSpec {
  var observed: Int = 0
  "subject" should { "case" in { observed = Effects.changed() } }
}
