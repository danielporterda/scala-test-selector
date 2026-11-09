package registrationcase
import org.scalatest.{FutureOutcome, Outcome, Tag}
import org.scalatest.wordspec.{AnyWordSpec, AsyncWordSpec, FixtureAnyWordSpec, FixtureAsyncWordSpec}
import org.scalatest.flatspec.AnyFlatSpec

object Slow extends Tag("registration-style")
final class AsyncWordSuite extends AsyncWordSpec {
  var observed: Int = 0
  "case" in { observed = Effects.changed(); succeed }
}
final class FixtureFunctionSuite extends FixtureAnyWordSpec {
  type FixtureParam = Int
  var observed: Int = 0
  var made: Int = 0
  override def withFixture(test: OneArgTest): Outcome = test(5)
  def make(): FixtureParam => Any = {
    made = Effects.direct()
    value => { observed = Effects.changed() }
  }
  "case" in make()
}
final class FixtureThunkSuite extends FixtureAnyWordSpec {
  type FixtureParam = Int
  var observed: Int = 0
  override def withFixture(test: OneArgTest): Outcome = test(5)
  "case" in { () => observed = Effects.changed() }
}
final class TaggedFixtureSuite extends FixtureAnyWordSpec {
  type FixtureParam = Int
  var observed: Int = 0
  override def withFixture(test: OneArgTest): Outcome = test(5)
  "case" taggedAs(Slow) in { value => observed = Effects.changed() }
}
final class FixtureAsyncFunctionSuite extends FixtureAsyncWordSpec {
  type FixtureParam = Int
  var observed: Int = 0
  override def withFixture(test: OneArgAsyncTest): FutureOutcome = test(5)
  "case" in { value => observed = Effects.changed(); succeed }
}
final class FixtureAsyncThunkSuite extends FixtureAsyncWordSpec {
  type FixtureParam = Int
  var observed: Int = 0
  override def withFixture(test: OneArgAsyncTest): FutureOutcome = test(5)
  "case" in { () => observed = Effects.changed(); succeed }
}
final class TaggedAsyncSuite extends AsyncWordSpec {
  var observed: Int = 0
  "case" taggedAs(Slow) in { observed = Effects.changed(); succeed }
}
final class FlatItSuite extends AnyFlatSpec {
  var observed: Int = 0
  it should "case" in { observed = Effects.changed() }
}
final class WhenWordSuite extends AnyWordSpec {
  var observed: Int = 0
  "subject" when { "case" in { observed = Effects.changed() } }
}
