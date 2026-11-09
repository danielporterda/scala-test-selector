package registrationcase
import org.scalatest.{Args, Reporter, Suite}
object CheckRegistration {
  def main(args: Array[String]): Unit = {
    val factory = new FixtureFunctionSuite
    assert(factory.made == 7, "Function1 fixture argument factory executes during registration")
    println("factory:FixtureFunctionSuite:made=" + factory.made + ":observed=" + factory.observed)
    val suites: List[(Suite, () => Int)] = List(
      { val s = new AsyncWordSuite; (s, () => s.observed) },
      (factory, () => factory.observed),
      { val s = new FixtureThunkSuite; (s, () => s.observed) },
      { val s = new TaggedFixtureSuite; (s, () => s.observed) },
      { val s = new FixtureAsyncFunctionSuite; (s, () => s.observed) },
      { val s = new FixtureAsyncThunkSuite; (s, () => s.observed) },
      { val s = new TaggedAsyncSuite; (s, () => s.observed) },
      { val s = new FlatItSuite; (s, () => s.observed) },
      { val s = new WhenWordSuite; (s, () => s.observed) }
    )
    val reporter = new Reporter { def apply(event: org.scalatest.events.Event): Unit = () }
    for ((suite, observed) <- suites) {
      assert(observed() == 0)
      assert(suite.testNames.size == 1)
      val status = suite.run(None, Args(reporter))
      status.waitUntilCompleted()
      assert(status.succeeds())
      assert(observed() == 41, suite.getClass.getName + ":" + observed())
      println("suite:" + suite.getClass.getName + ":tests=1:observed=" + observed())
    }
  }
}
