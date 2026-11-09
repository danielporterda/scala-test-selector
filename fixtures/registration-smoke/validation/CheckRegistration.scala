package registrationcase
import org.scalatest.{Args, Reporter, Suite}
object CheckRegistration {
  def main(args: Array[String]): Unit = {
    val suites: List[(Suite, () => Int, Int)] = List(
      { val s = new DirectSuite; (s, () => s.observed, 41) },
      { val s = new StoredSuite; (s, () => s.observed, 7) },
      { val s = new InvokedSuite; (s, () => s.observed, 41) },
      { val s = new OpaqueSuite; (s, () => s.observed, 7) },
      { val s = new InheritedSuite; (s, () => s.observed, 41) },
      { val s = new InheritedSibling; (s, () => s.observed, 7) },
      { val s = new HookSuite; (s, () => s.observed, 41) },
      { val s = new HookSibling; (s, () => s.observed, 7) },
      { val s = new FixtureSuite; (s, () => s.observed, 41) },
      { val s = new WordSuite; (s, () => s.observed, 41) },
      { val s = new NestedWordSuite; (s, () => s.observed, 41) }
    )
    val reporter = new Reporter { def apply(event: org.scalatest.events.Event): Unit = () }
    for ((suite, observed, expected) <- suites) {
      assert(observed() == 0, "registration must defer executable test and hook bodies")
      assert(suite.testNames.size == 1)
      val status = suite.run(None, Args(reporter))
      status.waitUntilCompleted()
      assert(status.succeeds())
      assert(observed() == expected, suite.getClass.getName + ":" + observed())
      println("suite:" + suite.getClass.getName + ":tests=" + suite.testNames.size + ":observed=" + observed())
    }
  }
}
