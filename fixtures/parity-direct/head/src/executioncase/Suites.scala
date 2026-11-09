package executioncase

// These are real ScalaTest suites. The exercised lifecycle is suite construction.
// No library test-registration semantics are assumed by the selector fixture.
final class AffectedSuite extends org.scalatest.Suite {
  val observed: Int = Changed.value()
  def dormant(): Int = Unchanged.value()
}
final class UnaffectedSuite extends org.scalatest.Suite {
  val observed: Int = Unchanged.value()
}
final class DormantSuite extends org.scalatest.Suite {
  val observed: Int = Unchanged.value()
  def dormantFactory(): () => Int = Factory.make(() => Changed.value())
}
