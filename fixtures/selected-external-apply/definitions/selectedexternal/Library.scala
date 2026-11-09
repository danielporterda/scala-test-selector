package selectedexternal

object Effects {
  var trace: String = ""
  def note(event: String): Unit = { trace = if (trace.isEmpty) event else trace + "," + event }
  def reset(): Unit = { trace = "" }
}
final class Span(val value: Int)
trait Configuration {
  case class PatienceConfig(timeout: Span = new Span(10), interval: Span = new Span(20))
  object PatienceConfig {
    def apply(label: String): PatienceConfig = {
      Effects.note("overload:" + label)
      new PatienceConfig(new Span(30), new Span(40))
    }
    def returning(timeout: Span): Span => PatienceConfig = {
      Effects.note("factory")
      interval => { Effects.note("returned-body"); new PatienceConfig(timeout, interval) }
    }
  }
}
object Library extends Configuration
