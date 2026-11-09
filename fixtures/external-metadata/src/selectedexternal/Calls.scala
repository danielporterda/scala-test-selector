package selectedexternal

final class Calls extends Configuration {
  def interval(): Span = { Effects.note("interval"); new Span(2) }
  def timeout(): Span = { Effects.note("timeout"); new Span(1) }
  def label(): String = { Effects.note("label"); "x" }
  def qualifier(): Library.type = { Effects.note("qualifier"); Library }

  def inherited(): PatienceConfig = PatienceConfig(interval = interval(), timeout = timeout())
  def qualified(): Any = qualifier().PatienceConfig(interval = interval(), timeout = timeout())
  def positional(): Any = qualifier().PatienceConfig(timeout(), interval())
  def overloaded(): Any = qualifier().PatienceConfig(label())
  def eta(): () => Any = {
    val factory: (Span, Span) => Any = qualifier().PatienceConfig.apply
    () => factory(timeout(), interval())
  }
  def returned(): Span => Any = qualifier().PatienceConfig.returning(timeout())
  def appliedReturned(): Any = qualifier().PatienceConfig.returning(timeout())(interval())
  def dormant(): () => Any = () => qualified()
}
