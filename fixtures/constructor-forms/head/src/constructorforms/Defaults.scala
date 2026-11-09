package constructorforms
object Defaults {
  def run(value: Int = Effects.changed()): Int = value
  def force(value: => Int = Effects.changed()): Int = value
  def ignore(value: => Int = Effects.changed()): Int = 7
  def dependent(prefix: Int)(value: Int = prefix): Int = value
}
