package anonymouscase

object Effects {
  private var events = List.empty[String]
  def note(value: String): Unit = { events = value :: events }
  def drain(): String = { val result = events.reverse.mkString(","); events = Nil; result }
}
trait Parent {
  Effects.note("trait-init")
  def work(): Unit = ()
}
class WithCtor(value: Int) {
  Effects.note("class:" + value)
}
final class Active {
  val allocated = new Parent {}
}
final class ClassActive {
  def effectArg(): Int = { Effects.note("argument"); 7 }
  val allocated = new WithCtor(effectArg()) {}
}
final class BodyActive {
  val allocated = new Parent { Effects.note("body") }
}
final class Dormant {
  val later = () => new Parent {}
}
final class OverrideActive {
  val allocated = new Parent { override def work(): Unit = Effects.note("override") }
}
