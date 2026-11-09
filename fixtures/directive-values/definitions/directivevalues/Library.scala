package directivevalues

object Effects {
  var trace: String = ""
  def note(value: String): Unit = { trace = if (trace.isEmpty) value else trace + "," + value }
  def reset(): Unit = { trace = "" }
}

final class Gate {
  def run(inner: () => Int): Int = { Effects.note("run"); inner() }
}
final class StrictGate {
  def run(inner: Int): Int = { Effects.note("strict-run"); inner }
}
final class DeferredGate {
  def run(inner: () => Int): Int = { Effects.note("deferred-run"); inner() }
}

trait Api {
  def get: Gate = { Effects.note("get"); new Gate }
  implicit def convert(gate: Gate): (=> Int) => Int = {
    Effects.note("convert")
    inner => { Effects.note("invoke"); gate.run(() => inner) }
  }
  def strictGet: StrictGate = { Effects.note("strict-get"); new StrictGate }
  implicit def strictConvert(gate: StrictGate): Int => Int = {
    Effects.note("strict-convert")
    inner => { Effects.note("strict-invoke"); gate.run(inner) }
  }
  def deferredGet: DeferredGate = { Effects.note("deferred-get"); new DeferredGate }
  implicit def deferredConvert(gate: => DeferredGate): (=> Int) => Int = {
    Effects.note("deferred-convert")
    inner => { Effects.note("deferred-invoke"); gate.run(() => inner) }
  }
}
