package repeatedcallbacks

object Effects {
  var trace: String = ""
  def note(value: String): Unit = { trace = if (trace.isEmpty) value else trace + "," + value }
  def reset(): Unit = { trace = "" }
}

trait Api {
  def aggregate(callbacks: (() => Int)*): Int = {
    Effects.note("aggregate")
    callbacks(0)() + callbacks(1)()
  }
  def store(callbacks: (() => Int)*): () => Int = () => aggregate(callbacks: _*)
  def mixed(prefix: => Int, callbacks: (() => Int)*): Int = {
    Effects.note("mixed")
    callbacks(0)() + callbacks(1)() + prefix
  }
}
