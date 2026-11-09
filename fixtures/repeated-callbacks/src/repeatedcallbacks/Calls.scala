package repeatedcallbacks

final class Calls extends Api {
  def provider(label: String, value: Int): () => Int = {
    Effects.note("provider:" + label)
    () => { Effects.note("call:" + label); value }
  }
  def flat(): Int = aggregate(provider("a", 1), provider("b", 2))
  def empty(): () => Int = store()
  def spread(): Int = {
    val callbacks = Seq(provider("a", 1), provider("b", 2))
    aggregate(callbacks: _*)
  }
  def captured(): () => Int = store(provider("a", 1), provider("b", 2))
  def prefix(): Int = { Effects.note("prefix"); 7 }
  def mixedCall(): Int = mixed(prefix(), provider("a", 1), provider("b", 2))
  def dormant(): () => Int = () => aggregate(provider("dormant-a", 4), provider("dormant-b", 5))
}
