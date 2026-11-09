package callbackcase
object Shared {
  def run(callback: () => Int): Int = callback()
  def captured(callback: () => Int): () => Int = () => callback()
}
