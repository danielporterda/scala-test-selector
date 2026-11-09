package executioncase
object Factory {
  def make(callback: () => Int): () => Int = () => callback()
}
