package curriedcase

import org.scalactic.Prettifier
import org.scalactic.source.Position

object Effects {
  var hits: Int = 0
  def note(value: Int): Int = { hits += value; hits }
}

object Library {
  def curried(value: Int)(implicit position: Position, prettifier: Prettifier): Int =
    Effects.note(value)

  def returned(value: Int): () => Int = () => Effects.note(value)
}
