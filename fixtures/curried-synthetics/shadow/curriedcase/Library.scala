package curriedcase

import org.scalactic.source.Position

// Same binary owner, incompatible descriptor. It must shadow later classpaths.
object Library {
  def curried(value: Int)(implicit position: Position): Int = value + 1000
  def returned(value: Int): Int = value
}
