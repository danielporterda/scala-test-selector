package valuebounds
object Factories {
  type Alias = Narrow
  def known(): Base = new Allowed()
  def narrow(): Narrow = Opaque.narrow()
  def alias(): Alias = Opaque.narrow()
  def generic[T <: Narrow](): T = Opaque.generic[T]()
  def intersection(): Narrow with Marker = Opaque.intersection()
  def broad(): Base = Opaque.broad()
}
