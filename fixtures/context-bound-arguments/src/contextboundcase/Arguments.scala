package contextboundcase

trait Render[V] { def render(value: V): Int }
object Effects {
  var defaults = 0
  var renders = 0
  var evidence = 0
  def defaultMade(): Unit = { defaults += 1 }
  def rendered(value: Int, factor: Int): Int = {
    renders += 1
    evidence = factor
    value * factor
  }
}
final class RecordingRender(val factor: Int) extends Render[Int] {
  def render(value: Int): Int = Effects.rendered(value, factor)
}
object Evidence {
  implicit val first: Render[Int] = new RecordingRender(2)
  val second: Render[Int] = new RecordingRender(3)
}
final class Item(val value: Int)
object Syntax {
  implicit final class RenderOps[V](val value: V)(implicit val evidence: Render[V]) {
    def rendered: Int = evidence.render(value)
  }
}
object Api {
  def defaultCond[T]: T => Boolean = {
    Effects.defaultMade()
    _ => true
  }
  def param[T, V: Render](name: String, get: T => V,
                         cond: T => Boolean = defaultCond[T]): T => Int = {
    x => if (cond(x)) implicitly[Render[V]].render(get(x)) else 0
  }
  def named[V: Render](value: V): Int = {
    import Syntax._
    val use: V => Int = x => x.rendered
    use(value)
  }
  def placeholder[V: Render](value: V): Int = {
    import Syntax._
    val use: V => Int = _.rendered
    use(value)
  }
}
object Calls {
  import Evidence.first
  def omitted(): Item => Int = Api.param[Item, Int]("omitted", _.value)
  def explicitCondition(): Item => Int =
    Api.param[Item, Int]("explicit", _.value, (_: Item) => true)
  def namedArguments(): Item => Int =
    Api.param[Item, Int](get = _.value, name = "named")
  def explicitEvidence(): Item => Int =
    Api.param[Item, Int]("evidence", _.value)(Evidence.second)
  def immediatelyApplied(): Int =
    Api.param[Item, Int]("applied", _.value)(Evidence.second)(new Item(7))
  def renderedNamed(): Int = Api.named[Int](3)
  def renderedPlaceholder(): Int = Api.placeholder[Int](3)
}
