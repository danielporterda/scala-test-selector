package traitcase
trait Root { def f: Int = 1 }
trait Layer extends Root { abstract override def f: Int = super.f + 1 }
final class Uses extends Root with Layer {
  def plain: Int = super.f
  def qualified: Int = super[Root].f
}
object Check {
  def main(args: Array[String]): Unit = {
    val x = new Uses
    assert(x.plain == 2)
    assert(x.qualified == 1)
    println(s"plain:${x.plain},qualified:${x.qualified}")
  }
}
