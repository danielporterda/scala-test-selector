package externalprefix

final class Box[A](val value: A) {
  def map[B](function: A => B): Box[B] = {
    Native.note("map")
    new Box[B](function(value))
  }
  def flatMap[B](function: A => Box[B]): Box[B] = {
    Native.note("flatMap")
    function(value)
  }
}

final class Calls {
  def text(): String = { Native.note("text"); "x" }
  def number(): Int = { Native.note("number"); 7 }
  def stringConstructor(): Native = new Native(text())
  def intConstructor(): Native = new Native(number())
  def dormantConstructor(): () => Native = () => new Native(text())
  def classLiteral(): Class[Native] = classOf[Native]
  def box(): Box[Int] = { Native.note("box"); new Box[Int](1) }
  def mapped(value: Int): Int = { Native.note("map-body"); value + 1 }
  def flatMapped(value: Int): Box[Int] = { Native.note("flat-body"); new Box[Int](value + 1) }
  def chain(): Int = box().map(value => mapped(value)).flatMap(value => flatMapped(value)).value
  def dormantChain(): () => Int = () => chain()
  def generic[A](value: A): A = { Native.note("generic"); value }
  def eta(): Int => Int = generic[Int] _
}
