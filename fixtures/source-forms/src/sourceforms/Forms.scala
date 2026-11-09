package sourceforms

object Forms {
  private var calls = 0
  def observed: Int = calls
  def effect: Int = { calls += 1; 7 }
  def generic[A]: Int = effect
  def identity[A](value: A): A = { calls += 10; value }
  def typed: Int = generic[Int]
  def applied: Int = identity[Int](effect)
  val placeholder: Int => Int = identity[Int](_)
  val eta: Int => Int = identity[Int]
  def receiver: Forms.type = { calls += 1000; Forms }
  def receiverEta: Int => Int = receiver.identity[Int]
  def bare(value: Int): Int = { calls += 100; value }
  val bareEta: Int => Int = bare
  def bareReceiverEta: Int => Int = receiver.bare
  def nullaryBare: Int = effect
  def curried[A](a: A)(b: A): A = b
  val curriedEta: Int => Int => Int = curried[Int]
  def interpolate: String = s"value=${effect}"
  def yielding: List[Int] = for (x <- List(effect)) yield identity[Int](x)
  def named(a: Int, b: Int): Int = a * 10 + b
  def first: Int = 1
  def second: Int = 2
  def namedCall: Int = named(b = second, a = first)
}

object CheckSourceForms {
  def main(args: Array[String]): Unit = {
    assert(Forms.observed == 0, "creating placeholder/eta callbacks must not invoke identity")
    assert(Forms.typed == 7 && Forms.observed == 1)
    assert(Forms.applied == 7 && Forms.observed == 12)
    assert(Forms.placeholder(1) == 1 && Forms.observed == 22)
    assert(Forms.eta(2) == 2 && Forms.observed == 32)
    assert(Forms.namedCall == 12)
    assert(Forms.yielding == List(7) && Forms.observed == 43)
    assert(Forms.interpolate == "value=7" && Forms.observed == 44)
    val capturedReceiver = Forms.receiverEta
    assert(Forms.observed == 1044, "eta receiver must be evaluated at callback creation")
    assert(capturedReceiver(3) == 3 && Forms.observed == 1054)
    assert(Forms.curriedEta(1)(2) == 2)
    assert(Forms.bareEta(4) == 4 && Forms.observed == 1154)
    val bareReceiver = Forms.bareReceiverEta
    assert(Forms.observed == 2154, "bare eta receiver must be evaluated at callback creation")
    assert(bareReceiver(5) == 5 && Forms.observed == 2254)
    assert(Forms.nullaryBare == 7 && Forms.observed == 2255)
    println("source-forms:typed=7:applied=7:placeholder=1:eta=2:named=12:yield=7:receiver=3:bare=4:bare-receiver=5:nullary=7:calls=2255")
  }
}
