package anonymouscase

object CheckAllocations {
  def observed(name: String, expected: String): Unit = {
    val actual = Effects.drain()
    assert(actual == expected, name + ":" + actual)
    println(name + ":" + actual)
  }
  def main(args: Array[String]): Unit = {
    new Active
    observed("active", "trait-init")
    new ClassActive
    observed("class-active", "argument,class:7")
    new BodyActive
    observed("body-active", "trait-init,body")
    val dormant = new Dormant
    observed("dormant-created", "")
    dormant.later()
    observed("dormant-invoked", "trait-init")
    val overridden = new OverrideActive
    observed("override-created", "trait-init")
    overridden.allocated.work()
    observed("override-invoked", "override")
  }
}
