package namespacecase
object CheckNamespace {
  def main(args: Array[String]): Unit = {
    assert(Tracker.staticInitializations == 0)
    new ClassOnlySuite
    assert(Tracker.staticInitializations == 0)
    println("class-only:0")
    val dormant = new DormantSuite
    assert(Tracker.staticInitializations == 0)
    println("dormant-created:0")
    val active = new ActiveSuite
    assert(active.observed == 7 && Tracker.staticInitializations == 1 && Tracker.staticCalls == 1)
    println("active:7:1:1")
    assert(dormant.later() == 7 && Tracker.staticInitializations == 1 && Tracker.staticCalls == 2)
    println("dormant-invoked:7:1:2")
    val module = new ModuleSuite
    assert(module.observed == 8 && Tracker.moduleInitializations == 1 && Tracker.moduleCalls == 1)
    println("module:8:1:1")
    val instance = new InstanceSuite
    assert(instance.observed == 9 && Tracker.instances == 1 && Tracker.instanceCalls == 1)
    println("instance:9:1:1")
  }
}
