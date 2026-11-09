package namespacecase

object ScalaModule {
  Tracker.moduleInitializations += 1
  def ping(): Int = { Tracker.moduleCalls += 1; 8 }
}
final class ActiveSuite { val observed = JavaStaticHost.ping() }
final class DormantSuite { val later = () => JavaStaticHost.ping() }
final class ModuleSuite { val observed = ScalaModule.ping() }
final class InstanceSuite { val host = new JavaInstanceHost(); val observed = host.ping() }
final class ClassOnlySuite { val observed = classOf[JavaStaticHost] }
