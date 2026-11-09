package namespacecase;
public final class JavaInstanceHost {
  public JavaInstanceHost() { Tracker.instances++; }
  public int ping() { Tracker.instanceCalls++; return 9; }
}
