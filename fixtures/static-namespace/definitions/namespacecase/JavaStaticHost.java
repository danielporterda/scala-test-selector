package namespacecase;
public final class JavaStaticHost {
  static { Tracker.staticInitializations++; }
  public static int ping() { return changed(); }
  public static int changed() { Tracker.staticCalls++; return 7; }
}
