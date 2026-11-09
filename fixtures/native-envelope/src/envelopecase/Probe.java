package envelopecase;

public final class Probe {
  public static final class Scalar {
    public static int disjointScalar(int value) { return value > 0 ? (value * 3) ^ 17 : -value; }
    public static int disjointEntry() { return disjointScalar(4); }
  }
  private static int hits;
  private static Runnable escaped;

  public static int changed() { ++hits; return 41; }
  public static void reset() { hits = 0; }
  public static int hits() { return hits; }
  public static int branch(boolean selected) { return selected ? changed() : 0; }
  public static int sparseSwitch(int selected) {
    switch (selected) { case 7: return changed(); case 100: return 2; default: return 0; }
  }
  public static int denseSwitch(int selected) {
    switch (selected) { case 0: return 0; case 1: return changed(); case 2: return 2; default: return 3; }
  }
  public static int caught(boolean selected) {
    try {
      if (selected) throw new IllegalArgumentException("selected");
      return 0;
    } catch (IllegalArgumentException failure) { return changed(); }
  }
  public static int disjointScalar(int value) { return value > 0 ? (value * 3) ^ 17 : -value; }
  public static int disjointEntry() { return disjointScalar(4); }
  public static int branchEntry() { return branch(true); }
  public static void escape(Runnable callback) { escaped = callback; }
  public static void invokeEscaped() { escaped.run(); }
  public static Class<?> reflection(String name) throws ClassNotFoundException { return Class.forName(name); }
  public static native void missing();
  public static void invokesMissing() { missing(); }
  public static int array(int[] values) { return values[0]; }
  public static void monitor(Object lock) { synchronized (lock) { changed(); } }
}
