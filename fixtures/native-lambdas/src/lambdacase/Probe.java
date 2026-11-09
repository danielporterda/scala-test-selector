package lambdacase;

public final class Probe {
  private static int staticEffects;
  private int receiverEffects;
  private int stored;
  private static int targetInitializations;
  private static int targetEffects;

  public static Runnable staticClosure(int captured) {
    return () -> staticEffect(captured);
  }

  public Runnable receiverClosure(int captured) {
    return () -> receiverEffect(captured);
  }

  public Runnable boundClosure() {
    return this::next;
  }

  private static void staticEffect(int value) {
    staticEffects += value;
  }

  private void receiverEffect(int value) {
    receiverEffects += value;
  }

  private void next() {
    ++receiverEffects;
  }

  public static java.util.function.Consumer<Probe> unbound() { return Probe::next; }

  public static Runnable separateStaticClosure() { return DeferredTarget::touch; }
  public static void runSeparate() { separateStaticClosure().run(); }

  private static final class DeferredTarget {
    static { ++targetInitializations; }
    private static void touch() { ++targetEffects; }
  }

  public static int targetInitializations() { return targetInitializations; }
  public static int targetEffects() { return targetEffects; }

  public static void runStatic() { staticClosure(3).run(); }
  public void runReceiver() { receiverClosure(5).run(); }
  public void runBound() { boundClosure().run(); }

  public void unsupportedThenStore(int value) {
    String opaque = "opaque:" + value;
    stored = value;
  }

  public static int staticEffects() { return staticEffects; }
  public int receiverEffects() { return receiverEffects; }
  public int stored() { return stored; }
}
