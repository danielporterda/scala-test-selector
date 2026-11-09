package fixture;

interface Runner { void invoke(Runnable callback); }
class Made {
  final Runnable callback;
  Made(Runnable callback) { this.callback = callback; }
}
final class Refined extends Made { Refined(Runnable callback) { super(callback); } }
class Base { public Made make() { return new Made(null); } }
class Child extends Base { public Refined make() { return new Refined(null); } }
final class Immediate { Immediate(Runnable callback) { callback.run(); } }

public final class Probe implements Runner {
  private final Runnable callback;
  public Probe(Runnable callback) { this.callback = callback; }
  public static Made make(Runnable callback) { return new Made(callback); }
  public static Immediate createRun(Runnable callback) { return new Immediate(callback); }
  public static Made callAfterStore(Runnable callback) {
    Made box = new Made(callback); box.callback.run(); return box;
  }
  public static Made opaqueAfterStore(Runnable callback) {
    Made box = new Made(callback); opaque(box); return box;
  }
  private static void opaque(Object value) { if (System.nanoTime() > 0) System.out.println(value); }
  public static Object forward(Object value) { return value; }
  public Object self() { return this; }
  public Runnable getter() { return callback; }
  public void invoke(Runnable callback) { callback.run(); }
  public void submit(Runnable callback) { invoke(callback); }
  public static Object wide(long first, Object second, double third) { return second; }
  public static long wideConstant() { return 123456789123L; }
  public static Object branch(boolean pick, Object left, Object right) { return pick ? left : right; }
  public static Object partial(Runnable callback, boolean pick) { callback.run(); return pick ? callback : null; }
  public static Object over(int value) { return null; }
  public static Object over(String value) { return value; }
  public static Made declaredOnly() { throw new IllegalStateException(); }
  public static Object indy() { return (Runnable) () -> {}; }
}
