package floatingcase;

/** Genuine scalar/effect boundaries; no CI suite or framework model. */
public final class Probe {
  public static final class Pure {
    public static float fdiv(float a, float b) { return a / b; }
    public static float frem(float a, float b) { return a % b; }
    public static double ddiv(double a, double b) { return a / b; }
    public static double drem(double a, double b) { return a % b; }
    public static int idiv(int a, int b) { return a / b; }
    public static int irem(int a, int b) { return a % b; }
    public static long ldiv(long a, long b) { return a / b; }
    public static long lrem(long a, long b) { return a % b; }
  }

  public static float stored;
  public static int hits;
  public static native void opaque();
  public static int changed() { return ++hits; }
  public static float field(float a, float b) { stored = a / b; return stored; }
  public static float callback(float a, float b, Runnable body) {
    float value = a / b;
    body.run();
    return value;
  }
  public static float nativeCall(float a, float b) {
    float value = a / b;
    opaque();
    return value;
  }
  public static float reflected(float a, float b, String name) throws Exception {
    float value = a / b;
    Class.forName(name);
    return value;
  }
  public static float monitor(float a, float b, Object lock) {
    synchronized (lock) { return a / b; }
  }
  public static float array(float a, float b, float[] values) {
    values[0] = a / b;
    return values[0];
  }
  public static float caught(float a, float b, boolean fail) {
    try {
      if (fail) throw new IllegalArgumentException();
      return a / b;
    } catch (IllegalArgumentException error) {
      changed();
      return a % b;
    }
  }
  public static float caughtCallback(float a, float b, boolean fail, Runnable body) {
    try {
      if (fail) throw new IllegalArgumentException();
      return a / b;
    } catch (IllegalArgumentException error) {
      body.run();
      return a % b;
    }
  }
  public static float throwing(float a, float b, Throwable failure) throws Throwable {
    float value = a / b;
    if (value > 0) throw failure;
    return value;
  }
  public static String dynamic(float a, float b) { return "value=" + (a / b); }
  public static float mixedInteger(float a, float b, int numerator, int divisor) {
    return a / b + numerator / divisor;
  }

  public static void main(String[] args) throws Throwable {
    System.out.println("float:" + Pure.fdiv(1, 0) + ":" + Pure.frem(1, 0));
    System.out.println("double:" + Pure.ddiv(1, 0) + ":" + Pure.drem(1, 0));
    int integerThrows = 0;
    try { Pure.idiv(1, 0); } catch (ArithmeticException expected) { integerThrows++; }
    try { Pure.irem(1, 0); } catch (ArithmeticException expected) { integerThrows++; }
    try { Pure.ldiv(1, 0); } catch (ArithmeticException expected) { integerThrows++; }
    try { Pure.lrem(1, 0); } catch (ArithmeticException expected) { integerThrows++; }
    System.out.println("integer-zero-throws:" + integerThrows);
    System.out.println("field:" + field(1, 0) + ":" + stored);
    callback(1, 0, () -> changed());
    System.out.println("callback-hits:" + hits);
    try { nativeCall(1, 0); }
    catch (UnsatisfiedLinkError expected) { System.out.println("native:UnsatisfiedLinkError"); }
    System.out.println("reflection:" + reflected(1, 0, "java.lang.String"));
    System.out.println("monitor:" + monitor(1, 0, new Object()));
    System.out.println("array:" + array(1, 0, new float[1]));
    System.out.println("caught:" + caught(1, 0, true) + ":" + hits);
    caughtCallback(1, 0, false, () -> changed());
    int dormantHandlerHits = hits;
    caughtCallback(1, 0, true, () -> changed());
    System.out.println("handler-callback-hits:" + dormantHandlerHits + ":" + hits);
    Throwable failure = new Throwable("identity-control");
    try { throwing(1, 0, failure); }
    catch (Throwable observed) { System.out.println("throw-identity:" + (observed == failure)); }
    System.out.println("dynamic:" + dynamic(1, 0));
    try { mixedInteger(1, 0, 1, 0); }
    catch (ArithmeticException expected) { System.out.println("mixed:ArithmeticException"); }
  }
}
