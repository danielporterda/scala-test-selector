package finitecase;

/** Genuine instructions, not normalized Rust IR or compiler capture records. */
public final class Probe {
  public static int shared;
  public static int readInt(int[] a, int i) { return a[i]; }
  public static long readLong(long[] a, int i) { return a[i]; }
  public static float readFloat(float[] a, int i) { return a[i]; }
  public static double readDouble(double[] a, int i) { return a[i]; }
  public static Object readReference(Object[] a, int i) { return a[i]; }
  public static byte readByte(byte[] a, int i) { return a[i]; }
  public static boolean readBoolean(boolean[] a, int i) { return a[i]; }
  public static char readChar(char[] a, int i) { return a[i]; }
  public static short readShort(short[] a, int i) { return a[i]; }
  public static int length(int[] a) { return a.length; }
  public static int referenceLength(Object[] a) { return a.length; }
  public static boolean[] newBoolean(int n) { return new boolean[n]; }
  public static byte[] newByte(int n) { return new byte[n]; }
  public static char[] newChar(int n) { return new char[n]; }
  public static short[] newShort(int n) { return new short[n]; }
  public static int[] newInt(int n) { return new int[n]; }
  public static long[] newLong(int n) { return new long[n]; }
  public static float[] newFloat(int n) { return new float[n]; }
  public static double[] newDouble(int n) { return new double[n]; }
  public static Object[] newReference(int n) { return new Object[n]; }
  public static int[][] newMultiPrimitive(int n, int m) { return new int[n][m]; }
  public static Object[][] newMultiReference(int n, int m) { return new Object[n][m]; }
  public static void writeInt(int[] a, int i, int x) { a[i] = x; }
  public static void writeLong(long[] a, int i, long x) { a[i] = x; }
  public static void writeFloat(float[] a, int i, float x) { a[i] = x; }
  public static void writeDouble(double[] a, int i, double x) { a[i] = x; }
  public static void writeReference(Object[] a, int i, Object x) { a[i] = x; }
  public static void writeByte(byte[] a, int i, byte x) { a[i] = x; }
  public static void writeBoolean(boolean[] a, int i, boolean x) { a[i] = x; }
  public static void writeChar(char[] a, int i, char x) { a[i] = x; }
  public static void writeShort(short[] a, int i, short x) { a[i] = x; }
  public static int divideInt(int a, int b) { return a / b; }
  public static long divideLong(long a, long b) { return a / b; }
  public static int remainderInt(int a, int b) { return a % b; }
  public static long remainderLong(long a, long b) { return a % b; }
  public static int branchAndCatch(boolean first, int[] a, int i, Runnable effect) {
    try {
      if (first) { int x = a[i]; shared = 1; return x; }
      int x = readInt(a, i);
      effect.run();
      return x;
    } catch (NullPointerException | ArrayIndexOutOfBoundsException failure) {
      effect.run(); shared = 2; return -1;
    }
  }
  public static int catchDivision(int a, int b, Runnable effect) {
    try { return a / b; }
    catch (ArithmeticException failure) { effect.run(); shared = 3; return -1; }
  }
  public static int catchNegative(int n, Runnable effect) {
    try { return new int[n].length; }
    catch (NegativeArraySizeException failure) { effect.run(); shared = 4; return -1; }
  }
  public static int writeAfterAllocation(int n) {
    int[] a = new int[n]; shared = 5; return after(a.length);
  }
  public static int after(int n) { shared = 6; return n; }
  public static int callbackAfterRead(int[] a, Runnable effect) {
    int x = a[0]; effect.run(); return x;
  }
  public static int monitorAfterRead(int[] a, Object lock) {
    int x = a[0]; synchronized (lock) { return x; }
  }
  public static native int opaque();
  public static int nativeAfterRead(int[] a) { int x = a[0]; return x + opaque(); }
  public static Class<?> reflectAfterRead(int[] a, String name) throws Exception {
    shared = a[0]; return Class.forName(name);
  }
  public static String dynamicAfterRead(int[] a) { return "n=" + a[0]; }
  public static int throwAfterRead(int[] a, Throwable failure) throws Throwable {
    int x = a[0]; if (x > 0) throw failure; return x;
  }
}
