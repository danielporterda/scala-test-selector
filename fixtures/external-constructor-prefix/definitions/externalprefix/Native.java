package externalprefix;

public final class Native {
  public static String trace = "";
  public final int value;
  public static void note(String value) { trace = trace.isEmpty() ? value : trace + "," + value; }
  public static void reset() { trace = ""; }
  public Native(String value) { note("ctor-string:" + value); this.value = value.length(); }
  public Native(int value) { note("ctor-int:" + value); this.value = value; }
}
