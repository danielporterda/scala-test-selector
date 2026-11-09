package envelopecase;

public final class CheckShadow {
  public static void main(String[] args) {
    int result = Probe.branch(true);
    if (result != 0) throw new AssertionError("selected shadow bytes");
    System.out.println("shadow:" + result);
  }
}
