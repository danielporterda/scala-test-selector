package envelopecase;

public final class CheckProbe {
  private static void observed(String name, int value) {
    System.out.println(name + ":" + value + ":" + Probe.hits());
    Probe.reset();
  }
  public static void main(String[] args) throws Exception {
    observed("branch-false", Probe.branch(false));
    observed("branch-true", Probe.branch(true));
    observed("sparse-hit", Probe.sparseSwitch(7));
    observed("sparse-miss", Probe.sparseSwitch(8));
    observed("dense-hit", Probe.denseSwitch(1));
    observed("dense-miss", Probe.denseSwitch(0));
    observed("catch-hit", Probe.caught(true));
    observed("catch-miss", Probe.caught(false));
    observed("scalar", Probe.disjointScalar(7));
    observed("disjoint-entry", Probe.disjointEntry());
    observed("branch-entry", Probe.branchEntry());
    observed("scalar-component-entry", Probe.Scalar.disjointEntry());
    Probe.escape(() -> { for (int i=0; i<100; ++i) Probe.changed(); });
    System.out.println("escape-before:" + Probe.hits());
    Probe.invokeEscaped();
    System.out.println("escape-after:" + Probe.hits());
    Probe.reset();
    System.out.println("reflection:" + Probe.reflection("java.lang.String").getName());
    try { Probe.invokesMissing(); throw new AssertionError("native implementation unexpectedly available"); }
    catch (UnsatisfiedLinkError expected) { System.out.println("native-missing:UnsatisfiedLinkError"); }
    System.out.println("array:" + Probe.array(new int[]{9}));
    Probe.monitor(new Object());
    System.out.println("monitor:" + Probe.hits());
    if (Probe.hits() != 1) throw new AssertionError("monitor execution receipt");
  }
}
