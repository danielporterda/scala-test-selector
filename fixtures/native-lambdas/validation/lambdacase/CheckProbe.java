package lambdacase;

public final class CheckProbe {
  public static void main(String[] args) {
    Probe probe = new Probe();
    Runnable staticValue = Probe.staticClosure(3);
    Runnable receiverValue = probe.receiverClosure(5);
    Runnable boundValue = probe.boundClosure();
    System.out.println("deferred:" + Probe.staticEffects() + ":" + probe.receiverEffects());
    staticValue.run();
    System.out.println("static:" + Probe.staticEffects() + ":" + probe.receiverEffects());
    receiverValue.run();
    System.out.println("receiver:" + Probe.staticEffects() + ":" + probe.receiverEffects());
    boundValue.run();
    System.out.println("bound:" + Probe.staticEffects() + ":" + probe.receiverEffects());
    probe.unsupportedThenStore(9);
    System.out.println("opaque-followed-by-store:" + probe.stored());
    Probe wrapped = new Probe();
    Probe.runStatic();
    wrapped.runReceiver();
    wrapped.runBound();
    System.out.println("native-wrappers:" + Probe.staticEffects() + ":" + wrapped.receiverEffects());
    Runnable separate = Probe.separateStaticClosure();
    System.out.println("target-created:" + Probe.targetInitializations() + ":" + Probe.targetEffects());
    separate.run();
    System.out.println("target-run:" + Probe.targetInitializations() + ":" + Probe.targetEffects());
    Probe.runSeparate();
    System.out.println("target-wrapper:" + Probe.targetInitializations() + ":" + Probe.targetEffects());
    java.util.function.Consumer<Probe> unbound = Probe.unbound();
    System.out.println("unbound-created:" + probe.receiverEffects());
    unbound.accept(probe);
    System.out.println("unbound-run:" + probe.receiverEffects());
    if (Probe.targetInitializations() != 1 || Probe.targetEffects() != 2
        || Probe.staticEffects() != 6 || probe.receiverEffects() != 7
        || wrapped.receiverEffects() != 6 || probe.stored() != 9) {
      throw new AssertionError("independent JVM lambda effects/order mismatch");
    }
  }
}
