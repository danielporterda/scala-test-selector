package finitecase;
import java.lang.management.ManagementFactory;
import com.sun.management.HotSpotDiagnosticMXBean;
/** Optimization observations only: neither reuse nor freshness is asserted. */
public final class Warm {
  static volatile int zero;
  static int divide() { return 1/zero; }
  static int load(int[] values) { return values[zero+1]; }
  static int nullLoad(int[] values) { return values[zero]; }
  static void diagnostic(String name, int iterations) {
    Throwable previous=null, first=null; int caught=0, repeated=0, sameFirst=0;
    int[] values={7};
    for(int i=0;i<iterations;i++) {
      try { if(name.equals("divide"))divide(); else if(name.equals("bounds"))load(values); else nullLoad(null); }
      catch(ArithmeticException|ArrayIndexOutOfBoundsException|NullPointerException failure) {
        caught++; if(first==null)first=failure;
        if(failure==previous)repeated++; if(failure==first)sameFirst++; previous=failure;
      }
    }
    if(caught!=iterations)throw new AssertionError("missing expected exceptions");
    System.out.println(name+":caught="+caught+":same-previous="+repeated+":same-first="+sameFirst+
        ":last-trace="+previous.getStackTrace().length);
  }
  public static void main(String[] args) {
    System.out.println("vm="+System.getProperty("java.vm.name")+":"+System.getProperty("java.runtime.version"));
    System.out.println("arguments="+ManagementFactory.getRuntimeMXBean().getInputArguments());
    try { System.out.println("OmitStackTraceInFastThrow="+ManagementFactory.getPlatformMXBean(HotSpotDiagnosticMXBean.class).getVMOption("OmitStackTraceInFastThrow").getValue()); }
    catch(RuntimeException unsupported) { System.out.println("OmitStackTraceInFastThrow=unavailable"); }
    int iterations=Integer.parseInt(args[0]);
    diagnostic("divide",iterations); diagnostic("bounds",iterations); diagnostic("null",iterations);
  }
}
