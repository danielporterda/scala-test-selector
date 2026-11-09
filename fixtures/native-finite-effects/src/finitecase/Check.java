package finitecase;
public final class Check {
  static int effects;
  interface Throwing { void run() throws Throwable; }
  static void observed(String label, Throwing action, Class<?> expected) {
    try { action.run(); throw new AssertionError(label + " did not throw"); }
    catch (Throwable failure) {
      if (failure.getClass() != expected) throw new AssertionError(label, failure);
      System.out.println(label + ":" + failure.getClass().getSimpleName());
    }
  }
  public static void main(String[] args) throws Throwable {
    Object reference = new Object();
    if (Probe.readInt(new int[]{7},0)!=7 || Probe.readLong(new long[]{8},0)!=8 ||
        Probe.readFloat(new float[]{9},0)!=9 || Probe.readDouble(new double[]{10},0)!=10 ||
        Probe.readReference(new Object[]{reference},0)!=reference || Probe.readByte(new byte[]{11},0)!=11 ||
        !Probe.readBoolean(new boolean[]{true},0) || Probe.readChar(new char[]{'Q'},0)!='Q' ||
        Probe.readShort(new short[]{12},0)!=12) throw new AssertionError("load matrix");
    System.out.println("loads:all-nine");
    if (Probe.newBoolean(1).length!=1 || Probe.newByte(1).length!=1 || Probe.newChar(1).length!=1 ||
        Probe.newShort(1).length!=1 || Probe.newInt(1).length!=1 || Probe.newLong(1).length!=1 ||
        Probe.newFloat(1).length!=1 || Probe.newDouble(1).length!=1 || Probe.newReference(1).length!=1 ||
        Probe.newMultiPrimitive(1,1)[0].length!=1 || Probe.newMultiReference(1,1)[0].length!=1 ||
        Probe.length(new int[3])!=3 || Probe.referenceLength(new Object[4])!=4) throw new AssertionError("allocation matrix");
    System.out.println("new-and-length:all-types");
    int[] a={0}; long[] b={0}; float[] c={0}; double[] d={0}; Object[] e={null};
    byte[] f={0}; boolean[] g={true}; char[] h={0}; short[] j={0};
    Probe.writeInt(a,0,5); Probe.writeLong(b,0,6); Probe.writeFloat(c,0,7); Probe.writeDouble(d,0,8);
    Probe.writeReference(e,0,reference); Probe.writeByte(f,0,(byte)9); Probe.writeBoolean(g,0,false);
    Probe.writeChar(h,0,'R'); Probe.writeShort(j,0,(short)10);
    if(a[0]!=5||b[0]!=6||c[0]!=7||d[0]!=8||e[0]!=reference||f[0]!=9||g[0]||h[0]!='R'||j[0]!=10) throw new AssertionError("store matrix");
    System.out.println("stores:all-nine");
    observed("null-load",()->Probe.readInt(null,0),NullPointerException.class);
    observed("bounds-load",()->Probe.readInt(new int[0],0),ArrayIndexOutOfBoundsException.class);
    observed("null-length",()->Probe.length(null),NullPointerException.class);
    observed("negative-new",()->Probe.newInt(-1),NegativeArraySizeException.class);
    observed("zero-divide",()->Probe.divideInt(1,0),ArithmeticException.class);
    observed("zero-remainder",()->Probe.remainderLong(1,0),ArithmeticException.class);
    Runnable callback=()->effects++;
    int p=Probe.branchAndCatch(true,new int[]{7},0,callback);
    int q=Probe.branchAndCatch(false,new int[]{7},0,callback);
    int r=Probe.branchAndCatch(true,null,0,callback);
    int s=Probe.catchDivision(1,0,callback);
    int t=Probe.catchNegative(-1,callback);
    if(p!=7||q!=7||r!=-1||s!=-1||t!=-1||effects!=4||Probe.shared!=4) throw new AssertionError("handler effects");
    System.out.println("handlers:7:7:-1:-1:-1:callbacks=4:shared=4");
    if(Probe.writeAfterAllocation(2)!=2||Probe.shared!=6) throw new AssertionError("later effect");
    if(Probe.callbackAfterRead(new int[]{7},callback)!=7||effects!=5||Probe.monitorAfterRead(new int[]{7},new Object())!=7) throw new AssertionError("consumer effects");
    observed("native",()->Probe.nativeAfterRead(new int[]{7}),UnsatisfiedLinkError.class);
    if(Probe.reflectAfterRead(new int[]{7},"java.lang.String")!=String.class||!Probe.dynamicAfterRead(new int[]{7}).equals("n=7")) throw new AssertionError("dynamic controls");
    Throwable thrown=new Throwable("identity");
    try { Probe.throwAfterRead(new int[]{7},thrown); throw new AssertionError("throw missing"); }
    catch(Throwable actual) { if(actual!=thrown)throw new AssertionError("throw identity"); }
    System.out.println("consumers:later-store-call:callback:monitor:native:reflection:dynamic:throw-identity");
  }
}
