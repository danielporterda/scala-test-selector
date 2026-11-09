package admissioncase;

interface Contract {
  Box aGet();
  int unused00(); int unused01(); int unused02(); int unused03();
  int unused04(); int unused05(); int unused06(); int unused07();
}
class Getter implements Contract {
  private Box cached;
  public Box aGet() { return lazyHelper(); }
  private Box lazyHelper() {
    if (cached == null) cached = new Box();
    Effects.changed();
    return cached;
  }
  public int unused00() { return 0; } public int unused01() { return 1; }
  public int unused02() { return 2; } public int unused03() { return 3; }
  public int unused04() { return 4; } public int unused05() { return 5; }
  public int unused06() { return 6; } public int unused07() { return 7; }
}
class Box {
  final int ready;
  Box() { ready = Effects.changed(); }
}
class Effects {
  static int hits;
  public static int changed() { return ++hits; }
}
class Closed { public static int scalar() { return 17; } }
interface VirtualContract { int m(); }
class Base implements VirtualContract { public int m() { return -1; } }
class Child extends Base { public int m() { return Effects.changed(); } }
class Factory {
  public static Contract make() { return new Getter(); }
  public static Box invoke(Contract receiver) { return receiver.aGet(); }
  public static Box entry() { return invoke(make()); }
  public static int invokeBase(Base receiver) { return receiver.m(); }
  public static int childEntry() { return invokeBase(new Child()); }
}

/** Actual JVM observation; Rust tests supply a normalized demand inventory. */
public final class Fixture {
  public static void main(String[] args) {
    Getter getter = new Getter();
    Box first = getter.aGet();
    Box second = getter.aGet();
    System.out.println("lazy:" + (first == second) + ":" + first.ready + ":" + Effects.hits);
    Box entry = Factory.entry();
    System.out.println("entry:" + entry.ready + ":" + Effects.hits);
    int child = Factory.childEntry();
    System.out.println("override:" + child + ":" + new Base().m() + ":" + Effects.hits);
    System.out.println("scalar:" + Closed.scalar() + ":" + Effects.hits);
  }
}
