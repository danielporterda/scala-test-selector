package metadatacase;

public final class Probe {
  public static final class Effects {
    public static int bits = 0;
    public static int changedCalls = 0;
    public static int note(int bit) { bits |= bit; return bits; }
    public static int changed() { changedCalls++; return 7; }
  }
  public interface Marker { int MARKER = Effects.note(1); }
  public interface Child extends Marker {
    int CHILD = Effects.note(2) + Effects.changed();
    static int ping() { return Effects.changed(); }
    static int opaque() { return Missing.value(); }
  }
  public interface DefaultParent {
    int DEFAULT = Effects.note(4);
    default int value() { return 1; }
  }
  public static final class DefaultChild implements DefaultParent {
    static int OWN = Effects.note(8) + Effects.changed();
    public static int ping() { return Effects.changed(); }
  }
  public static class SuperParent {
    static int PARENT = Effects.note(16);
    public SuperParent() { Effects.note(64); }
  }
  public static final class SuperChild extends SuperParent {
    static int OWN = Effects.note(32) + Effects.changed();
    public SuperChild() { super(); }
    public static int ping() { return Effects.changed(); }
  }
  public static final class Missing { public static int value() { return 11; } }
  public static void main(String[] args) {
    int value;
    switch (args[0]) {
      case "child": value = Child.ping(); break;
      case "default": value = DefaultChild.ping(); break;
      case "super-static": value = SuperChild.ping(); break;
      case "super-constructor": new SuperChild(); value = 0; break;
      case "missing": value = Child.opaque(); break;
      default: throw new IllegalArgumentException(args[0]);
    }
    System.out.println(args[0] + ":" + Effects.bits + ":" + Effects.changedCalls + ":" + value);
  }
}
