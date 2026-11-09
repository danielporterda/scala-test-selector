package hierarchycase;
public final class Factory {
  public interface Contract { int value(); }
  public static class Base {}
  public static final class A extends Base implements Contract { public int value() { return 1; } }
  public static final class B implements Contract { public int value() { return 2; } }
  public static A echo(A value) { return value; }
  public static int caller(A value) { Contract receiver = echo(value); return receiver.value(); }
  public static String objectText(A value) { return value.toString(); }
  public static void main(String[] args) {
    System.out.println("caller:" + caller(new A()));
    System.out.println("B:" + new B().value());
    System.out.println("A-parent:" + A.class.getSuperclass().getName());
    String text = objectText(new A());
    if (!text.startsWith("hierarchycase.Factory$A@")) throw new AssertionError(text);
    System.out.println("object-method:class-name-prefix");
  }
}
