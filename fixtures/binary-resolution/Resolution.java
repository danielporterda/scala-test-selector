package fixture;

class ResolveBase {
  public static Object shared = new Object();
  public ResolveBase() {}
  public ResolveBase(Object value) {}
  public Object inherited() { return this; }
  public Object overload(int value) { return null; }
  public Object overload(String value) { return value; }
  public Object ping() { return "base"; }
  public static Object staticInherited() { return shared; }
}
class ResolveMid extends ResolveBase {
  public Object ping() { return "mid"; }
}
class ResolveLeaf extends ResolveMid {
  public Object invokeInherited() { return inherited(); }
  public Object invokeSuper() { return super.ping(); }
  public static Object readInherited() { return ResolveLeaf.shared; }
  public static Object invokeStatic() { return ResolveLeaf.staticInherited(); }
  public static Object allocateWithCall() { return new InitArgument(ResolveBase.staticInherited()); }
}
class InitArgument { InitArgument(Object value) {} }
interface DefaultTop {
  default Object choose() { return "top"; }
  static Object staticOnly() { return null; }
}
interface DefaultOne extends DefaultTop {
  default Object choose() { return "one"; }
}
interface DefaultTwo extends DefaultTop {
  default Object choose() { return "two"; }
}
class DefaultLeaf implements DefaultTop, DefaultOne {
  public Object invokeDefault() { return DefaultOne.super.choose(); }
}
interface AbstractOne { Object choose(); }
interface AbstractTwo { Object choose(); }
abstract class AbstractLeaf implements AbstractOne, AbstractTwo {}
interface FieldTop { Object shared = new Object(); }
interface FieldOne extends FieldTop {}
interface FieldTwo { Object shared = new Object(); }
class FieldLeaf implements FieldOne {}
class FieldBoth implements FieldOne, FieldTwo {}
class FieldOverride extends ResolveBase implements FieldOne {
  public static Object shared = new Object();
}
class FieldBeforeParent extends ResolveBase implements FieldOne {}

public final class Resolution {
  public static void main(String[] args) throws Exception {
    ResolveLeaf leaf = new ResolveLeaf();
    System.out.println("inherited=" + ResolveLeaf.class.getMethod("inherited").getDeclaringClass().getName());
    System.out.println("staticMethod=" + ResolveLeaf.class.getMethod("staticInherited").getDeclaringClass().getName());
    System.out.println("staticField=" + ResolveLeaf.class.getField("shared").getDeclaringClass().getName());
    System.out.println("defaultMethod=" + DefaultLeaf.class.getMethod("choose").getDeclaringClass().getName());
    System.out.println("defaultResult=" + new DefaultLeaf().invokeDefault());
    System.out.println("superResult=" + leaf.invokeSuper());
    System.out.println("fieldBeforeParent=" + FieldBeforeParent.class.getField("shared").getDeclaringClass().getName());
    System.out.println("fieldOverride=" + FieldOverride.class.getField("shared").getDeclaringClass().getName());
  }
}
