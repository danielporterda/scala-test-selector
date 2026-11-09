package admissioncase;
public final class ShadowCheck {
  public static void main(String[] args) {
    System.out.println("shadow:" + (Factory.entry() == null) + ":" + Effects.hits);
  }
}
