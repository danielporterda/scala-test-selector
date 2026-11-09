package valuebounds;
public final class Opaque {
  public static Narrow narrow() { return new Allowed(); }
  public static Base broad() { return new Allowed(); }
  @SuppressWarnings("unchecked") public static <T extends Narrow> T generic() { return (T)new Allowed(); }
  @SuppressWarnings("unchecked") public static <T extends Narrow & Marker> T intersection() { return (T)new Allowed(); }
}
