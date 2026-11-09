package registrationcase;
public final class OpaqueSink {
  public static void accept(scala.Function0<?> callback) {
    if (Boolean.getBoolean("registrationcase.executeOpaque")) callback.apply();
  }
}
