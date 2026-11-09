package lntcase;

@Marker(1)
public final class Probe {
    private static final int ONE = 1;
    private static final int TWO = 2;
    public static int state = 7;

    public static int value(int x) {
        return x + 4;
    }

    public static void fail() {
        Thrower.fail();
    }
}
