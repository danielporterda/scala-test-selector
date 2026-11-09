package lntcase;
public final class Thrower {
    public static void fail() { throw new IllegalStateException("marker"); }
}
