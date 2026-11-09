package aliascase;

public class Probe {
    public Object value;
    public Object left;
    public Object right;
    public int calls;
    public static Object global;
    public Probe(Object left, Object right) { this.left = left; this.right = right; }
    public void initialize() { calls++; value = left; }
    public Object lazy() { if (value == null) initialize(); return value; }
    public Object choose(boolean branch) { return branch ? left : right; }
    public Object chooseArgs(boolean branch, Object first, Object second) { return branch ? first : second; }
    public Object scalarPredicate(int n, Object first, Object second) { return (n & 1) == 0 ? first : second; }
    public Object mergedField(boolean branch, Probe first, Probe second) {
        Probe alias = branch ? first : second;
        return alias.value;
    }
    public Object mergedCall(boolean branch, Probe first, Probe second) {
        Probe alias = branch ? first : second;
        return alias.lazy();
    }
    public Object mergedStore(boolean branch, Object first, Object second) {
        Object alias = branch ? first : second;
        global = alias;
        return alias;
    }
    public Object throwing(boolean branch) {
        if (branch) { initialize(); global = right; throw new IllegalStateException(); }
        return left;
    }
    public Object loop(int count) { while (count-- > 0) initialize(); return left; }
    public Object caught(boolean branch) {
        try { if (branch) throw new IllegalStateException(); return left; }
        catch (IllegalStateException exception) { global = right; return right; }
    }
    public Object unknownBranch(boolean branch, Object[] values) { return branch ? left : values[0]; }
    public Object literal(boolean branch) { return branch ? "literal" : Probe.class; }
    public native Object opaque();
    public Object mixed(boolean branch) { return branch ? left : opaque(); }
    public Object reflecting(boolean branch) throws ClassNotFoundException {
        if (branch) Class.forName("aliascase.Probe");
        global = left;
        return left;
    }
    public static void main(String[] args) {
        Probe first = new Probe("left", "right");
        Probe second = new Probe("other", "last");
        boolean lazy = first.lazy() == first.left && first.calls == 1;
        lazy &= first.lazy() == first.left && first.calls == 1;
        second.value = second.right;
        boolean branches = first.choose(true) == first.left && first.choose(false) == first.right;
        boolean field = first.mergedField(false, first, second) == second.right;
        boolean call = first.mergedCall(false, first, second) == second.right;
        boolean store = first.mergedStore(false, first.left, second.right) == global && global == second.right;
        try { first.throwing(true); } catch (IllegalStateException expected) { }
        boolean thrown = first.calls == 2 && global == first.right;
        boolean caught = first.caught(true) == first.right && global == first.right;
        boolean literal = first.literal(true).equals("literal") && first.literal(false) == Probe.class;
        System.out.println("lazy:" + lazy + ",branches:" + branches + ",field:" + field
            + ",call:" + call + ",store:" + store + ",throw:" + thrown + ",catch:" + caught + ",literal:" + literal);
        if (!(lazy && branches && field && call && store && thrown && caught && literal)) throw new AssertionError();
    }
}
