package lntcase;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Path;
import java.lang.reflect.InvocationTargetException;
import java.security.MessageDigest;
import java.util.HexFormat;

public final class Observe {
    private static final class Loader extends URLClassLoader {
        boolean targetLoaded;
        Loader(Path directory) throws Exception { super(new URL[]{directory.toUri().toURL()}, null); }
        @Override protected Class<?> loadClass(String name, boolean resolve) throws ClassNotFoundException {
            if (name.equals("lntcase.Probe")) targetLoaded = true;
            return super.loadClass(name, resolve);
        }
    }
    public static void main(String[] arguments) throws Exception {
        try (Loader loader = new Loader(Path.of(arguments[0]))) {
            // Read the class bytes before loading Probe or invoking its methods.
            byte[] bytes = loader.getResourceAsStream("lntcase/Probe.class").readAllBytes();
            System.out.println("resource:" + HexFormat.of().formatHex(MessageDigest.getInstance("SHA-256").digest(bytes)));
            System.out.println("loaded-before-resource:" + loader.targetLoaded);
            Class<?> target = Class.forName("lntcase.Probe", true, loader);
            System.out.println("value:" + target.getMethod("value", int.class).invoke(null, 4));
            System.out.println("state:" + target.getField("state").get(null));
            try { target.getMethod("fail").invoke(null); }
            catch (InvocationTargetException failure) {
                StackTraceElement[] stack = failure.getCause().getStackTrace();
                System.out.println("stack-origin:" + stack[0].getClassName());
                StackTraceElement frame = java.util.Arrays.stream(stack)
                    .filter(f -> f.getClassName().equals("lntcase.Probe")).findFirst().orElseThrow();
                System.out.println("stack:" + frame.getClassName() + ":" + frame.getMethodName() + ":" + frame.getLineNumber());
            }
        }
    }
}
