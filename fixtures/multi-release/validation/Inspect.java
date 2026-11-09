import java.io.File;
import java.util.jar.JarFile;
import java.util.zip.ZipFile;

public final class Inspect {
  public static void main(String[] args) throws Exception {
    try (JarFile jar = new JarFile(new File(args[0]), false, ZipFile.OPEN_READ,
                                  Runtime.Version.parse(args[1]))) {
      System.out.println(jar.getJarEntry("mr/Probe.class").getRealName());
      System.out.println(jar.isMultiRelease());
    }
  }
}
