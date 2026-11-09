package selector.metadata;

/** Pinned bridge to the bytecode-public, Scala-source-private constructor. */
public final class DemandConverter {
  private DemandConverter() {}
  public static scala.meta.internal.scalacp.Scalacp create(
      scala.meta.internal.scalacp.ScalaSigNode node,
      scala.meta.internal.scalacp.SymbolIndex index,
      scala.meta.metacp.Settings settings,
      scala.meta.cli.Reporter reporter) {
    return new scala.meta.internal.scalacp.Scalacp(node, index, settings, reporter);
  }
}
