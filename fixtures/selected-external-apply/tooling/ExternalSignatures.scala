import java.nio.file.{Files, Paths}
import java.security.MessageDigest
import scala.jdk.CollectionConverters._
import scala.meta.cli.Reporter
import scala.meta.io.{AbsolutePath, Classpath}
import scala.meta.metacp.Settings
import scala.meta.internal.classpath.{ClasspathIndex, CompressedClassfile}
import scala.meta.internal.metacp._
import scala.meta.internal.scalacp.{SymbolIndex, SymlinkChildren}
import scala.meta.internal.semanticdb._
import scala.tools.scalap.scalax.rules.scalasig.SymbolInfoSymbol

/** Fixture metadata only: no source definitions or executable-body claims. */
object ExternalSignatures {
  def hash(bytes: Array[Byte]): String = MessageDigest.getInstance("SHA-256").digest(bytes).map(b => f"${b & 255}%02x").mkString
  def quote(s: String): String = "\"" + s.flatMap {
    case '\\' => "\\\\"; case '"' => "\\\""; case '\n' => "\\n"; case '\r' => "\\r"; case '\t' => "\\t"
    case c if c < ' ' => f"\\u${c.toInt}%04x"; case c => c.toString
  } + "\""
  def main(args: Array[String]): Unit = {
    require(args.length == 5, "orderedClasspath outerClass expectedHash exactRequests outputPrefix")
    val paths = Files.readAllLines(Paths.get(args(0))).asScala.toList.filter(_.nonEmpty)
    val requests = Files.readAllLines(Paths.get(args(3))).asScala.toList.filter(_.nonEmpty)
    require(requests.nonEmpty && requests.distinct.size == requests.size)
    val cp = Classpath(paths.map(AbsolutePath(_)))
    val settings = Settings().withClasspath(cp).withDependencyClasspath(Classpath(Nil))
      .withStubBrokenSignatures(false).withUsejavacp(false).withIncludeJdk(false)
      .withScalaLibrarySynthetics(false).withPar(false).withLogBrokenSignatures(true)
    val index = ClasspathIndex(cp, false)
    val selected = index.getClassfile(args(1) + ".class").getOrElse(sys.error("requested class absent"))
    val stream = selected.openInputStream()
    val bytes = try stream.readAllBytes() finally stream.close()
    require(hash(bytes) == args(2), "selected provider hash mismatch")
    val sig = selected.toClassNode.scalaSig.getOrElse(sys.error("ScalaSig required; Java fallback prohibited"))
    val converter = prototype.DemandConverter.create(sig, SymbolIndex(index), settings, Reporter())
    val symbols = sig.scalaSig.symbols.collect { case s: SymbolInfoSymbol => s }
    val rows = scala.collection.mutable.LinkedHashMap.empty[String, SymbolInformation]
    val methods = requests.map { request =>
      val matching = symbols.filter(s => converter.XtensionSymbolSSymbol(s).toSemantic == request)
      require(matching.size == 1, "requested compiler identity absent or ambiguous: " + request)
      val info = converter.XtensionGSymbolSSymbolInformation(matching.head).toSymbolInformation(SymlinkChildren)
      require(info.symbol == request && info.language == Language.SCALA)
      val method = info.signature match { case m: MethodSignature => m; case _ => sys.error("method signature required") }
      rows.put(info.symbol, info)
      val formals = method.parameterLists.zipWithIndex.flatMap { case (clause, c) =>
        clause.symlinks.zipWithIndex.map { case (symbol, ordinal) =>
          val raw = symbols.filter(s => converter.XtensionSymbolSSymbol(s).toSemantic == symbol)
          require(raw.size == 1, "formal missing or ambiguous: " + symbol)
          val formal = converter.XtensionGSymbolSSymbolInformation(raw.head).toSymbolInformation(SymlinkChildren)
          require(formal.symbol == symbol && formal.language == Language.SCALA)
          val tpe = formal.signature match { case v: ValueSignature => v.tpe; case _ => sys.error("value signature required") }
          rows.put(symbol, formal)
          "{" + Seq("symbol" -> quote(symbol), "name" -> quote(formal.displayName), "clause" -> c.toString,
            "ordinal" -> ordinal.toString, "default" -> ((formal.properties & SymbolInformation.Property.DEFAULT.value) != 0).toString,
            "implicit" -> ((formal.properties & SymbolInformation.Property.IMPLICIT.value) != 0).toString,
            "by_name" -> tpe.isInstanceOf[ByNameType].toString, "repeated" -> tpe.isInstanceOf[RepeatedType].toString)
            .map { case (k,v) => quote(k) + ":" + v }.mkString(",") + "}"
        }
      }
      "{" + quote("symbol") + ":" + quote(request) + "," + quote("formals") + ":" + formals.mkString("[",",","]") + "}"
    }
    require(rows.nonEmpty && rows.values.forall(_.language == Language.SCALA))
    val documents = TextDocuments(Seq(TextDocument(schema=Schema.SEMANTICDB4, uri=args(1)+".class", language=Language.SCALA, symbols=rows.values.toVector)))
    Files.write(Paths.get(args(4)+".semanticdb"), documents.toByteArray)
    Files.writeString(Paths.get(args(4)+".textproto"), documents.toProtoString)
    val provider = selected match { case c: CompressedClassfile => c.zip.getAbsolutePath + "!/" + c.entry.getName; case x => x.toString }
    val json = "{" + quote("provider")+":"+quote(provider)+","+quote("class_sha256")+":"+quote(hash(bytes))+","+quote("jdk_object_in_index")+":"+index.getClassfile("java/lang/Object.class").nonEmpty.toString+","+quote("methods")+":"+methods.mkString("[",",","]")+"}\n"
    Files.writeString(Paths.get(args(4)+".json"), json)
    print(json)
  }
}
