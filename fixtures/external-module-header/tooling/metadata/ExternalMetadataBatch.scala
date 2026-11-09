import java.nio.file.{Files, Paths}
import java.security.MessageDigest
import scala.jdk.CollectionConverters._
import scala.collection.mutable
import scala.meta.cli.Reporter
import scala.meta.io.{AbsolutePath, Classpath}
import scala.meta.metacp.Settings
import scala.meta.internal.classpath.ClasspathIndex
import scala.meta.internal.metacp._
import scala.meta.internal.scalacp.{SymbolIndex, SymlinkChildren}
import scala.meta.internal.semanticdb._
import scala.tools.scalap.scalax.rules.scalasig.{ClassSymbol, ObjectSymbol, SymbolInfoSymbol}

/** Demand-only signatures. One immutable classpath index for a whole batch.
  * There is deliberately no Javacp, broken-signature stub, JDK, or body export.
  */
object ExternalMetadataBatch {
  def hash(bytes: Array[Byte]): String = MessageDigest.getInstance("SHA-256")
    .digest(bytes).map(b => f"${b & 255}%02x").mkString
  def quote(s: String): String = "\"" + s.flatMap {
    case '\\' => "\\\\"; case '"' => "\\\""; case '\n' => "\\n"
    case '\r' => "\\r"; case '\t' => "\\t"
    case c if c < ' ' => f"\\u${c.toInt}%04x"; case c => c.toString
  } + "\""
  def obj(fields: (String, String)*): String = fields.map { case (k,v) => quote(k)+":"+v }.mkString("{",",","}")
  def failure(t: Throwable): String = Option(t.getMessage).getOrElse(t.getClass.getName).take(2048)
  def main(args: Array[String]): Unit = {
    require(args.length == 3, "orderedClasspath batchTSV outputDirectory")
    val paths = Files.readAllLines(Paths.get(args(0))).asScala.toList.filter(_.nonEmpty)
    val tasks = Files.readAllLines(Paths.get(args(1))).asScala.toVector.filter(_.nonEmpty)
    require(tasks.size <= 4096, "outer class task limit")
    val cp = Classpath(paths.map(AbsolutePath(_)))
    val settings = Settings().withClasspath(cp).withDependencyClasspath(Classpath(Nil))
      .withStubBrokenSignatures(false).withUsejavacp(false).withIncludeJdk(false)
      .withScalaLibrarySynthetics(false).withPar(false).withLogBrokenSignatures(true)
    val index = ClasspathIndex(cp, false)
    val symbolIndex = SymbolIndex(index)
    val out = Paths.get(args(2)); Files.createDirectories(out)
    val classes = tasks.zipWithIndex.map { case (line, ordinal) =>
      val fields = line.split("\t", -1).toVector
      require(fields.size >= 3 && fields.size <= 4098, "malformed bounded batch task")
      val outer = fields(0); val expected = fields(1)
      val tagged = fields(2).startsWith("@")
      val header = tagged && fields(2) == "@module_header"
      require(!tagged || header || fields(2) == "@method", "unknown metadata task scope")
      val requests = fields.drop(if(tagged) 3 else 2)
      require(requests.nonEmpty, "empty metadata task")
      require(requests.distinct.size == requests.size, "duplicate requested root")
      var methods = Vector.empty[String]
      var payload: Option[String] = None
      var classFailure: Option[String] = None
      try {
        val selected = index.getClassfile(outer + ".class").getOrElse(sys.error("requested class absent"))
        val stream = selected.openInputStream()
        val bytes = try stream.readAllBytes() finally stream.close()
        require(bytes.length <= 16*1024*1024 && hash(bytes) == expected, "selected class hash mismatch or size bound")
        val sig = selected.toClassNode.scalaSig.getOrElse(sys.error("ScalaSig required; Java fallback prohibited"))
        val converter = selector.metadata.DemandConverter.create(sig, symbolIndex, settings, Reporter())
        val raw = mutable.HashMap.empty[String, mutable.ArrayBuffer[SymbolInfoSymbol]]
        sig.scalaSig.symbols.collect { case s: SymbolInfoSymbol => s }.foreach { s =>
          // Some compiler-internal symbols have no SemanticDB encoding; they are
          // not requested declarations and cannot become substitute identities.
          try { val name = converter.XtensionSymbolSSymbol(s).toSemantic
            raw.getOrElseUpdate(name, mutable.ArrayBuffer.empty) += s
          } catch { case _: Exception => () }
        }
        val converted = mutable.HashMap.empty[String, SymbolInformation]
        def info(name: String): SymbolInformation = converted.getOrElseUpdate(name, {
          val matches = raw.getOrElse(name, mutable.ArrayBuffer.empty)
          require(matches.size == 1, "exact compiler identity absent or ambiguous: " + name)
          val row = converter.XtensionGSymbolSSymbolInformation(matches.head).toSymbolInformation(SymlinkChildren)
          require(row.symbol == name && row.language == Language.SCALA, "non-SCALA or rewritten identity")
          row
        })
        val rows = mutable.TreeMap.empty[String, SymbolInformation]
        methods = requests.map { request =>
          try {
            val selectedRows = mutable.TreeMap.empty[String, SymbolInformation]
            if(header) {
              require(request.endsWith(".") && !request.endsWith(").") && !request.startsWith("@"), "module term identity required")
              val matches = raw.getOrElse(request, mutable.ArrayBuffer.empty)
              require(matches.nonEmpty, "exact compiler module absent")
              require(matches.size == 1 || (matches.size == 2 &&
                matches.exists(_.isInstanceOf[ObjectSymbol]) && matches.exists(_.isInstanceOf[ClassSymbol])),
                "ambiguous compiler module declarations")
              // Scala pickle may encode one module as ObjectSymbol and ClassSymbol.
              // Only identical projected OBJECT headers are duplicates; methods
              // retain their original exact-one declaration contract above.
              val projected = matches.map { symbol =>
                val original = converter.XtensionGSymbolSSymbolInformation(symbol).toSymbolInformation(SymlinkChildren)
                require(original.symbol == request && original.language == Language.SCALA && original.kind == SymbolInformation.Kind.OBJECT,
                  "non-SCALA, aliased, or non-OBJECT module identity")
                SymbolInformation(symbol=original.symbol, language=Language.SCALA,
                  kind=SymbolInformation.Kind.OBJECT, displayName=original.displayName)
              }
              val root = projected.head
              require(projected.forall(_.toByteArray.sameElements(root.toByteArray)), "conflicting compiler module headers")
              selectedRows(request) = root
            } else {
            val root = info(request)
            require(root.kind == SymbolInformation.Kind.METHOD || root.kind == SymbolInformation.Kind.CONSTRUCTOR,
              "requested declaration is not a method")
            val method = root.signature match { case m: MethodSignature => m; case _ => sys.error("method signature required") }
            selectedRows(request) = root
            val seen = mutable.HashSet.empty[String]
            def children(scope: Option[Scope], kind: SymbolInformation.Kind, owner: String): Unit = scope.foreach { s =>
              require(s.hardlinks.isEmpty, "hardlinked declaration scope prohibited")
              s.symlinks.foreach { name =>
                require(seen.add(name), "duplicate declaration/formal slot")
                val child = info(name)
                require(child.kind == kind && name.startsWith(owner), "wrong formal kind or owner")
                selectedRows(name) = child
                child.signature match {
                  case t: TypeSignature => children(t.typeParameters, SymbolInformation.Kind.TYPE_PARAMETER, name)
                  case _: ValueSignature if kind == SymbolInformation.Kind.PARAMETER => ()
                  case _ => sys.error("unsupported declared formal signature")
                }
              }
            }
            children(method.typeParameters, SymbolInformation.Kind.TYPE_PARAMETER, request)
            method.parameterLists.foreach(s => children(Some(s), SymbolInformation.Kind.PARAMETER, request))
            }
            val digest = MessageDigest.getInstance("SHA-256")
            selectedRows.values.foreach { row =>
              val b = row.toByteArray
              digest.update(java.nio.ByteBuffer.allocate(8).putLong(b.length.toLong).array()); digest.update(b)
            }
            val semanticHash = digest.digest().map(b => f"${b & 255}%02x").mkString
            selectedRows.foreach { case (name,row) =>
              rows.get(name).foreach(old => require(old == row, "conflicting shared formal")); rows(name)=row
            }
            obj("symbol"->quote(request), "success"->"true", "semantic_sha256"->quote(semanticHash),
              "rows"->selectedRows.size.toString)
          } catch { case e: Exception => obj("symbol"->quote(request), "success"->"false", "error"->quote(failure(e))) }
        }
        if(rows.nonEmpty) {
          val name = f"class-$ordinal%04d.semanticdb"
          Files.write(out.resolve(name), TextDocuments(Seq(TextDocument(schema=Schema.SEMANTICDB4,
            uri=outer+".class", language=Language.SCALA, symbols=rows.values.toVector))).toByteArray)
          payload = Some(name)
        }
      } catch { case e: Exception => classFailure = Some(failure(e)) }
      obj("outer_class"->quote(outer), "class_sha256"->quote(expected),
        "payload"->payload.map(quote).getOrElse("null"),
        "error"->classFailure.map(quote).getOrElse("null"), "methods"->methods.mkString("[",",","]"))
    }
    Files.writeString(out.resolve("result.json"), obj("schema"->quote("selector-external-metadata-batch/v1"),
      "jdk_object_in_index"->index.getClassfile("java/lang/Object.class").nonEmpty.toString,
      "classes"->classes.mkString("[",",","]"))+"\n")
  }
}
