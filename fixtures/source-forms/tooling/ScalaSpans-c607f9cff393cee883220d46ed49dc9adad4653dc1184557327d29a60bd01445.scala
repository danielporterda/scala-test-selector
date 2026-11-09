import scala.meta._
import java.nio.file.{Files, Paths}
import java.nio.charset.StandardCharsets.UTF_8
import java.security.MessageDigest
import scala.collection.mutable

/** Native selector structural exporter derived from compiler-selector ScalaSpans.
  * No classpath, name-resolution, or PR-specific rules. */
object ScalaSpans {
  def sha(text: String): String = MessageDigest.getInstance("SHA-256")
    .digest(text.getBytes(UTF_8)).map(x => f"${x & 255}%02x").mkString
  def names(tree: Tree): Seq[String] = tree.collect {
    case n: Name if n.value.nonEmpty => n.value
  }.distinct.sorted
  def words(tree: Tree, start: Int, end: Int): Seq[String] = tree.tokens.iterator
    .filter(t => t.pos.start >= start && t.pos.end <= end)
    .filterNot(t => Set("Space", "Tab", "LF", "CR", "FF", "Comment", "BOF", "EOF")(t.productPrefix))
    .map(_.syntax).toSeq
  def outsideWords(tree: Tree, start: Int, end: Int, blocked: Seq[Tree]): Seq[String] = tree.tokens.iterator
    .filter(t => t.pos.start >= start && t.pos.end <= end)
    .filterNot(t => Set("Space", "Tab", "LF", "CR", "FF", "Comment", "BOF", "EOF")(t.productPrefix))
    .filterNot(t => blocked.exists(b => b.pos.start <= t.pos.start && t.pos.end <= b.pos.end))
    .map(_.syntax).toSeq
  def outsideRanges(start: Int, end: Int, blocked: Seq[Tree]): ujson.Arr = {
    var cursor = start
    val result = mutable.ArrayBuffer.empty[ujson.Obj]
    blocked.filter(t => t.pos.start >= start && t.pos.end <= end).sortBy(_.pos.start).foreach { t =>
      if (cursor < t.pos.start) result += ujson.Obj("start" -> cursor, "end" -> t.pos.start)
      cursor = math.max(cursor, t.pos.end)
    }
    if (cursor < end) result += ujson.Obj("start" -> cursor, "end" -> end)
    ujson.Arr.from(result)
  }
  def arr(xs: Seq[String]): ujson.Arr = ujson.Arr.from(xs)
  def allNodes(tree: Tree): Seq[Tree] = tree +: tree.children.flatMap(allNodes)
  def nestedDeclarations(tree: Tree): Seq[Tree] = allNodes(tree).filterNot(_ eq tree).collect {
    case t @ (_: Defn.Def | _: Decl.Def | _: Defn.Type | _: Decl.Type |
              _: Defn.Class | _: Defn.Trait | _: Defn.Object | _: Defn.Enum) => t
    case t: Defn.Val if t.mods.exists(_.isInstanceOf[Mod.Lazy]) => t
  }
  def range(tree: Tree): ujson.Obj = ujson.Obj("start" -> tree.pos.start, "end" -> tree.pos.end)
  def runtime(tree: Tree, kind: String, eager: Boolean): ujson.Obj =
    ujson.Obj("start" -> tree.pos.start, "end" -> tree.pos.end,
      "kind" -> kind, "eager" -> eager,
      "tokens" -> arr(outsideWords(tree, tree.pos.start, tree.pos.end, nestedDeclarations(tree))))
  def deferred(tree: Tree, body: Tree, kind: String): ujson.Obj = {
    val tokens = outsideWords(body, body.pos.start, body.pos.end, nestedDeclarations(body))
    def immediatePlaceholders(node: Tree): Seq[Term.Placeholder] = node match {
      case p: Term.Placeholder => Seq(p)
      case _: Term.Function | _: Term.AnonymousFunction | _: Term.PartialFunction | _: Term.Eta => Nil
      case _: Defn.Def | _: Decl.Def | _: Defn.Class | _: Defn.Trait |
           _: Defn.Object | _: Defn.Enum | _: Ctor.Secondary => Nil
      case _ => node.children.flatMap(immediatePlaceholders)
    }
    val (parameters, placeholders, unknowns): (Seq[Tree], Seq[Tree], Seq[String]) = tree match {
      case f: Term.Function =>
        val names = f.params.map(_.name)
        val usable = names.filter(n => n.value.nonEmpty && n.pos.start >= 0 && n.pos.end > n.pos.start)
        (usable, Nil, if (usable.size == names.size) Nil else Seq("function_parameter_without_name_range"))
      case _: Term.AnonymousFunction =>
        val holes = immediatePlaceholders(body).sortBy(_.pos.start)
        (Nil, holes, if (holes.nonEmpty) Nil else Seq("placeholder_parameter_ranges_unavailable"))
      case _: Term.PartialFunction => (Nil, Nil, Seq("partial_function_patterns_unsupported"))
      case _: Term.Eta => (Nil, Nil, Seq("eta_parameter_ranges_unavailable"))
      case _ => (Nil, Nil, Seq("deferred_parameter_form_unsupported"))
    }
    ujson.Obj("start" -> tree.pos.start, "end" -> tree.pos.end,
      "body_start" -> body.pos.start, "body_end" -> body.pos.end, "kind" -> kind,
      "body" -> arr(tokens), "body_hash" -> sha(tokens.mkString("\u0000")),
      "parameter_ranges" -> ujson.Arr.from(parameters.map(range)),
      "placeholder_ranges" -> ujson.Arr.from(placeholders.map(range)),
      "parameter_unknowns" -> arr(unknowns))
  }
  def arguments(argss: Seq[Seq[Term]]): ujson.Arr = ujson.Arr.from(
    argss.zipWithIndex.flatMap { case (clause, clauseIndex) =>
      clause.zipWithIndex.map { case (arg, argumentIndex) =>
        val (expression, label) = arg match {
          case a: Term.Assign => (a.rhs, Some(a.lhs))
          case _ => (arg, None)
        }
        def referencePath(term: Term): Boolean = term match {
          case _: Term.Name | _: Term.This | _: Term.Super => true
          case t: Term.Select => referencePath(t.qual)
          case _ => false
        }
        val expressionForm = expression match {
          case _: Lit => "literal"
          case t if referencePath(t) => "reference"
          case _ => "other"
        }
        ujson.Obj("start" -> arg.pos.start, "end" -> arg.pos.end,
          "expression_start" -> expression.pos.start, "expression_end" -> expression.pos.end,
          "expression_form" -> expressionForm,
          "reference_ranges" -> ujson.Arr.from(expression.collect { case n: Term.Name => range(n) }),
          "clause_index" -> clauseIndex, "argument_index" -> argumentIndex,
          "label_range" -> label.map(range).getOrElse(ujson.Null))
      }
    })
  def callSites(tree: Tree): ujson.Arr = {
    def site(whole: Tree, fun: Term, kind: String, args: Seq[Seq[Term]]): Option[ujson.Obj] = {
      def unwrap(term: Term): (Term, Seq[Seq[Term]]) = term match {
        case t: Term.ApplyType => unwrap(t.fun)
        case t: Term.Apply =>
          val (base, clauses) = unwrap(t.fun)
          (base, clauses :+ t.args)
        case _ => (term, Nil)
      }
      val (base, previousArgs) = unwrap(fun)
      val (name, receiver) = base match {
        case t: Term.Select => (Some(t.name), Some(t.qual))
        case n: Term.Name => (Some(n), None)
        case _ => (None, None)
      }
      name.map(n => ujson.Obj("start" -> whole.pos.start, "end" -> whole.pos.end,
        "function_start" -> fun.pos.start, "function_end" -> fun.pos.end,
        "name_start" -> n.pos.start, "name_end" -> n.pos.end, "kind" -> kind,
        "receiver_start" -> receiver.map(t => ujson.Num(t.pos.start)).getOrElse(ujson.Null),
        "receiver_end" -> receiver.map(t => ujson.Num(t.pos.end)).getOrElse(ujson.Null),
        "arguments" -> arguments(previousArgs ++ args)))
    }
    ujson.Arr.from(allNodes(tree).flatMap {
      case t: Term.Apply => site(t, t.fun, "apply", Seq(t.args)).toSeq
      // Compiler method metadata decides whether a bare type application is a
      // nullary invocation or an unevaluated method value. Do not guess here.
      case t: Term.ApplyType => site(t, t.fun, "type_apply", Nil).toSeq
      case t: Term.Select => site(t, t, "select", Nil).toSeq
      case t: Term.ApplyInfix =>
        val rightAssociative = t.op.value.endsWith(":") && t.args.nonEmpty
        val receiverStart = if (rightAssociative) t.args.head.pos.start else t.lhs.pos.start
        val receiverEnd = if (rightAssociative) t.args.last.pos.end else t.lhs.pos.end
        Seq(ujson.Obj("start" -> t.pos.start, "end" -> t.pos.end,
          "function_start" -> t.op.pos.start, "function_end" -> t.op.pos.end,
          "name_start" -> t.op.pos.start, "name_end" -> t.op.pos.end, "kind" -> "infix",
          "receiver_start" -> receiverStart, "receiver_end" -> receiverEnd,
          "arguments" -> arguments(Seq(if (rightAssociative) Seq(t.lhs) else t.args))))
      case _ => Nil
    }.sortBy(x => (x("start").num, x("end").num, x("kind").str)))
  }
  def parameters(tree: Tree): Seq[Term.Param] = tree match {
    case d: Defn.Def => d.paramss.flatten
    case d: Decl.Def => d.paramss.flatten
    case d: Defn.Class => d.ctor.paramss.flatten
    case d: Defn.Trait => d.ctor.paramss.flatten
    case d: Ctor.Secondary => d.paramss.flatten
    case _ => Nil
  }
  def parameterClauses(tree: Tree): Seq[Seq[Term.Param]] = tree match {
    case d: Defn.Def => d.paramss
    case d: Decl.Def => d.paramss
    case d: Defn.Class => d.ctor.paramss
    case d: Defn.Trait => d.ctor.paramss
    case d: Ctor.Secondary => d.paramss
    case _ => Nil
  }
  def parameterJson(tree: Tree): ujson.Arr = {
    val caseClass = tree match {
      case d: Defn.Class => d.mods.exists(_.isInstanceOf[Mod.Case])
      case _ => false
    }
    val indexed = parameterClauses(tree).zipWithIndex.flatMap { case (clause, clauseIndex) =>
      clause.zipWithIndex.map { case (p, parameterIndex) => (p, clauseIndex, parameterIndex) }
    }
    ujson.Arr.from(indexed.zipWithIndex.map { case ((p, clauseIndex, parameterIndex), index) =>
      ujson.Obj("name" -> p.name.value, "name_start" -> p.name.pos.start,
        "name_end" -> p.name.pos.end, "start" -> p.pos.start, "end" -> p.pos.end,
        "index" -> index, "clause_index" -> clauseIndex, "parameter_index" -> parameterIndex,
        "by_name" -> p.decltpe.exists(_.isInstanceOf[Type.ByName]),
        "is_field" -> ((caseClass && clauseIndex == 0) || p.mods.exists(m => Set("val", "var")(m.syntax))),
        "default" -> p.default.map(runtime(_, "parameter_default", false)).getOrElse(ujson.Null),
        "type_range" -> p.decltpe.map(range).getOrElse(ujson.Null))
    })
  }
  /** Result structure only: compiler occurrences still supply every identity.
    * Nested arguments, local definitions and deferred bodies are not results
    * of their enclosing expression merely because their ranges are contained.
    */
  def valueExpressions(tree: Tree): ujson.Arr = {
    def positioned(term: Term): Boolean = term.pos.start >= 0 && term.pos.end >= term.pos.start
    def row(term: Term, kind: String, results: Seq[Term] = Nil,
            unknown: Seq[String] = Nil): ujson.Obj =
      ujson.Obj("start" -> term.pos.start, "end" -> term.pos.end, "kind" -> kind,
        "result_ranges" -> ujson.Arr.from(results.filter(positioned).map(t => ujson.Arr(t.pos.start, t.pos.end))),
        "unknown" -> arr(unknown ++ (if (results.exists(t => !positioned(t))) Seq("result_without_source_range") else Nil)))
    ujson.Arr.from(allNodes(tree).collect {
      case t: Term if positioned(t) => t match {
        case _: Term.Name | _: Term.This | _: Term.Super | _: Term.Select => row(t, "reference")
        case _: Term.New => row(t, "allocation")
        case _: Term.NewAnonymous => row(t, "anonymous_allocation", unknown = Seq("anonymous_runtime_class_unresolved"))
        case _: Term.Apply | _: Term.ApplyInfix => row(t, "call")
        case _: Term.ApplyType => row(t, "type_application")
        case _: Term.Placeholder => row(t, "placeholder")
        // Hole expressions execute before the interpolator call. They are not
        // the interpolation's result; the consumer retains an unknown runtime
        // boundary until the compiler-bound interpolator receiver is admitted.
        case i: Term.Interpolate =>
          val value = row(t, "interpolation")
          value("effect_ranges") = ujson.Arr.from(i.args.filter(positioned).map(t => ujson.Arr(t.pos.start, t.pos.end)))
          value
        case _: Lit => row(t, "literal")
        case _: Term.Function | _: Term.AnonymousFunction | _: Term.PartialFunction | _: Term.Eta => row(t, "deferred")
        case b: Term.Block => b.stats.lastOption match {
          case Some(result: Term) => row(t, "block", Seq(result))
          case _ => row(t, "block", unknown = Seq("block_has_no_term_result"))
        }
        case i: Term.If => row(t, "if", Seq(i.thenp, i.elsep))
        case m: Term.Match => row(t, "match", m.cases.map(_.body),
          if (m.cases.isEmpty) Seq("match_has_no_cases") else Nil)
        case r: Term.Return => row(t, "return", Seq(r.expr))
        case a: Term.Ascribe => row(t, "ascribe", Seq(a.expr))
        case a: Term.Annotate => row(t, "ascribe", Seq(a.expr))
        // A finally expression does not replace a normally returned value,
        // but explicit returns inside it are separate method return exits.
        case tr: Term.Try => row(t, "try", tr.expr +: tr.catchp.map(_.body))
        case _: Term.Assign => row(t, "assignment", unknown = Seq("mutable_assignment"))
        case _ => row(t, "unsupported", unknown = Seq("unsupported_result_expression:" + t.productPrefix))
      }
    }.groupBy(ujson.write(_)).values.map(_.head).toSeq
      .sortBy(x => (x("start").num, x("end").num, x("kind").str)))
  }
  /** Explicit return values owned by this method, not nested declarations.
    * Deferred functions have their own execution boundary; their allocations
    * and returns must not become eager factory return values.
    */
  def methodReturnRanges(body: Tree): ujson.Arr = {
    def exits(tree: Tree): Seq[Term] = tree match {
      case r: Term.Return => r.expr +: exits(r.expr)
      case _: Defn.Def | _: Decl.Def | _: Defn.Class | _: Defn.Trait |
           _: Defn.Object | _: Defn.Enum | _: Ctor.Secondary => Nil
      case _: Term.Function | _: Term.AnonymousFunction | _: Term.PartialFunction | _: Term.Eta => Nil
      case _ => tree.children.flatMap(exits)
    }
    ujson.Arr.from(exits(body).filter(t => t.pos.start >= 0 && t.pos.end >= t.pos.start)
      .map(range).groupBy(ujson.write(_)).values.map(_.head).toSeq
      .sortBy(x => (x("start").num, x("end").num)))
  }
  def methodReturnUnknowns(body: Tree): ujson.Arr = {
    def unknowns(tree: Tree, deferred: Boolean): Seq[String] = tree match {
      case r: Term.Return =>
        (if (deferred) Seq("deferred_nonlocal_return") else Nil) ++
          (if (r.expr.pos.start < 0 || r.expr.pos.end < r.expr.pos.start) Seq("return_value_without_source_range") else Nil) ++
          unknowns(r.expr, deferred)
      case _: Defn.Def | _: Decl.Def | _: Defn.Class | _: Defn.Trait |
           _: Defn.Object | _: Defn.Enum | _: Ctor.Secondary => Nil
      case _: Term.Function | _: Term.AnonymousFunction | _: Term.PartialFunction | _: Term.Eta =>
        tree.children.flatMap(unknowns(_, true))
      case _ => tree.children.flatMap(unknowns(_, deferred))
    }
    arr(unknowns(body, false).distinct.sorted)
  }
  def parse(path: String, text: String): ujson.Obj = {
    val owners = ujson.Arr()
    val members = ujson.Arr()
    val constructors = ujson.Arr()
    val diagnostics = ujson.Arr()
    val out = ujson.Obj("path" -> path, "sha256" -> sha(text), "package" -> "",
      "owners" -> owners, "members" -> members, "constructors" -> constructors,
      "call_sites" -> ujson.Arr(),
      "value_expressions" -> ujson.Arr(),
      "deferred_ranges" -> ujson.Arr(),
      "type_ranges" -> ujson.Arr(), "diagnostics" -> diagnostics,
      "parser" -> "scalameta-4.15.2")
    def attempt(dialect: Dialect): Parsed[Source] = dialect(Input.VirtualFile(path, text)).parse[Source]
    // Repository sources use Scala 2.13 with -Xsource:3. Scala3 has stricter
    // indentation and can reject legal Scala213Source3 chained infix calls.
    val candidates = Seq("Scala213Source3" -> dialects.Scala213Source3,
      "Scala3" -> dialects.Scala3, "Scala213" -> dialects.Scala213)
    val failures = mutable.ArrayBuffer.empty[(String, Parsed.Error)]
    var selected: Option[(String, Parsed.Success[Source])] = None
    candidates.iterator.takeWhile(_ => selected.isEmpty).foreach { case (name, dialect) =>
      attempt(dialect) match {
        case ok: Parsed.Success[Source] => selected = Some(name -> ok)
        case error: Parsed.Error => failures += name -> error
      }
    }
    val parsed: Parsed[Source] = selected match {
      case Some((name, ok)) =>
        out("dialect") = name
        if (failures.nonEmpty) diagnostics.value += ujson.Obj("kind" -> "dialect_fallback",
          "from" -> candidates.head._1, "to" -> name, "failed_attempts" -> ujson.Arr.from(failures.map {
            case (dialect, error) => ujson.Obj("dialect" -> dialect,
              "line" -> (error.pos.startLine + 1), "message" -> error.message)
          }))
        ok
      case None =>
        failures.foreach { case (dialect, error) =>
          diagnostics.value += ujson.Obj("kind" -> "parse_error", "dialect" -> dialect,
            "line" -> (error.pos.startLine + 1), "message" -> error.message)
        }
        failures.last._2
    }
    parsed match {
      case Parsed.Success(source) =>
        def packagePrefix(stats: List[Stat], prefix: String): String = stats match {
          case (p: Pkg) :: Nil =>
            packagePrefix(p.stats, if (prefix.isEmpty) p.ref.syntax else prefix + "." + p.ref.syntax)
          case _ => prefix
        }
        out("package") = packagePrefix(source.stats, "")
        out("call_sites") = callSites(source)
        out("value_expressions") = valueExpressions(source)
        out("deferred_ranges") = ujson.Arr.from(allNodes(source).flatMap {
          case t: Term.Function => Seq(deferred(t, t.body, "function"))
          case t: Term.AnonymousFunction => Seq(deferred(t, t.body, "placeholder_function"))
          case t: Term.PartialFunction => Seq(deferred(t, t, "partial_function"))
          case t: Term.Eta => Seq(deferred(t, t.expr, "eta"))
          case _ => Nil
        })
        // Lit implements both Term and Type in Scalameta. A literal RHS is an
        // executable expression; including it here erases compiler-inserted
        // conversions as declaration-only synthetics. Signature/header spans
        // continue to classify singleton literal type declarations.
        out("type_ranges") = ujson.Arr.from(allNodes(source).collect { case t: Type if !t.isInstanceOf[Lit] =>
          range(t)
        }.groupBy(ujson.write(_)).values.map(_.head).toSeq.sortBy(x => (x("start").num, x("end").num)))
        val counts = mutable.Map.empty[(String, String), Int]
        def addMember(tree: Tree, owner: String, name: Name, kind: String,
                      body: Option[Tree], parent: Option[String],
                      bodyBounds: Option[(Int, Int)] = None): String = {
          val key = (owner, name.value)
          val count = counts.getOrElse(key, 0)
          counts(key) = count + 1
          val id = s"$owner#${name.value}@$count"
          val bodyStart = bodyBounds.map(_._1).orElse(body.map(_.pos.start))
          val bodyEnd = bodyBounds.map(_._2).orElse(body.map(_.pos.end))
          val signatureEnd = bodyStart.getOrElse(tree.pos.end)
          val defaults = parameters(tree).flatMap(_.default)
          val signature = outsideWords(tree, tree.pos.start, signatureEnd, defaults)
          val bodyWords = bodyStart.toSeq.flatMap(start =>
            outsideWords(tree, start, bodyEnd.get, nestedDeclarations(tree)))
          val lazyValue = tree match {
            case d: Defn.Val => d.mods.exists(_.isInstanceOf[Mod.Lazy])
            case _ => false
          }
          members.value += ujson.Obj("id" -> id, "path" -> path, "owner" -> owner,
            "name" -> name.value, "name_start" -> name.pos.start, "name_end" -> name.pos.end,
            "kind" -> kind, "start" -> tree.pos.start, "end" -> tree.pos.end,
            "body_start" -> bodyStart.map(ujson.Num(_)).getOrElse(ujson.Null),
            "body_end" -> bodyEnd.map(ujson.Num(_)).getOrElse(ujson.Null),
            "signature_ranges" -> outsideRanges(tree.pos.start, signatureEnd, defaults),
            "line" -> (tree.pos.startLine + 1), "signature" -> arr(signature), "body" -> arr(bodyWords),
            "signature_hash" -> sha(signature.mkString("\u0000")), "body_hash" -> sha(bodyWords.mkString("\u0000")),
            "executable" -> (body.nonEmpty && Set("def", "val", "var", "constructor")(kind)), "lazy" -> lazyValue,
            "parameters" -> parameterJson(tree),
            "return_ranges" -> (tree match {
              case d: Defn.Def => methodReturnRanges(d.body)
              case _ => ujson.Arr()
            }),
            "return_unknowns" -> (tree match {
              case d: Defn.Def => methodReturnUnknowns(d.body)
              case _ => ujson.Arr()
            }),
            "parent" -> parent.map(ujson.Str(_)).getOrElse(ujson.Null))
          id
        }
        def addConstructor(init: Init, kind: String, allocation: Option[Tree] = None): Unit = {
          val target = init.tpe match {
            case t: Type.Apply => t.tpe
            case t => t
          }
          val name = target match {
            case t: Type.Select => t.name
            case t => t
          }
          constructors.value += ujson.Obj("start" -> init.pos.start, "end" -> init.pos.end,
            "type_start" -> init.tpe.pos.start, "type_end" -> init.tpe.pos.end,
            "name_start" -> name.pos.start, "name_end" -> name.pos.end,
            "allocation_start" -> allocation.map(t => ujson.Num(t.pos.start)).getOrElse(ujson.Null),
            "allocation_end" -> allocation.map(t => ujson.Num(t.pos.end)).getOrElse(ujson.Null),
            "kind" -> kind, "arguments" -> arguments(init.argss))
        }
        def visit(tree: Tree, owner: String, pkg: String, parent: Option[String]): Unit = tree match {
          case p: Pkg =>
            val nextPkg = if (pkg.isEmpty) p.ref.syntax else pkg + "." + p.ref.syntax
            p.stats.foreach(visit(_, nextPkg, nextPkg, parent))
          case c: Defn.Class => visitOwner(c, c.name, "class", c.templ, owner, pkg, parent)
          case c: Defn.Trait => visitOwner(c, c.name, "trait", c.templ, owner, pkg, parent)
          case c: Defn.Object => visitOwner(c, c.name, "object", c.templ, owner, pkg, parent)
          case c: Defn.Enum => visitOwner(c, c.name, "enum", c.templ, owner, pkg, parent)
          case d: Defn.Def =>
            val id = addMember(d, owner, d.name, "def", Some(d.body), parent)
            d.children.foreach(visit(_, owner, pkg, Some(id)))
          case d: Decl.Def => addMember(d, owner, d.name, "def", None, parent)
          case d: Ctor.Secondary =>
            val bodyStart = d.tokens.dropWhile(_.syntax != "=").drop(1)
              .find(t => !Set("Space", "Tab", "LF", "CR", "FF", "Comment")(t.productPrefix))
              .map(_.pos.start).getOrElse(d.init.pos.start)
            val id = addMember(d, owner, d.name, "constructor", Some(d.init), parent,
              Some((bodyStart, d.pos.end)))
            addConstructor(d.init, "constructor_delegation")
            d.children.foreach(visit(_, owner, pkg, Some(id)))
          case d: Defn.Val =>
            val ns = d.pats.flatMap(_.collect { case p: Pat.Var => p.name }).distinct
            val ids = ns.map(n => addMember(d, owner, n, "val", Some(d.rhs), parent))
            d.children.foreach(visit(_, owner, pkg, ids.headOption.orElse(parent)))
          case d: Defn.Var =>
            val ns = d.pats.flatMap(_.collect { case p: Pat.Var => p.name }).distinct
            val ids = ns.map(n => addMember(d, owner, n, "var", d.rhs, parent))
            d.children.foreach(visit(_, owner, pkg, ids.headOption.orElse(parent)))
          case d: Defn.Type => addMember(d, owner, d.name, "type", None, parent)
          case d: Decl.Val => d.pats.flatMap(_.collect { case p: Pat.Var => p.name }).distinct
            .foreach(n => addMember(d, owner, n, "val", None, parent))
          case d: Decl.Var => d.pats.flatMap(_.collect { case p: Pat.Var => p.name }).distinct
            .foreach(n => addMember(d, owner, n, "var", None, parent))
          case d: Decl.Type => addMember(d, owner, d.name, "type", None, parent)
          case n: Term.New =>
            addConstructor(n.init, "allocation", Some(n))
            n.children.foreach(visit(_, owner, pkg, parent))
          case n: Term.NewAnonymous =>
            n.templ.inits.foreach(addConstructor(_, "anonymous_allocation", Some(n)))
            n.children.foreach(visit(_, owner, pkg, parent))
          case _ => tree.children.foreach(visit(_, owner, pkg, parent))
        }
        def visitOwner(tree: Tree, name: Name, kind: String, templ: Template,
                       owner: String, pkg: String, parent: Option[String]): Unit = {
          val id = (if (owner.isEmpty) name.value else owner + "." + name.value) + (if (kind == "object") "$" else "")
          val bodyStart = templ.stats.headOption.map(_.pos.start).getOrElse(tree.pos.end)
          val initializers = parameters(tree).flatMap(_.default).map(runtime(_, "parameter_default", false)) ++
            templ.inits.flatMap(_.argss.flatten).map(runtime(_, "parent_argument", true)) ++
            (templ.early ++ templ.stats).flatMap {
              case v: Defn.Val => Seq(runtime(v.rhs, "field_rhs", !v.mods.exists(_.isInstanceOf[Mod.Lazy])))
              case v: Defn.Var => v.rhs.toSeq.map(runtime(_, "field_rhs", true))
              case t: Term => Seq(runtime(t, "template_statement", true))
              case _ => Nil
            }
          templ.inits.foreach(addConstructor(_, "parent_constructor"))
          val earlyRuntime = templ.early.flatMap {
            case v: Defn.Val => Seq(v.rhs)
            case v: Defn.Var => v.rhs.toSeq
            case t: Term => Seq(t)
            case _ => Nil
          }
          val headerRuntime = parameters(tree).flatMap(_.default) ++
            templ.inits.flatMap(_.argss.flatten) ++ earlyRuntime
          owners.value += ujson.Obj("id" -> id, "name" -> name.value, "kind" -> kind, "path" -> path,
            "name_start" -> name.pos.start, "name_end" -> name.pos.end,
            "start" -> tree.pos.start, "end" -> tree.pos.end, "body_start" -> bodyStart, "body_end" -> tree.pos.end,
            "parent_owner" -> (if (owner == pkg || owner.isEmpty) ujson.Null else ujson.Str(owner)),
            "parent_member" -> parent.map(ujson.Str(_)).getOrElse(ujson.Null),
            "header_ranges" -> outsideRanges(tree.pos.start, bodyStart, headerRuntime),
            "header_tokens" -> arr(outsideWords(tree, tree.pos.start, bodyStart, headerRuntime)),
            "initializer_ranges" -> ujson.Arr.from(initializers), "parameters" -> parameterJson(tree))
          tree.children.foreach(visit(_, id, pkg, parent))
        }
        visit(source, "", "", None)
      case _: Parsed.Error => ()
    }
    out
  }
  def main(args: Array[String]): Unit = {
    require(args.length == 2, "ScalaSpans input.json output.json")
    val inputs = ujson.read(Files.readString(Paths.get(args(0)), UTF_8)).obj
    val results = ujson.Arr.from(inputs.toSeq.sortBy(_._1).map { case (path, value) => parse(path, value.str) })
    Files.writeString(Paths.get(args(1)), ujson.write(ujson.Obj("schema_version" -> 1,
      "parser" -> "scalameta-4.15.2", "sources" -> results)), UTF_8)
  }
}
