//! Bounded native counterpart of helper-shadow's handwritten Pekko certificate.
//! Source tokens only constrain the admitted compiler references and synthetic
//! structure; they are never used to invent a dispatch endpoint.
use super::*;

const REQUEST_CONTRACT: &str = r#"def makeRequest[T: ToEntityMarshaller](
    method: HttpMethod, uri: Uri, headers: scala.collection.immutable.Seq[HttpHeader],
    entity: T, protocol: HttpProtocol,
  ): EitherT[Future, Either[Throwable, HttpResponse], HttpRequest] = {
    EitherT(Marshal(entity).to[RequestEntity]
      .map[Either[Either[Throwable, HttpResponse], HttpRequest]] { entity =>
        Right(HttpRequest(method = method, uri = uri, headers = headers,
          entity = entity, protocol = protocol))
      }.recover({ case t => Left(Left(t)) }))
  }"#;
const URI: &str = "org/apache/pekko/http/scaladsl/model/Uri.apply().";

struct Region<'a> {
    symbol: SymbolId,
    tokens: &'a [Token<'a>],
    body: usize,
}

impl RouterReferences<'_> {
    fn transport_rows(
        &self,
        file: FileId,
    ) -> impl Iterator<Item = &selector_facts::OccurrenceRecord> {
        let first = self
            .transport_occurrences
            .partition_point(|id| self.facts.occurrences[id.index()].file < file);
        let last = self
            .transport_occurrences
            .partition_point(|id| self.facts.occurrences[id.index()].file <= file);
        self.transport_occurrences[first..last]
            .iter()
            .map(|id| &self.facts.occurrences[id.index()])
    }
    /// Every same-operation definition in admitted handwritten Client.scala
    /// files must pass. An unsupported second client preserves broad coverage.
    pub fn handwritten_transport_clients(
        &self,
        operation: WireOperation<'_>,
    ) -> Vec<TransportProof> {
        if !identifier(operation.operation_id) {
            return Vec::new();
        }
        let Some(base) = server_base(operation) else {
            return Vec::new();
        };
        let Some(expected_path) = template_path(operation.path) else {
            return Vec::new();
        };
        let contract = tokens(REQUEST_CONTRACT).unwrap();
        let normalized: Vec<_> = normalize(&contract).collect();
        let mut named = BTreeSet::new();
        let mut result = Vec::new();
        for &file_id in &self.transport_files {
            let file = &self.facts.files[file_id.index()];
            let definitions: Vec<_> = self
                .transport_rows(file_id)
                .filter(|occurrence| {
                    occurrence.role == 2
                        && self.facts.symbols[occurrence.symbol.index()].kind == 3
                        && display(self.facts, occurrence.symbol) == operation.operation_id
                })
                .collect();
            named.extend(definitions.iter().map(|occurrence| occurrence.symbol));
            if definitions.is_empty() || file.flags & SOURCE_VERIFIED == 0 {
                continue;
            }
            let source = self.facts.text(file.source);
            if source.len() > 4 * 1024 * 1024 {
                continue;
            }
            let Some(all) = tokens(source) else {
                continue;
            };
            let regions: Vec<_> = self
                .transport_rows(file_id)
                .filter(|occurrence| {
                    occurrence.role == 2
                        && self.facts.symbols[occurrence.symbol.index()].kind == 3
                        && (display(self.facts, occurrence.symbol) == "makeRequest"
                            || display(self.facts, occurrence.symbol) == operation.operation_id)
                })
                .filter_map(|occurrence| region(&all, occurrence.symbol, occurrence.span))
                .collect();
            for occurrence in definitions {
                let symbol = occurrence.symbol;
                let owner = self.facts.symbols[symbol.index()].owner;
                if owner.is_none()
                    || self.facts.symbols[owner.index()].kind != 13
                    || self.facts.symbols[owner.index()].file != file_id
                    || self.facts.symbols[symbol.index()].file != file_id
                    || self.blocked(symbol)
                    || self.blocked(owner)
                {
                    continue;
                }
                let method_regions: Vec<_> = regions
                    .iter()
                    .filter(|region| region.symbol == symbol)
                    .collect();
                if method_regions.len() != 1 {
                    continue;
                }
                let helpers: Vec<_> = regions
                    .iter()
                    .filter(|region| {
                        display(self.facts, region.symbol) == "makeRequest"
                            && self.facts.symbols[region.symbol.index()].owner == owner
                            && !self.blocked(region.symbol)
                            && normalize(region.tokens).eq(normalized.iter().copied())
                    })
                    .collect();
                if helpers.len() != 1 {
                    continue;
                }
                let helper = helpers[0];
                if !self.helper_references(file_id, helper) {
                    continue;
                }
                let method = method_regions[0];
                if self.prove_transport_method(
                    file_id,
                    source,
                    owner,
                    helper.symbol,
                    method,
                    operation,
                    &base,
                    &expected_path,
                ) {
                    let mut hash = Sha256::new();
                    for token in method.tokens {
                        hash.update((token.text.len() as u32).to_le_bytes());
                        hash.update(token.text.as_bytes());
                    }
                    result.push(TransportProof {
                        symbol,
                        file: file_id,
                        request_helper_symbol: helper.symbol,
                        source_sha256: file.source_hash,
                        method_tokens_sha256: ContentHash(hash.finalize().into()),
                        verb: operation.verb.to_owned(),
                        base_path: base.clone(),
                        uri_template: operation.path.to_owned(),
                    });
                }
            }
        }
        result.sort_unstable_by_key(|proof| proof.symbol);
        result.dedup_by_key(|proof| proof.symbol);
        if named == result.iter().map(|proof| proof.symbol).collect() {
            result
        } else {
            Vec::new()
        }
    }
    fn reference(
        &self,
        file: FileId,
        start: usize,
        end: usize,
        predicate: impl Fn(SymbolId, &str) -> bool,
    ) -> bool {
        self.transport_rows(file).any(|occurrence| {
            occurrence.role == 1
                && start <= occurrence.span.start as usize
                && occurrence.span.start < occurrence.span.end
                && occurrence.span.end as usize <= end
                && predicate(occurrence.symbol, self.facts.symbol_name(occurrence.symbol))
        })
    }
    fn token_reference(
        &self,
        file: FileId,
        token: &Token<'_>,
        predicate: impl Fn(SymbolId, &str) -> bool,
    ) -> bool {
        self.reference(file, token.start, token.end, predicate)
    }
    fn helper_references(&self, file: FileId, helper: &Region<'_>) -> bool {
        let constructors: Vec<_> = helper
            .tokens
            .windows(2)
            .filter(|window| window[0].text == "HttpRequest" && window[1].text == "(")
            .collect();
        if constructors.len() != 1
            || !self.token_reference(file, &constructors[0][0], |_, name| {
                name.starts_with("org/apache/pekko/http/scaladsl/model/HttpRequest.")
                    || name.starts_with("org/apache/pekko/http/scaladsl/model/HttpRequest#<init>(")
            })
        {
            return false;
        }
        for token in &helper.tokens[helper.body..] {
            let allowed: &[&str] = match token.text {
                "EitherT" => &["cats/data/EitherT."],
                "Marshal" => &["org/apache/pekko/http/scaladsl/marshalling/Marshal."],
                "to" => &["org/apache/pekko/http/scaladsl/marshalling/Marshal#to()."],
                "map" => &["scala/concurrent/Future#map()."],
                "recover" => &["scala/concurrent/Future#recover()."],
                "Right" => &["scala/package.Right.", "scala/util/Right."],
                "Left" => &["scala/package.Left.", "scala/util/Left."],
                _ => continue,
            };
            if !self.token_reference(file, token, |_, name| allowed.contains(&name)) {
                return false;
            }
        }
        true
    }
    fn own_field(&self, symbol: SymbolId, owner: SymbolId, name: &str) -> bool {
        let info = &self.facts.symbols[symbol.index()];
        let parent = info.owner;
        display(self.facts, symbol) == name
            && !parent.is_none()
            && (parent == owner
                || self.facts.symbols[parent.index()].owner == owner
                    && display(self.facts, parent) == "<init>")
            && !self.blocked(symbol)
    }
    #[allow(clippy::too_many_arguments)]
    fn prove_transport_method(
        &self,
        file: FileId,
        source: &str,
        owner: SymbolId,
        helper: SymbolId,
        method: &Region<'_>,
        operation: WireOperation<'_>,
        base: &str,
        expected_path: &str,
    ) -> bool {
        let sequence = method.tokens;
        let calls: Vec<_> = sequence
            .windows(2)
            .enumerate()
            .filter(|(_, window)| window[0].text == "makeRequest" && window[1].text == "(")
            .map(|(index, _)| index)
            .collect();
        if calls.len() != 1 {
            return false;
        }
        let call = calls[0];
        let Some((args, end)) = token_arguments(sequence, call + 1) else {
            return false;
        };
        if args.len() != 5
            || !self.token_reference(file, &sequence[call], |symbol, _| symbol == helper)
        {
            return false;
        }
        let (v0, v1) = args[0];
        let verb = operation.verb.to_ascii_uppercase();
        if !matches!(
            operation.verb,
            "get" | "post" | "put" | "patch" | "delete" | "options" | "head" | "trace"
        ) || !texts_eq(&sequence[v0..v1], &["HttpMethods", ".", &verb])
        {
            return false;
        }
        let verb_symbol = format!("org/apache/pekko/http/scaladsl/model/HttpMethods.{verb}.");
        if !self.reference(file, sequence[v0].start, sequence[v1 - 1].end, |_, name| {
            name == verb_symbol
        }) {
            return false;
        }
        let (u0, u1) = args[1];
        let uri = &sequence[u0..u1];
        if uri.len() < 5
            || !texts_eq(&uri[..4], &["host", "+", "basePath", "+"])
            || !self.token_reference(file, &uri[0], |symbol, _| {
                self.own_field(symbol, owner, "host")
            })
            || !self.token_reference(file, &uri[2], |symbol, _| {
                self.own_field(symbol, owner, "basePath")
            })
        {
            return false;
        }
        let base_symbols: Vec<_> = self
            .transport_rows(file)
            .filter(|occurrence| {
                occurrence.role == 2
                    && self.facts.symbols[occurrence.symbol.index()].owner == owner
                    && display(self.facts, occurrence.symbol) == "basePath"
            })
            .filter(|occurrence| literal_base_declaration(source, occurrence.span, base))
            .map(|occurrence| occurrence.symbol)
            .collect();
        if !self.token_reference(file, &uri[2], |symbol, _| base_symbols.contains(&symbol)) {
            return false;
        }
        let mut suffix = String::new();
        let mut roots = BTreeSet::new();
        let mut at = 4;
        while at < uri.len() {
            if uri.get(at..at + 6).is_some_and(|slice| {
                texts_eq(&slice[..4], &["Formatter", ".", "addPath", "("]) && slice[5].text == ")"
            }) {
                let mut found = BTreeSet::new();
                for occurrence in self.transport_rows(file).filter(|occurrence| {
                    occurrence.role == 1
                        && uri[at].start <= occurrence.span.start as usize
                        && occurrence.span.end as usize <= uri[at + 5].end
                }) {
                    let symbol = occurrence.symbol;
                    let info = &self.facts.symbols[symbol.index()];
                    let name = self.facts.symbol_name(symbol);
                    if display(self.facts, symbol) == "addPath"
                        && !info.owner.is_none()
                        && !self.blocked(symbol)
                        && !self.blocked(info.owner)
                        && !info.file.is_none()
                        && self.facts.files[info.file.index()].flags & SOURCE_VERIFIED != 0
                        && self
                            .facts
                            .symbol_name(info.owner)
                            .ends_with("/Implicits.Formatter.")
                        && self
                            .facts
                            .path(info.file)
                            .split('/')
                            .any(|part| part == "src_managed")
                        && self.facts.path(info.file).ends_with("/Implicits.scala")
                    {
                        if let Some((root, _)) = name.split_once("/Implicits.Formatter.") {
                            found.insert(root);
                        }
                    }
                }
                if found.is_empty() {
                    return false;
                }
                roots.extend(found);
                suffix.push_str("{}");
                at += 6;
            } else {
                let Ok(literal) = serde_json::from_str::<String>(uri[at].text) else {
                    return false;
                };
                suffix.push_str(&literal);
                at += 1;
            }
            if at < uri.len() {
                if uri[at].text != "+" {
                    return false;
                }
                at += 1;
                if at == uri.len() {
                    return false;
                }
            }
        }
        if suffix != expected_path {
            return false;
        }
        let prefix = [
            ".",
            "flatMap",
            "(",
            "req",
            "=",
            ">",
            "EitherT",
            "(",
            "httpClient",
            "(",
            "req",
            ")",
        ];
        let Some(after) = sequence.get(end..end + prefix.len()) else {
            return false;
        };
        if !texts_eq(after, &prefix)
            || !self.token_reference(file, &after[8], |symbol, _| {
                self.own_field(symbol, owner, "httpClient")
            })
            || !self.token_reference(file, &after[1], |_, name| {
                name == "cats/data/EitherT#flatMap()."
            })
            || !self.token_reference(file, &after[6], |_, name| name == "cats/data/EitherT.")
        {
            return false;
        }
        let uri_span = Span {
            start: uri[0].start as u32,
            end: uri.last().unwrap().end as u32,
        };
        let first = self.transport_operations.partition_point(|id| {
            self.facts.bodies[self.facts.operations[id.index()].body.index()].file < file
        });
        let last = self.transport_operations.partition_point(|id| {
            self.facts.bodies[self.facts.operations[id.index()].body.index()].file <= file
        });
        let canonical = self.transport_operations[first..last]
            .iter()
            .map(|id| &self.facts.operations[id.index()])
            .any(|op| {
                op.opcode == Opcode::Call
                    && op.flags & OP_SYNTHETIC_EXACT_ORIGINAL_ARGUMENT != 0
                    && op.span == uri_span
                    && self.facts.symbol_name(op.target) == URI
                    && !op.body.is_none()
                    && self.facts.bodies[op.body.index()].file == file
            });
        if !canonical {
            return false;
        }
        let mut required = BTreeSet::new();
        for root in roots {
            required.insert(format!("{root}/PekkoHttpImplicits.addShowablePath()."));
            required.insert(format!("{root}/Implicits.Show.showString."));
        }
        let mut seen = BTreeSet::new();
        for occurrence in self.transport_rows(file).filter(|occurrence| {
            occurrence.role == 3
                && uri_span.start <= occurrence.span.start
                && occurrence.span.end <= uri_span.end
        }) {
            let name = self.facts.symbol_name(occurrence.symbol);
            if name != URI && !required.contains(name) {
                return false;
            }
            seen.insert(name);
        }
        seen.contains(URI) && required.iter().all(|name| seen.contains(name.as_str()))
    }
}

fn texts_eq(tokens: &[Token<'_>], texts: &[&str]) -> bool {
    tokens.len() == texts.len()
        && tokens
            .iter()
            .zip(texts)
            .all(|(token, text)| token.text == *text)
}
fn normalize<'a>(tokens: &'a [Token<'a>]) -> impl Iterator<Item = &'a str> {
    tokens
        .iter()
        .enumerate()
        .filter(|(index, token)| {
            token.text != ","
                || !tokens
                    .get(index + 1)
                    .is_some_and(|next| matches!(next.text, ")" | "]" | "}"))
        })
        .map(|(_, token)| token.text)
}
fn region<'a>(tokens: &'a [Token<'a>], symbol: SymbolId, name: Span) -> Option<Region<'a>> {
    let at = tokens
        .iter()
        .position(|token| token.start == name.start as usize && token.end == name.end as usize)?;
    if at == 0 || tokens[at - 1].text != "def" {
        return None;
    }
    let start = at - 1;
    let mut stack = Vec::new();
    let mut body = None;
    for (index, token) in tokens.iter().enumerate().skip(at + 1) {
        if stack.is_empty()
            && token.text == "="
            && tokens.get(index + 1).is_some_and(|next| next.text == "{")
        {
            body = Some(index + 1);
            break;
        }
        balance(token.text, &mut stack)?;
    }
    let body = body?;
    for (index, token) in tokens.iter().enumerate().skip(body) {
        balance(token.text, &mut stack)?;
        if stack.is_empty() {
            return Some(Region {
                symbol,
                tokens: &tokens[start..=index],
                body: body - start,
            });
        }
    }
    None
}
fn balance(token: &str, stack: &mut Vec<&'static str>) -> Option<()> {
    match token {
        "(" => stack.push(")"),
        "[" => stack.push("]"),
        "{" => stack.push("}"),
        ")" | "]" | "}" => {
            if stack.pop() != Some(token) {
                return None;
            }
        }
        _ => {}
    }
    Some(())
}
fn token_arguments(tokens: &[Token<'_>], offset: usize) -> Option<(Vec<(usize, usize)>, usize)> {
    if tokens.get(offset)?.text != "(" {
        return None;
    }
    let mut stack = vec![")"];
    let mut args = Vec::new();
    let mut start = offset + 1;
    for (index, token) in tokens.iter().enumerate().skip(start) {
        balance(token.text, &mut stack)?;
        if stack.is_empty() {
            if start < index {
                args.push((start, index));
            }
            return Some((args, index + 1));
        }
        if stack.len() == 1 && token.text == "," {
            args.push((start, index));
            start = index + 1;
        }
    }
    None
}
fn literal_base_declaration(source: &str, name: Span, expected: &str) -> bool {
    let left = name.start as usize;
    let Some(prefix) = source.get(..left) else {
        return false;
    };
    let start = prefix.rfind('\n').map_or(0, |at| at + 1);
    let end = source
        .get(left..)
        .and_then(|rest| rest.find('\n'))
        .map_or(source.len(), |at| left + at);
    let Some(before) = tokens(&source[start..left]) else {
        return false;
    };
    let Some(after) = tokens(&source[left..end]) else {
        return false;
    };
    before.last().is_some_and(|token| token.text == "val")
        && after.len() == 5
        && texts_eq(&after[..4], &["basePath", ":", "String", "="])
        && serde_json::from_str::<String>(after[4].text)
            .ok()
            .as_deref()
            == Some(expected)
}
fn server_base(operation: WireOperation<'_>) -> Option<String> {
    let mut bases = BTreeSet::new();
    let urls = if operation.server_urls.is_empty() {
        &[""][..]
    } else {
        operation.server_urls
    };
    for url in urls {
        if url.contains(['{', '}', '?', '#']) {
            return None;
        }
        let path = if let Some((_, rest)) = url.split_once("://") {
            rest.find('/').map_or("", |at| &rest[at..])
        } else if let Some(rest) = url.strip_prefix("//") {
            rest.find('/').map_or("", |at| &rest[at..])
        } else {
            url
        };
        bases.insert(path.trim_end_matches('/'));
    }
    if bases.len() == 1 {
        Some(bases.into_iter().next()?.to_owned())
    } else {
        None
    }
}
fn template_path(path: &str) -> Option<String> {
    let mut result = String::with_capacity(path.len());
    let mut rest = path;
    while let Some(at) = rest.find('{') {
        result.push_str(&rest[..at]);
        rest = &rest[at + 1..];
        let end = rest.find('}')?;
        if end == 0 || rest[..end].contains('{') {
            return None;
        }
        result.push_str("{}");
        rest = &rest[end + 1..];
    }
    if rest.contains('}') {
        return None;
    }
    result.push_str(rest);
    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use selector_facts::{
        BodyRecord, FileRecord, OccurrenceRecord, OperationRecord, SymbolRecord, TextRange,
    };
    const OWNER: &str = "example/RawClient#";
    fn intern(facts: &mut FactSnapshot, text: &str) -> StrId {
        let id = StrId(facts.strings.entries.len() as u32);
        facts.strings.entries.push(TextRange {
            start: facts.strings.bytes.len() as u64,
            len: text.len() as u32,
        });
        facts.strings.bytes.extend_from_slice(text.as_bytes());
        id
    }
    fn symbol(
        facts: &mut FactSnapshot,
        name: &str,
        display: &str,
        owner: SymbolId,
        file: FileId,
        kind: u32,
    ) -> SymbolId {
        if let Some(symbol) = facts.find_symbol(name) {
            return symbol;
        }
        let name = intern(facts, name);
        let display = intern(facts, display);
        let id = SymbolId(facts.symbols.len() as u32);
        facts.symbols.push(SymbolRecord {
            name,
            display,
            owner,
            file,
            context: StrId::NONE,
            kind,
            properties: 0,
            signature: StrId::NONE,
            span: Span::default(),
            flags: if file.is_none() { 0 } else { SYMBOL_DEFINED },
        });
        id
    }
    fn occurrence(facts: &mut FactSnapshot, file: FileId, symbol: SymbolId, span: Span, role: u32) {
        let ordinal = facts.occurrences.len() as u32;
        facts.occurrences.push(OccurrenceRecord {
            file,
            symbol,
            span,
            role,
            ordinal,
        });
    }
    fn phrase(
        facts: &mut FactSnapshot,
        file: FileId,
        source: &str,
        symbol: SymbolId,
        phrase: &str,
        token: &str,
        role: u32,
    ) {
        let start = source.find(phrase).unwrap() + phrase.find(token).unwrap();
        occurrence(
            facts,
            file,
            symbol,
            Span::new(start, start + token.len()).unwrap(),
            role,
        );
    }
    fn transport_fixture() -> (super::super::tests::Fixture, SymbolId, SymbolId, FileId) {
        let mut fixture = super::super::tests::fixture("acceptOffer");
        let facts = &mut fixture.facts;
        facts.symbols[fixture.client.index()].flags = 0;
        let source = format!(
            "class RawClient(host: String)(httpClient: HttpRequest => Future[HttpResponse]) {{\n  val basePath: String = \"\"\n{REQUEST_CONTRACT}\n  def acceptOffer(body: String) = {{\n    makeRequest(HttpMethods.POST, host + basePath + \"/offer\", Nil, body, HttpProtocols.HTTP11).flatMap(req => EitherT(httpClient(req).map(response => Right(response))))\n  }}\n}}\n"
        );
        let path = intern(facts, "apps/wallet/src/main/scala/RawClient.scala");
        let source_id = intern(facts, &source);
        let file = FileId(facts.files.len() as u32);
        facts.files.push(FileRecord {
            path,
            source: source_id,
            revision: StrId::NONE,
            context: StrId::NONE,
            source_hash: ContentHash(Sha256::digest(source.as_bytes()).into()),
            flags: SOURCE_VERIFIED,
        });
        let owner = symbol(facts, OWNER, "RawClient", SymbolId::NONE, file, 13);
        let client = symbol(
            facts,
            &format!("{OWNER}acceptOffer()."),
            "acceptOffer",
            owner,
            file,
            3,
        );
        let helper = symbol(
            facts,
            &format!("{OWNER}makeRequest()."),
            "makeRequest",
            owner,
            file,
            3,
        );
        phrase(
            facts,
            file,
            &source,
            client,
            "def acceptOffer",
            "acceptOffer",
            2,
        );
        phrase(
            facts,
            file,
            &source,
            helper,
            "def makeRequest",
            "makeRequest",
            2,
        );
        phrase(
            facts,
            file,
            &source,
            helper,
            "makeRequest(HttpMethods",
            "makeRequest",
            1,
        );
        for name in ["host", "basePath", "httpClient"] {
            let field = symbol(facts, &format!("{OWNER}{name}."), name, owner, file, 20);
            phrase(facts, file, &source, field, &format!("{name}:"), name, 2);
            phrase(
                facts,
                file,
                &source,
                field,
                if name == "httpClient" {
                    "httpClient(req)"
                } else {
                    "host + basePath"
                },
                name,
                1,
            );
        }
        let request = symbol(
            facts,
            "org/apache/pekko/http/scaladsl/model/HttpRequest.",
            "HttpRequest",
            SymbolId::NONE,
            FileId::NONE,
            10,
        );
        phrase(
            facts,
            file,
            &source,
            request,
            "HttpRequest(method",
            "HttpRequest",
            1,
        );
        let verb = symbol(
            facts,
            "org/apache/pekko/http/scaladsl/model/HttpMethods.POST.",
            "POST",
            SymbolId::NONE,
            FileId::NONE,
            10,
        );
        phrase(facts, file, &source, verb, "HttpMethods.POST", "POST", 1);
        for (name, target) in [
            ("EitherT", "cats/data/EitherT."),
            (
                "Marshal",
                "org/apache/pekko/http/scaladsl/marshalling/Marshal.",
            ),
            (
                "to",
                "org/apache/pekko/http/scaladsl/marshalling/Marshal#to().",
            ),
            ("map", "scala/concurrent/Future#map()."),
            ("recover", "scala/concurrent/Future#recover()."),
            ("Right", "scala/package.Right."),
            ("Left", "scala/package.Left."),
            ("flatMap", "cats/data/EitherT#flatMap()."),
        ] {
            let target = symbol(facts, target, name, SymbolId::NONE, FileId::NONE, 3);
            for token in tokens(&source)
                .unwrap()
                .iter()
                .filter(|token| token.text == name)
            {
                occurrence(
                    facts,
                    file,
                    target,
                    Span::new(token.start, token.end).unwrap(),
                    1,
                );
            }
        }
        let target = symbol(facts, URI, "apply", SymbolId::NONE, FileId::NONE, 3);
        let uri = "host + basePath + \"/offer\"";
        let start = source.find(uri).unwrap();
        let span = Span::new(start, start + uri.len()).unwrap();
        occurrence(facts, file, target, span, 3);
        let body = BodyId(facts.bodies.len() as u32);
        facts.bodies.push(BodyRecord {
            symbol: client,
            file,
            span: Span::new(0, source.len()).unwrap(),
            name_span: Span::default(),
            operations: IdRange {
                start: facts.operations.len() as u32,
                len: 1,
            },
            parameters: IdRange::default(),
            body_hash: ContentHash::default(),
            flags: 0,
        });
        facts.operations.push(OperationRecord {
            body,
            opcode: Opcode::Call,
            target,
            dest: ValueId::NONE,
            a: ValueId::NONE,
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span,
            flags: OP_SYNTHETIC_EXACT_ORIGINAL_ARGUMENT,
        });
        (fixture, client, helper, file)
    }
    fn prove(fixture: &super::super::tests::Fixture) -> OperationProof {
        let tasks = [GenerationTask {
            schema_path: super::super::tests::operation().schema_path.to_owned(),
            package: "example.http.v0".into(),
            mode: GenerationMode::ScalaServer,
        }];
        RouterReferences::new(&fixture.facts).prove_operation_with_tasks(
            super::super::tests::operation(),
            RouteCandidates {
                clients: &[],
                handlers: &[fixture.handler],
                literal_packages: &[],
                inventory_complete: true,
            },
            &tasks,
            Some("wallet"),
        )
    }
    #[test]
    fn compiler_bound_pekko_transport_supplies_server_only_missing_client() {
        let (fixture, client, helper, file) = transport_fixture();
        let index = RouterReferences::new(&fixture.facts);
        let direct = index.handwritten_transport_clients(super::super::tests::operation());
        assert_eq!(direct.len(), 1);
        assert_eq!(direct[0].request_helper_symbol, helper);
        assert_eq!(direct[0].file, file);
        let proof = prove(&fixture);
        assert!(proof.complete, "{}", proof.reason);
        assert_eq!(proof.clients, [client]);
        assert!(proof.symbols.contains(&fixture.implementation));
        assert_eq!(proof.handwritten_transport_proofs.len(), 1);
        assert_eq!(proof.handwritten_transport_proofs[0].uri_template, "/offer");
        let tasks = [GenerationTask {
            schema_path: super::super::tests::operation().schema_path.to_owned(),
            package: "example.http.v0".into(),
            mode: GenerationMode::ScalaClient,
        }];
        assert!(
            !index
                .prove_operation_with_tasks(
                    super::super::tests::operation(),
                    RouteCandidates {
                        clients: &[],
                        handlers: &[fixture.handler],
                        literal_packages: &[],
                        inventory_complete: true
                    },
                    &tasks,
                    Some("wallet")
                )
                .complete
        );
    }
    #[test]
    fn unknown_helper_wire_receiver_or_rewritten_request_preserves_guard() {
        for (before, after) in [
            ("uri = uri", "uri = otherUri"),
            ("\"/offer\"", "\"/other\""),
            ("host + basePath", "unknownHost + basePath"),
            ("httpClient(req)", "httpClient(req.withUri(otherUri))"),
        ] {
            let (mut fixture, _, _, file) = transport_fixture();
            let source = fixture
                .facts
                .text(fixture.facts.files[file.index()].source)
                .replace(before, after);
            let source_id = intern(&mut fixture.facts, &source);
            fixture.facts.files[file.index()].source = source_id;
            fixture.facts.files[file.index()].source_hash =
                ContentHash(Sha256::digest(source.as_bytes()).into());
            assert!(!prove(&fixture).complete, "{after}");
        }
    }
    #[test]
    fn compiler_shadows_custom_wrappers_and_noncanonical_uri_never_bind() {
        for target in [
            "host.",
            "httpClient.",
            "HttpMethods.POST.",
            "makeRequest().",
            "EitherT.",
            "Marshal.",
            "#to().",
            "#map().",
            "#recover().",
            "package.Right.",
            "#flatMap().",
        ] {
            let (mut fixture, _, _, file) = transport_fixture();
            let unknown = symbol(
                &mut fixture.facts,
                "local0",
                "unknown",
                SymbolId::NONE,
                file,
                0,
            );
            let rejected: HashSet<_> = fixture
                .facts
                .symbols
                .iter()
                .enumerate()
                .filter(|(_, info)| fixture.facts.text(info.name).ends_with(target))
                .map(|(index, _)| SymbolId(index as u32))
                .collect();
            for occurrence in fixture.facts.occurrences.iter_mut().filter(|occurrence| {
                occurrence.file == file
                    && occurrence.role == 1
                    && rejected.contains(&occurrence.symbol)
            }) {
                occurrence.symbol = unknown;
            }
            assert!(!prove(&fixture).complete, "{target}");
        }
        let (mut fixture, _, _, _) = transport_fixture();
        fixture.facts.operations.last_mut().unwrap().flags = 0;
        assert!(!prove(&fixture).complete);
        let (mut fixture, _, _, file) = transport_fixture();
        let unknown = symbol(
            &mut fixture.facts,
            "custom/Rewriter#toUri().",
            "toUri",
            SymbolId::NONE,
            FileId::NONE,
            3,
        );
        fixture.facts.operations.last_mut().unwrap().target = unknown;
        assert!(!prove(&fixture).complete);
        let (mut fixture, _, _, file2) = transport_fixture();
        let unknown = symbol(
            &mut fixture.facts,
            "custom/Rewriter#toUri().",
            "toUri",
            SymbolId::NONE,
            FileId::NONE,
            3,
        );
        let span = fixture.facts.operations.last().unwrap().span;
        occurrence(&mut fixture.facts, file2, unknown, span, 3); // Unknown execution at canonical URI is also rejected.
        assert!(!prove(&fixture).complete);
        let _ = file;
    }
    #[test]
    fn unproved_second_same_operation_client_blocks_exhaustive_certificate() {
        let (mut fixture, _, _, _) = transport_fixture();
        let facts = &mut fixture.facts;
        let text = "class OtherClient { def acceptOffer() = unknownTransport(\"/offer\") }\n";
        let path = intern(facts, "apps/wallet/src/main/scala/OtherClient.scala");
        let source = intern(facts, text);
        let file = FileId(facts.files.len() as u32);
        facts.files.push(FileRecord {
            path,
            source,
            context: StrId::NONE,
            revision: StrId::NONE,
            source_hash: ContentHash(Sha256::digest(text.as_bytes()).into()),
            flags: SOURCE_VERIFIED,
        });
        let owner = symbol(
            facts,
            "example/OtherClient#",
            "OtherClient",
            SymbolId::NONE,
            file,
            13,
        );
        let client = symbol(
            facts,
            "example/OtherClient#acceptOffer().",
            "acceptOffer",
            owner,
            file,
            3,
        );
        phrase(
            facts,
            file,
            text,
            client,
            "def acceptOffer",
            "acceptOffer",
            2,
        );
        assert!(!prove(&fixture).complete);
    }
    #[test]
    fn generated_path_encoder_requires_exact_source_and_both_implicit_executions() {
        let (mut fixture, _, _, file) = transport_fixture();
        let facts = &mut fixture.facts;
        let old = "host + basePath + \"/offer\"";
        let new = "host + basePath + \"/offer/\" + Formatter.addPath(body)";
        let source = facts.text(facts.files[file.index()].source).to_owned();
        let start = source.find(old).unwrap();
        let end = start + old.len();
        let delta = (new.len() - old.len()) as u32;
        let changed = source.replace(old, new);
        let text = intern(facts, &changed);
        facts.files[file.index()].source = text;
        facts.files[file.index()].source_hash =
            ContentHash(Sha256::digest(changed.as_bytes()).into());
        for occurrence in facts
            .occurrences
            .iter_mut()
            .filter(|occurrence| occurrence.file == file)
        {
            if occurrence.span.start >= end as u32 {
                occurrence.span.start += delta;
                occurrence.span.end += delta;
            } else if occurrence.role == 3 && occurrence.span == Span::new(start, end).unwrap() {
                occurrence.span.end += delta;
            }
        }
        facts.operations.last_mut().unwrap().span.end += delta;
        facts.bodies.last_mut().unwrap().span.end += delta;
        let path = intern(
            facts,
            "apps/wallet/target/scala-2.13/src_managed/main/Implicits.scala",
        );
        let text = intern(
            facts,
            "object Implicits { object Formatter { def addPath(value: String) = value } }",
        );
        let formatter_file = FileId(facts.files.len() as u32);
        let hash = ContentHash(Sha256::digest(facts.text(text).as_bytes()).into());
        facts.files.push(FileRecord {
            path,
            source: text,
            context: StrId::NONE,
            revision: StrId::NONE,
            source_hash: hash,
            flags: SOURCE_VERIFIED,
        });
        let owner = symbol(
            facts,
            "example/http/Implicits.Formatter.",
            "Formatter",
            SymbolId::NONE,
            formatter_file,
            10,
        );
        let method = symbol(
            facts,
            "example/http/Implicits.Formatter.addPath().",
            "addPath",
            owner,
            formatter_file,
            3,
        );
        phrase(
            facts,
            file,
            &changed,
            method,
            "Formatter.addPath(body)",
            "addPath",
            1,
        );
        let span = Span::new(start, start + new.len()).unwrap();
        let encoder = symbol(
            facts,
            "example/http/PekkoHttpImplicits.addShowablePath().",
            "addShowablePath",
            SymbolId::NONE,
            FileId::NONE,
            3,
        );
        let show = symbol(
            facts,
            "example/http/Implicits.Show.showString.",
            "showString",
            SymbolId::NONE,
            FileId::NONE,
            3,
        );
        occurrence(facts, file, encoder, span, 3);
        occurrence(facts, file, show, span, 3);
        let operation = WireOperation {
            path: "/offer/{id}",
            ..super::super::tests::operation()
        };
        assert_eq!(
            RouterReferences::new(facts)
                .handwritten_transport_clients(operation)
                .len(),
            1
        );
        facts
            .occurrences
            .retain(|occurrence| occurrence.role != 3 || occurrence.symbol != show);
        assert!(
            RouterReferences::new(facts)
                .handwritten_transport_clients(operation)
                .is_empty()
        );
        occurrence(facts, file, show, span, 3);
        let path = intern(facts, "apps/wallet/src/main/scala/Implicits.scala");
        facts.files[formatter_file.index()].path = path;
        assert!(
            RouterReferences::new(facts)
                .handwritten_transport_clients(operation)
                .is_empty()
        );
    }
}
