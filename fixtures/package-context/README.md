# Compiler package context regression

`documents.jsonl` contains two exact, unmodified native SemanticDB export rows
from the independently rebuilt PR7646 head capture. The original capture row,
raw SemanticDB, source and whole-capture hashes are retained in `manifest.json`.

`RetryFor.scala` has a definition occurrence for
`org/lfdecentralizedtrust/splice/environment/` in its package clause, with no
corresponding `SymbolInformation` entry. `TopupUtil.scala` refers to that package
in an import from a different compiler context, also without package metadata.
The normalized package kind therefore remains zero. A slash descriptor still
identifies a namespace; it cannot identify a single JVM class or source provider.

The extraction regression checks those actual compiler records at one and four
workers and rejects an invented cross-context source-provider obligation. It
supplies no syntax and makes no executable completeness claim. Ordered class
binding, missing earlier product inventories and Java class shadowing have
separate compiler-context unit controls.

```sh
cargo test -p selector-extract --test package_context --offline
cargo test -p selector-extract compiler_contexts::tests --offline
```
