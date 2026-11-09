# Scala Test Selector

This preview packages the Rust compiler-backed selector and its paired
runtime-equivalence tool. The workspace and tracked fixtures come from the
Splice commit recorded in [SPLICE_SOURCE_REVISION](SPLICE_SOURCE_REVISION).

## Download and verify

On Ubuntu 24.04 x86-64, authenticate the GitHub CLI as an account with read
access to this private repository. Download the named preview into an empty
directory.

```sh
gh auth status
tag=v0.1.0-preview.1
package="scala-test-selector-${tag}-linux-x86_64"
gh release download "$tag" --repo danielporterda/scala-test-selector \
  --pattern "$package.tar.gz" --pattern SHA256SUMS
sha256sum --check SHA256SUMS && tar -xzf "$package.tar.gz"
cd "$package"
./selector --help
./selector producers
```

The archive contains `selector`, `runtime_equivalence`, `ScalaSpans.scala`, the
license, and `PROVENANCE.json`. Provenance records the standalone tag and
commit, the exact Splice revision, the Rust target, and the JSON emitted by
`selector producers`.

## Check a paired Scala Test change

Use Git with both exact 40-character commit IDs present locally. Preflight
reports the changed paths and blob IDs for a diff of up to 32 regular tracked
Scala sources under a project's `src/test/scala/`.

```sh
./runtime_equivalence preflight-tracked-test BASE_SHA HEAD_SHA GIT_REPO
```

For selection, supply the existing compiler-context capture
(`sbt-compiler-context/v1`), complete suite catalogue
(`compiler-ci-catalogue/v1`), and physical capture root for each revision. Keep
the captured sources and compiled products available at their expected paths.
The contexts and catalogue must identify the same exact commit on each side.

```sh
./runtime_equivalence select-tracked-test \
  BASE_CONTEXTS BASE_CATALOGUE BASE_ROOT \
  HEAD_CONTEXTS HEAD_CATALOGUE HEAD_ROOT GIT_REPO > selection.json
```

The receipt lists `excluded` and `retained` suites for the verified tracked
test-source scope. A rejected preflight or failed proof supplies no suite
exclusions. Use `compare` with the same six capture arguments to diagnose
classpath equivalence.

## Run the syntax exporter

Pass the bundled Scala source to the selector with captured compiler documents.
This requires Java and the cached Scala 2.13.18, Scalameta 4.15.2, and ujson
4.0.2 jars. Set `COURSIER_CACHE` to the Coursier v1 cache root containing
`https/repo1.maven.org/maven2`. The full jar list is in
[`selector-extract`'s toolchain module](crates/selector-extract/src/toolchain.rs).

```sh
./selector syntax --input documents.jsonl --exporter ScalaSpans.scala \
  --tool-cache toolchain-cache --output syntax.jsonl
```

## Build from the release tag

The Rust toolchain is pinned by `rust-toolchain.toml`. Fetch the locked
dependencies first so the selector build script can read Cargo metadata offline.

```sh
cargo fetch --locked
cargo test --locked --offline -p selector-runtime-equivalence --lib
cargo build --locked --offline --release -p selector-cli --bin selector
cargo build --locked --offline --release -p selector-native-effects --example runtime_equivalence
```
