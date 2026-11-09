This is a genuine compiler and JVM control for Scalactic 3.2.19 source positions.
Preparation uses cached Scala 2.13.18, SemanticDB 4.15.2, ScalaTest 3.2.19 and
native Scalameta. No sbt project or repository analysis runs. Ordinary acceptance
tests read the frozen compiler records without launching a JVM.

`PositionSuite` obtains one position explicitly (`Position.here`, line10), one
through implicit search (`capture`, line12), and another implicitly through real
ScalaTest registration (line14). Independent JVM observations verify the exact
file/line metadata and that the surrounding counter remains0. `javap-suites.log`
shows actual `new Position(String,String,int)` constructor expansions.

The negative controls have observable runtime effects. A separately compiled user
macro adds1 to the counter, and a ScalaTest assertion macro argument adds10. Their
JVM observations are `0→1` and `1→11`. They are not source-position intrinsics and
must retain macro uncertainty unless separately modeled. Real ScalaTest execution
runs all three registered tests successfully in a fresh JVM.

`manifest.json` records compiler/plugin/JAR hashes, exact Position and PositionMacro
class hashes, Java identity, all commands, original SemanticDB protobufs, compiled
classfiles and logs. The fixture's revision is the first40 hex characters of the
source-tree SHA-256, not an upstream Git revision. Regenerate offline only when
intentionally updating the evidence:

```sh
python3 tools/prepare_position_macro.py --selector artifacts/phase2-producer/selector-optimized
python3 tools/prepare_position_macro.py --verify
```

The position observation does not assert purity for arbitrary compiler macros,
ScalaTest assertions, or arbitrary `Position`-named symbols. The exact compiler
identity and typed macro result are required by the model controls.
