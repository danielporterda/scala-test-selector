# Context bounds, defaults, implicit clauses, and placeholder callbacks

The actual Scala 2.13.18 compiler and SemanticDB 4.15.2 plugin captured one tiny
source with synthetics enabled. The unmodified protobuf, native JSON capture,
native ScalaSpans AST, classfiles and javap output are frozen with hashes. The
native capture/export executable is pinned in the manifest. Rust tests read the
frozen data; they do not compile Scala.

`Api.param[T,V:Render]` has three written arguments and a compiler-generated
fourth evidence formal. Its generated default getter has no value arguments.
The compiler-inserted implicit evidence must fill that fourth position after the
omitted default, without adding a fifth argument. The returned function is a
separate application when applied beyond the declared two parameter clauses.

Eight independent fresh-JVM controls show that default creation runs once when
the factory is called, render runs only when the returned callback executes,
and explicit evidence changes the actual rendered value (factor two vs three).
An explicit condition skips default creation; named and explicit argument forms
produce the same intended effects. An explicit named lambda and `_.rendered`
invoke the compiler-generated implicit conversion and renderer exactly once.
The unused returned callback does not render.

`binary.json` binds the genuine generated default getter, implicit-class
conversion and actual Predef.implicitly identity to their exact JVM descriptors.
Written method bodies retain source ownership. The tests independently check the
compiler formal declarations and synthetic wrapper structure, then use ordinary
import, native admission, graph construction and query APIs. Deliberately removed
or conflicting formal metadata is an admission-negative perturbation of the
captured compiler records, never a fabricated executable answer. These methods
are callable-root controls, not discovered CI suites or test-duration evidence.
