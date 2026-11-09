# Native unordered hierarchy completeness

Genuine javac classes define two distinct concrete implementations of one
interface, with `A` inheriting a separate `Base`. The exact descriptor of `echo`
returns `A`; an opaque result may call A.value but cannot acquire B.value once
all unordered JVM parents have been verified. No Scala parent order is implied.
A separate control omits Object bytes: exact child headers plus the same-context
canonical Object endpoint establish its fixed empty ancestry only. They do not
supply a class-header proof, a missing nonintrinsic method body, finality or purity.

The fixture includes the actual Object.class from the pinned JDK's java.base.jmod
and its original source/license notices. `incomplete.jar` omits Base; `shadow.jar`
supplies a genuine earlier Contract extending Runnable, whose bytes are not
admitted. These missing-authority cases remain broad rather than asserting class
absence. A derived class-budget boundary supplies another conservative control.

JVM observations and exact classfile/javap receipts are frozen. These are explicit
native endpoints, not invented Scala compiler declarations or a CI catalogue.
Use `python3 tools/prepare_native_hierarchy.py`; `--verify` checks frozen files only.
