# JVM symbolic member resolution

Shared, bounded JVM declaring-member resolution over immutable class metadata.
The provider must verify its inputs and preserve classpath precedence. Resolution
does not establish access checks, receiver dispatch, class initialization or
execution effects.

Graph construction and native effect extraction use this same implementation.
Neither depends on the other to resolve inherited fields and methods, which
allows their high-level crates to compile in parallel. The graph builder keeps
its existing `binary_resolve` import path as a compatibility re-export.
