# Square-maximality foundation

Source: [square-maximality development](https://github.com/novou/square-maximality-palomar).
The included source corresponds to PALOMAR-2026-08-23-000003-v1; provenance is
recorded in [third-party documentation](../docs/third-party.md).
The Apache 2.0 license is retained in `LICENSE-SquareMaximality`.

The 97 proof modules use the pinned Lean/mathlib 4.35.0-rc2 toolchain and are
included in the project's build and axiom audit. `SquareMaximality.lean` is
the public import wrapper.

[FoundationsBridge.lean](../SpanningTreeIsoperimetry/FoundationsBridge.lean)
identifies the graphs, counts, rectangles, and entropy with the main library's
definitions. The all-cardinality classification is proved in the main library.
