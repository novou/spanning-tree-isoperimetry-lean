# Square-maximality foundation

Source: [the author’s public square-maximality development](https://github.com/novou/square-maximality-palomar).
The included source corresponds to PALOMAR-2026-08-23-000003-v1; provenance is
recorded in [third-party documentation](../docs/third-party.md).
The Apache 2.0 license is retained in `LICENSE-SquareMaximality`.

All 97 implementation modules have been ported to the pinned Lean/mathlib
4.34.1 toolchain, compiled, and included in the project’s axiom audit.
`SquareMaximality.lean` is the public import wrapper. The incomplete upstream
`Challenge.lean` interface is excluded.

`FoundationsBridge.lean` checks the identification of graphs, counts, rectangles,
and entropy before this source is used. The newer all-cardinality classification
is proved separately in the main development.
