# Third-party formal proofs

## Kirchhoff's matrix-tree theorem

`SpanningTreeIsoperimetry/External/KirchhoffMatrixTree.lean` is adapted from
[Ho Boon Suan's FerrersBound project](https://github.com/boonsuan/FerrersBound),
revision `49bdf47cc096f37a4abe3eebf09a327a590fba81`, file
`FerrersBound/Graph/KirchhoffMatrixTreeCore.lean`.

The upstream project is distributed under the MIT license. Its full copyright
and license notice is preserved in
`SpanningTreeIsoperimetry/External/LICENSE-FerrersBound`; the copied source also
identifies its origin. No other part of FerrersBound is imported.

The source proves, for an arbitrary finite simple graph and any root, that its
integer reduced-Laplacian determinant equals the number of spanning trees. Its
count is exactly

```lean
Nat.card { T : SimpleGraph V // T ≤ G ∧ T.IsTree }
```

The main declarations are `SimpleGraph.kirchhoff_matrix_tree_int` and its real
counterpart `SimpleGraph.kirchhoff_matrix_tree`. The proof uses signed incidence
matrices, Cauchy–Binet, the zero/unit determinant dichotomy, and an equivalence
between selected tree edge sets and the above spanning-tree subtype.

The included proof uses the project's pinned Lean/mathlib toolchain. Its
theorem statements and mathematical hypotheses are preserved. Both theorem
axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

This theorem supplies the ordinary finite-graph matrix-tree theorem. The
paper's identification with the face-graph matrix `4I − A` is proved locally
in `PrimalDirichlet.lean` and instantiated for the corner domains by
`CornerPrimalFaces.cornerPrimal_treeCount_eq_faceDeterminant`. These proofs
include the planar geometry and the required domain conditions.

## Complete square-maximality foundation

`Foundations/SquareMaximality/` includes the complete public proof source from
[the square-maximality development](https://github.com/novou/square-maximality-palomar),
at its registered revision `b1d30cdb3334aa7bff7834b22b342393cdc97df8`.
The Apache 2.0 license is preserved in `Foundations/LICENSE-SquareMaximality`.
All 97 proof modules build with the project's pinned toolchain. Their
mathematical statements are preserved, and the six public endpoints use only
the permitted standard axioms. `FoundationsBridge.lean` identifies the graph,
count, rectangle, and entropy definitions with the main library. The
all-cardinality classification is proved in the main library.
