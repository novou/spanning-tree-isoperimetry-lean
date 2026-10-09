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

Upstream targets Lean/mathlib 4.28.0. This copy is ported to the project's pinned
4.34.1 environment. Changes address explicit finite-set membership, pointwise
matrix and function sums, renamed finite-sum lemmas, and equivalence reductions;
the theorem statements and mathematical hypotheses are preserved. The older
elaboration behavior is restored locally with the standard
`backward.isDefEq.respectTransparency.types` compatibility option. Every proof
still goes through the Lean kernel.

The port builds under the pinned environment. Both final theorem axiom audits
contain only `propext`, `Classical.choice`, and `Quot.sound`.

This theorem supplies the ordinary finite-graph matrix-tree theorem. The
paper's identification with the face-graph matrix `4I − A` is proved locally
in `PrimalDirichlet.lean` and instantiated for the corner domains by
`CornerPrimalFaces.cornerPrimal_treeCount_eq_faceDeterminant`. These proofs
include the planar geometry and the required domain conditions.

## Complete square-maximality foundation

`Foundations/SquareMaximality/` includes the complete public proof source from
[the author's square-maximality development](https://github.com/novou/square-maximality-palomar),
at its registered revision `b1d30cdb3334aa7bff7834b22b342393cdc97df8`.
The Apache 2.0 license is preserved in `Foundations/LICENSE-SquareMaximality`.
The source was obtained from the public repository, with the author's explicit
permission to include and recheck complete public proofs. `Challenge.lean`,
which contains unfinished exercise placeholders, is excluded.

All 97 included modules compile on Lean/mathlib 4.34.1, and the six closed
public endpoints use only the permitted standard axioms. The compatibility
port preserves the mathematical theorem statements. The original square
maximality theorem does not imply the new paper's full classification;
`FoundationsBridge.lean` proves the actual equality of the graph, count,
rectangle, and entropy definitions before any result is reused.
The foundation originally used Lean 4.32.0. The compatibility port updates
focused imports, finite-sum interfaces, and dependent-index elaboration for
Lean 4.34.1; the mathematical statements are preserved.
