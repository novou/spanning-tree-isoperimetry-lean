module

public import SquareMaximality.Infrastructure
public import SquareMaximality.Multigraph.All
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix

@[expose] public section

set_option autoImplicit false

/-!
# Matrix--Tree interface

The proof in `general.tex` uses Kirchhoff's Matrix--Tree theorem in both its
rectangular and labelled-planar-dual arguments.  This module states the exact
cofactor interfaces used by those arguments.  `Inputs/MatrixTreeTheorem.lean`
proves the generic labelled interface, and `Inputs/MatrixTreeBridge.lean`
derives the rectangular interface from it.
-/

namespace SquareMaximality

open SimpleGraph

/-- The reduced Laplacian obtained by deleting the row and column indexed
by `root`. -/
def reducedLapMatrix {V R : Type*} [Fintype V] [DecidableEq V]
    [AddCommGroupWithOne R] (G : SimpleGraph V) [DecidableRel G.Adj]
    (root : V) : Matrix {v : V // v ≠ root} {v : V // v ≠ root} R :=
  (G.lapMatrix R).submatrix Subtype.val Subtype.val

/-- The reduced integer Laplacian of the rectangular path product, with
decidability supplied internally. -/
noncomputable def rectangleReducedLapMatrix (r s : ℕ)
    (root : Fin r × Fin s) :
    Matrix {v : Fin r × Fin s // v ≠ root}
      {v : Fin r × Fin s // v ≠ root} ℤ := by
  classical
  exact reducedLapMatrix (pathGraph r □ pathGraph s) root

/-- The exact rectangular cofactor identity needed from Matrix--Tree.

This is deliberately restricted to the box product of two finite paths.
No spectral formula, product evaluation, or analytic estimate is included
in the input. -/
def RectangleCofactorInput : Prop :=
  ∀ (r s : ℕ) (_hr : 0 < r) (_hs : 0 < s) (root : Fin r × Fin s),
    (tauRect r s : ℤ) =
      Matrix.det (rectangleReducedLapMatrix r s root)

/-- The generic labelled-multigraph cofactor identity. Parallel edge labels
are counted separately by `spanningTreeCount`; loops are ignored on both
sides.  It is proved by `labeledMultigraphCofactorInput`. -/
def LabeledMultigraphCofactorInput : Prop :=
  ∀ (V E : Type*) [Fintype V] [DecidableEq V] [Finite E]
      (G : Multigraph.LabeledMultigraph V E) (root : V),
    (G.spanningTreeCount : ℤ) =
      Matrix.det (G.reducedLaplacian ℤ root)

end SquareMaximality
