import SquareMaximality.Multigraph.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Multiplicity matrices and Laplacians

The matrices here use the convention appropriate for spanning trees: loops
are ignored.  `edgeMultiplicity` still exposes the raw number of labels with
specified ends, while `adjacencyMultiplicity` replaces the diagonal by zero.
Thus the Laplacian is unchanged by `deleteLoops`.

No determinant identity is asserted in this file.
-/

set_option autoImplicit false

namespace SquareMaximality.Multigraph
namespace LabeledMultigraph

open scoped Matrix

variable {V E : Type*} (G : LabeledMultigraph V E)

noncomputable local instance laplacianDecidableEqVertex : DecidableEq V := Classical.decEq V

/-- Labels with the specified unordered pair of ends. -/
abbrev LinkEdge (u v : V) := {e : E // G.IsLink e u v}

/-- Swapping the displayed endpoints does not change the type of incident
edge labels. -/
noncomputable def linkEdgeSwapEquiv (u v : V) : G.LinkEdge u v ≃ G.LinkEdge v u where
  toFun e := ⟨e.1, (G.isLink_comm e.1 u v).mp e.2⟩
  invFun e := ⟨e.1, (G.isLink_comm e.1 v u).mp e.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Raw number of labelled edges whose ends are `u`, `v`.

For `u = v`, this counts loop labels once. -/
noncomputable def edgeMultiplicity [Finite E] (u v : V) : ℕ :=
  Nat.card (G.LinkEdge u v)

theorem edgeMultiplicity_comm [Finite E] (u v : V) :
    G.edgeMultiplicity u v = G.edgeMultiplicity v u := by
  unfold edgeMultiplicity
  exact Nat.card_congr (G.linkEdgeSwapEquiv u v)

theorem edgeMultiplicity_pos_iff [Finite E] (u v : V) :
    0 < G.edgeMultiplicity u v ↔ ∃ e, G.IsLink e u v := by
  rw [edgeMultiplicity, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨⟨e, he⟩⟩, _⟩
    exact ⟨e, he⟩
  · rintro ⟨e, he⟩
    exact ⟨⟨⟨e, he⟩⟩, inferInstance⟩

/-- The adjacency multiplicity used by the Laplacian.  It agrees with raw
multiplicity away from the diagonal and is zero on the diagonal, so loops are
ignored. -/
noncomputable def adjacencyMultiplicity [Finite E] (u v : V) : ℕ :=
  if u = v then 0 else G.edgeMultiplicity u v

@[simp]
theorem adjacencyMultiplicity_self [Finite E] (u : V) :
    G.adjacencyMultiplicity u u = 0 := by
  simp [adjacencyMultiplicity]

theorem adjacencyMultiplicity_of_ne [Finite E] {u v : V} (h : u ≠ v) :
    G.adjacencyMultiplicity u v = G.edgeMultiplicity u v := by
  simp [adjacencyMultiplicity, h]

theorem adjacencyMultiplicity_comm [Finite E] (u v : V) :
    G.adjacencyMultiplicity u v = G.adjacencyMultiplicity v u := by
  by_cases h : u = v
  · subst v
    rfl
  · rw [G.adjacencyMultiplicity_of_ne h,
      G.adjacencyMultiplicity_of_ne (Ne.symm h), G.edgeMultiplicity_comm]

theorem adjacencyMultiplicity_pos_iff [Finite E] (u v : V) :
    0 < G.adjacencyMultiplicity u v ↔ u ≠ v ∧ ∃ e, G.IsLink e u v := by
  by_cases h : u = v
  · subst v
    simp
  · simp [G.adjacencyMultiplicity_of_ne h, G.edgeMultiplicity_pos_iff, h]

/-- Edge labels between two distinct vertices are automatically nonloops,
giving the canonical correspondence after deleting loops. -/
def deleteLoopsLinkEquiv {u v : V} (h : u ≠ v) :
    G.deleteLoops.LinkEdge u v ≃ G.LinkEdge u v where
  toFun e := ⟨e.1.1, e.2⟩
  invFun e := ⟨⟨e.1, G.not_isLoop_of_isLink_of_ne e.2 h⟩, e.2⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

theorem deleteLoops_edgeMultiplicity_of_ne [Finite E] {u v : V} (h : u ≠ v) :
    G.deleteLoops.edgeMultiplicity u v = G.edgeMultiplicity u v := by
  unfold edgeMultiplicity
  exact Nat.card_congr (G.deleteLoopsLinkEquiv h)

@[simp]
theorem deleteLoops_adjacencyMultiplicity [Finite E] (u v : V) :
    G.deleteLoops.adjacencyMultiplicity u v = G.adjacencyMultiplicity u v := by
  by_cases h : u = v
  · subst v
    simp
  · rw [G.deleteLoops.adjacencyMultiplicity_of_ne h,
      G.adjacencyMultiplicity_of_ne h, G.deleteLoops_edgeMultiplicity_of_ne h]

/-- The loop-free edge-multiplicity adjacency matrix. -/
noncomputable def adjacencyMatrix [Finite E] : Matrix V V ℕ :=
  Matrix.of G.adjacencyMultiplicity

@[simp]
theorem adjacencyMatrix_apply [Finite E] (u v : V) :
    G.adjacencyMatrix u v = G.adjacencyMultiplicity u v :=
  rfl

@[simp]
theorem adjacencyMatrix_diagonal [Finite E] (u : V) : G.adjacencyMatrix u u = 0 :=
  G.adjacencyMultiplicity_self u

theorem adjacencyMatrix_transpose [Finite E] : G.adjacencyMatrixᵀ = G.adjacencyMatrix := by
  ext u v
  exact G.adjacencyMultiplicity_comm v u

/-- Degree after loops have been discarded, with parallel edge labels counted
with their multiplicity. -/
noncomputable def degree [Fintype V] [Finite E] (u : V) : ℕ :=
  ∑ v, G.adjacencyMultiplicity u v

@[simp]
theorem deleteLoops_degree [Fintype V] [Finite E] (u : V) :
    G.deleteLoops.degree u = G.degree u := by
  simp only [degree, deleteLoops_adjacencyMultiplicity]

/-- The combinatorial Laplacian over any commutative ring.

Diagonal entries are degrees and off-diagonal entries are negative edge
multiplicities. -/
noncomputable def laplacian (R : Type*) [CommRing R] [Fintype V] [Finite E] :
    Matrix V V R :=
  Matrix.of fun u v ↦
    if u = v then (G.degree u : R) else -(G.adjacencyMultiplicity u v : R)

@[simp]
theorem laplacian_apply (R : Type*) [CommRing R] [Fintype V] [Finite E] (u v : V) :
    G.laplacian R u v =
      if u = v then (G.degree u : R) else -(G.adjacencyMultiplicity u v : R) :=
  rfl

@[simp]
theorem laplacian_diagonal (R : Type*) [CommRing R] [Fintype V] [Finite E] (u : V) :
    G.laplacian R u u = (G.degree u : R) := by
  simp

theorem laplacian_offDiagonal (R : Type*) [CommRing R] [Fintype V] [Finite E]
    {u v : V} (h : u ≠ v) :
    G.laplacian R u v = -(G.adjacencyMultiplicity u v : R) := by
  simp [h]

theorem laplacian_apply_eq_diagonal_sub (R : Type*) [CommRing R] [Fintype V] [Finite E]
    (u v : V) :
    G.laplacian R u v =
      (if u = v then (G.degree u : R) else 0) - (G.adjacencyMultiplicity u v : R) := by
  by_cases h : u = v
  · subst v
    simp
  · simp [h]

/-- Every row of the Laplacian sums to zero. -/
theorem laplacian_row_sum (R : Type*) [CommRing R] [Fintype V] [Finite E] (u : V) :
    ∑ v, G.laplacian R u v = 0 := by
  simp_rw [G.laplacian_apply_eq_diagonal_sub R]
  rw [Finset.sum_sub_distrib]
  simp [degree]

theorem laplacian_transpose (R : Type*) [CommRing R] [Fintype V] [Finite E] :
    (G.laplacian R)ᵀ = G.laplacian R := by
  ext u v
  by_cases h : u = v
  · subst v
    rfl
  · rw [Matrix.transpose_apply, G.laplacian_offDiagonal R (Ne.symm h),
      G.laplacian_offDiagonal R h, G.adjacencyMultiplicity_comm]

@[simp]
theorem deleteLoops_laplacian (R : Type*) [CommRing R] [Fintype V] [Finite E] :
    G.deleteLoops.laplacian R = G.laplacian R := by
  ext u v
  by_cases h : u = v
  · subst v
    simp
  · simp [h]

/-- Vertex indices remaining after deleting one root row and column. -/
abbrev AwayFrom (root : V) := {v : V // v ≠ root}

/-- The root-reduced Laplacian, with the row and column indexed by `root`
deleted. -/
noncomputable def reducedLaplacian (R : Type*) [CommRing R] [Fintype V] [Finite E]
    (root : V) : Matrix (AwayFrom root) (AwayFrom root) R :=
  (G.laplacian R).submatrix Subtype.val Subtype.val

@[simp]
theorem reducedLaplacian_apply (R : Type*) [CommRing R] [Fintype V] [Finite E]
    (root : V) (u v : AwayFrom root) :
    G.reducedLaplacian R root u v = G.laplacian R u.1 v.1 :=
  rfl

theorem reducedLaplacian_transpose (R : Type*) [CommRing R] [Fintype V] [Finite E]
    (root : V) :
    (G.reducedLaplacian R root)ᵀ = G.reducedLaplacian R root := by
  ext u v
  rw [Matrix.transpose_apply, reducedLaplacian_apply, reducedLaplacian_apply]
  have hsymm := congr_fun (congr_fun (G.laplacian_transpose R) v.1) u.1
  simpa using hsymm.symm

@[simp]
theorem deleteLoops_reducedLaplacian (R : Type*) [CommRing R] [Fintype V] [Finite E]
    (root : V) :
    G.deleteLoops.reducedLaplacian R root = G.reducedLaplacian R root := by
  ext u v
  simp

end LabeledMultigraph
end SquareMaximality.Multigraph
