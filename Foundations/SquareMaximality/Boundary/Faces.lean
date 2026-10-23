module

public import SquareMaximality.Boundary.Encoding
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Unit faces and the boundary determinant matrix

This file formalizes the marked/unmarked face sets from `general.tex`, lines
778--790, and the finite matrix `4I - A_U` used later in the determinant
comparison.  It is purely definitional/combinatorial; no Matrix--Tree or
determinant identity is asserted here.
-/

namespace SquareMaximality

namespace Boundary

open Windows

/-- Starts of unit-square faces in the vertex grid `{0,...,R} × {0,...,S}`. -/
def faceIndices (R S : ℕ) : Finset LatticePoint :=
  validWindowStarts R 1 ×ˢ validWindowStarts S 1

@[simp] theorem mem_faceIndices {R S : ℕ} {z : LatticePoint} :
    z ∈ faceIndices R S ↔ z.1 + 1 ≤ R ∧ z.2 + 1 ≤ S := by
  simp [faceIndices]

@[simp] theorem card_faceIndices (R S : ℕ) :
    (faceIndices R S).card = R * S := by
  have hR : validWindowStarts R 1 = Finset.range R := by
    ext x
    simp [validWindowStarts, line]
    omega
  have hS : validWindowStarts S 1 = Finset.range S := by
    ext y
    simp [validWindowStarts, line]
    omega
  simp [faceIndices, hR, hS]

/-- The four corners of the unit face indexed by `z`. -/
def faceCorners (z : LatticePoint) : Finset LatticePoint :=
  rectangleWindow z.1 z.2 1 1

@[simp] theorem mem_faceCorners {z w : LatticePoint} :
    w ∈ faceCorners z ↔
      z.1 ≤ w.1 ∧ w.1 ≤ z.1 + 1 ∧ z.2 ≤ w.2 ∧ w.2 ≤ z.2 + 1 := by
  simp [faceCorners]

/-- Faces having at least one corner in the vacancy set. -/
def markedFaces (R S : ℕ) (V : Finset LatticePoint) : Finset LatticePoint :=
  (faceIndices R S).filter fun z => (faceCorners z ∩ V).Nonempty

/-- Faces with no vacant corner. -/
def unmarkedFaces (R S : ℕ) (V : Finset LatticePoint) : Finset LatticePoint :=
  faceIndices R S \ markedFaces R S V

@[simp] theorem mem_markedFaces {R S : ℕ} {V : Finset LatticePoint}
    {z : LatticePoint} :
    z ∈ markedFaces R S V ↔
      z.1 + 1 ≤ R ∧ z.2 + 1 ≤ S ∧
        ∃ w ∈ V,
          z.1 ≤ w.1 ∧ w.1 ≤ z.1 + 1 ∧
          z.2 ≤ w.2 ∧ w.2 ≤ z.2 + 1 := by
  simp only [markedFaces, Finset.mem_filter, mem_faceIndices]
  constructor
  · rintro ⟨hz, ⟨w, hw⟩⟩
    have hw' := Finset.mem_inter.mp hw
    exact ⟨hz.1, hz.2, w, hw'.2, (mem_faceCorners.mp hw'.1).1,
      (mem_faceCorners.mp hw'.1).2.1, (mem_faceCorners.mp hw'.1).2.2.1,
      (mem_faceCorners.mp hw'.1).2.2.2⟩
  · rintro ⟨hx, hy, w, hwV, hzx, hx1, hzy, hy1⟩
    exact ⟨⟨hx, hy⟩, ⟨w, Finset.mem_inter.mpr
      ⟨mem_faceCorners.mpr ⟨hzx, hx1, hzy, hy1⟩, hwV⟩⟩⟩

@[simp] theorem mem_unmarkedFaces {R S : ℕ} {V : Finset LatticePoint}
    {z : LatticePoint} :
    z ∈ unmarkedFaces R S V ↔
      z ∈ faceIndices R S ∧ (faceCorners z ∩ V) = ∅ := by
  classical
  simp only [unmarkedFaces, Finset.mem_sdiff, markedFaces, Finset.mem_filter]
  constructor
  · rintro ⟨hz, hnot⟩
    refine ⟨hz, ?_⟩
    apply Finset.not_nonempty_iff_eq_empty.mp
    exact fun hne => hnot ⟨hz, hne⟩
  · rintro ⟨hz, hempty⟩
    exact ⟨hz, fun h => by
      rw [hempty] at h
      exact Finset.not_nonempty_empty h.2⟩

theorem markedFaces_disjoint_unmarkedFaces (R S : ℕ) (V : Finset LatticePoint) :
    Disjoint (markedFaces R S V) (unmarkedFaces R S V) := by
  exact Finset.disjoint_sdiff

theorem markedFaces_union_unmarkedFaces (R S : ℕ) (V : Finset LatticePoint) :
    markedFaces R S V ∪ unmarkedFaces R S V = faceIndices R S := by
  classical
  rw [Finset.union_comm]
  exact Finset.sdiff_union_of_subset (Finset.filter_subset _ _)

theorem card_markedFaces_add_card_unmarkedFaces
    (R S : ℕ) (V : Finset LatticePoint) :
    (markedFaces R S V).card + (unmarkedFaces R S V).card = R * S := by
  rw [← card_faceIndices R S, ← markedFaces_union_unmarkedFaces R S V,
    Finset.card_union_of_disjoint (markedFaces_disjoint_unmarkedFaces R S V)]

/-- Marked unit faces are precisely the unit-window starts counted by the
two-dimensional window development. -/
theorem card_markedFaces_eq_meetingUnitWindows
    (R S : ℕ) (V : Finset LatticePoint) :
    (markedFaces R S V).card =
      (meetingRectangleWindowStarts R S 1 1 V).card := by
  classical
  apply Finset.card_bij (fun z _ => ⟨z.1, z.2⟩)
  · intro z hz
    rw [mem_meetingRectangleWindowStarts]
    exact mem_markedFaces.mp hz
  · intro z₁ hz₁ z₂ hz₂ h
    have hx : z₁.1 = z₂.1 := congrArg Sigma.fst h
    have hy : z₁.2 = z₂.2 := congrArg (fun z => z.2) h
    exact Prod.ext hx hy
  · rintro ⟨x, y⟩ h
    refine ⟨(x, y), ?_, rfl⟩
    exact mem_markedFaces.mpr (mem_meetingRectangleWindowStarts.mp h)

/-- The anisotropic-window estimate specialized to the marked unit faces. -/
theorem card_markedFaces_le
    (R S : ℕ) (V : Finset LatticePoint)
    (hV : V ⊆ grid R S) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hinj : SlidingWindowInjection R S 1 V) :
    (markedFaces R S V).card ≤
      V.card + horizontalInternalRunCount R S V +
        verticalInternalRunCount R S V := by
  rw [card_markedFaces_eq_meetingUnitWindows]
  simpa using anisotropic_window_inequality R S 1 1 V hV hR hS hinj

/-- Manhattan distance on natural-coordinate face indices. -/
def natManhattanDist (z w : LatticePoint) : ℕ :=
  Nat.dist z.1 w.1 + Nat.dist z.2 w.2

theorem natManhattanDist_comm (z w : LatticePoint) :
    natManhattanDist z w = natManhattanDist w z := by
  simp [natManhattanDist, Nat.dist_comm]

/-- The infinite simple square lattice on natural-coordinate face indices. -/
def faceLattice : SimpleGraph LatticePoint where
  Adj z w := natManhattanDist z w = 1
  symm.symm z w h := by
    rwa [natManhattanDist_comm]
  loopless.irrefl z h := by
    simp [natManhattanDist] at h

/-- The face-adjacency graph induced by a finite face set `U`. -/
def faceGraph (U : Finset LatticePoint) : SimpleGraph {z // z ∈ U} :=
  faceLattice.comap Subtype.val

noncomputable instance faceGraphDecidableAdj (U : Finset LatticePoint) :
    DecidableRel (faceGraph U).Adj := Classical.decRel _

@[simp] theorem faceGraph_adj_iff {U : Finset LatticePoint}
    (z w : {p // p ∈ U}) :
    (faceGraph U).Adj z w ↔ natManhattanDist z.1 w.1 = 1 :=
  Iff.rfl

/-- The exact finite matrix `4I - A_U` appearing in the boundary-vacancy
determinant comparison. -/
noncomputable def fourIminusAdjacency (U : Finset LatticePoint) :
    Matrix {z // z ∈ U} {z // z ∈ U} ℝ := by
  classical
  exact (4 : ℝ) • 1 - (faceGraph U).adjMatrix ℝ

theorem fourIminusAdjacency_apply (U : Finset LatticePoint)
    (z w : {p // p ∈ U}) :
    fourIminusAdjacency U z w =
      (if z = w then 4 else 0) -
        (if natManhattanDist z.1 w.1 = 1 then 1 else 0) := by
  classical
  simp [fourIminusAdjacency, SimpleGraph.adjMatrix_apply, Matrix.one_apply]

/-- The paper's empty-determinant convention is the standard Lean determinant
on the empty index type. -/
@[simp] theorem det_fourIminusAdjacency_empty :
    Matrix.det (fourIminusAdjacency (∅ : Finset LatticePoint)) = 1 := by
  classical
  simp

/-- Number of rooted closed face-adjacency walks of a prescribed length. -/
noncomputable def closedFaceWalkCount (U : Finset LatticePoint) (n : ℕ) : ℕ := by
  classical
  exact ∑ z : {p // p ∈ U},
    Fintype.card {w : (faceGraph U).Walk z z // w.length = n}

/-- The trace of an adjacency power counts rooted closed walks. -/
theorem trace_adjMatrix_pow_eq_closedFaceWalkCount
    (U : Finset LatticePoint) (n : ℕ) :
    Matrix.trace ((faceGraph U).adjMatrix ℕ ^ n) = closedFaceWalkCount U n := by
  classical
  rw [Matrix.trace, closedFaceWalkCount]
  apply Finset.sum_congr rfl
  intro z _
  exact SimpleGraph.adjMatrix_pow_apply_eq_card_walk n z z

/-- Real-valued form used by the logarithmic determinant expansion. -/
theorem trace_adjMatrix_pow_real_eq_closedFaceWalkCount
    (U : Finset LatticePoint) (n : ℕ) :
    Matrix.trace ((faceGraph U).adjMatrix ℝ ^ n) = (closedFaceWalkCount U n : ℝ) := by
  classical
  rw [Matrix.trace, closedFaceWalkCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact SimpleGraph.adjMatrix_pow_apply_eq_card_walk n z z

end Boundary

end SquareMaximality
