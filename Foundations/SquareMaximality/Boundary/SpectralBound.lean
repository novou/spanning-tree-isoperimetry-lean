import SquareMaximality.Boundary.DeterminantSeries
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
# Strict spectral bound for rectangular face adjacency

This module discharges the two spectral hypotheses left by
`Boundary.DeterminantSeries`.  The argument works for every induced face set
`U ⊆ faceIndices R S`, including empty and degenerate rectangles.

Instead of trigonometric weights, we use the positive quadratic horizontal
weight

`w(x) = (x+1)(R-x)`.

The four possible neighboring weights sum to `4 w(x) - 2`.  Diagonally
rescaling the adjacency matrix by `w` and applying Gershgorin therefore puts
every eigenvalue in the open interval `(-4,4)`.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Boundary
namespace SpectralBound

open ClosedWalk
open WithLp
open scoped BigOperators

/-- A positive horizontal barrier on the face columns `0,…,R-1`. -/
def horizontalWeight (R : ℕ) (z : LatticePoint) : ℝ :=
  ((z.1 : ℝ) + 1) * ((R : ℝ) - (z.1 : ℝ))

theorem horizontalWeight_pos {R S : ℕ} {z : LatticePoint}
    (hz : z ∈ faceIndices R S) : 0 < horizontalWeight R z := by
  have hx : z.1 < R := by
    rw [mem_faceIndices] at hz
    omega
  have hxR : (z.1 : ℝ) < (R : ℝ) := by exact_mod_cast hx
  unfold horizontalWeight
  positivity

/-- The barrier weight associated with each of the four possible steps. -/
def directionWeight (R : ℕ) (z : LatticePoint) : Step → ℝ
  | .east => ((z.1 : ℝ) + 2) * ((R : ℝ) - (z.1 : ℝ) - 1)
  | .west => (z.1 : ℝ) * ((R : ℝ) - (z.1 : ℝ) + 1)
  | .north => horizontalWeight R z
  | .south => horizontalWeight R z

theorem directionWeight_nonneg {R S : ℕ} {z : LatticePoint}
    (hz : z ∈ faceIndices R S) (d : Step) :
    0 ≤ directionWeight R z d := by
  have hx : z.1 + 1 ≤ R := (mem_faceIndices.mp hz).1
  have hxR : (z.1 : ℝ) + 1 ≤ (R : ℝ) := by exact_mod_cast hx
  cases d <;> simp only [directionWeight]
  · exact mul_nonneg (by positivity) (by linarith)
  · exact mul_nonneg (by positivity) (by linarith)
  · exact (horizontalWeight_pos hz).le
  · exact (horizontalWeight_pos hz).le

theorem sum_directionWeight (R : ℕ) (z : LatticePoint) :
    ∑ d : Step, directionWeight R z d = 4 * horizontalWeight R z - 2 := by
  have huniv : (Finset.univ : Finset Step) =
      {.east, .west, .north, .south} := by decide
  rw [huniv]
  simp [directionWeight, horizontalWeight]
  ring

/-- A total choice of direction, used only on adjacent pairs below. -/
noncomputable def latticeStep (z w : LatticePoint) : Step :=
  by
    classical
    exact if h : faceLattice.Adj z w then stepOfAdjacent z w h else .east

theorem latticeStep_vector {z w : LatticePoint}
    (h : faceLattice.Adj z w) :
    (latticeStep z w).vector =
      latticePointToPoint w - latticePointToPoint z := by
  simp only [latticeStep, dif_pos h]
  exact stepOfAdjacent_vector z w h

theorem latticePointToPoint_injective :
    Function.Injective latticePointToPoint := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  simp only [latticePointToPoint, Prod.mk.injEq] at h
  apply Prod.ext
  · exact_mod_cast h.1
  · exact_mod_cast h.2

theorem latticeStep_injective_at {z w₁ w₂ : LatticePoint}
    (h₁ : faceLattice.Adj z w₁) (h₂ : faceLattice.Adj z w₂)
    (hstep : latticeStep z w₁ = latticeStep z w₂) : w₁ = w₂ := by
  apply latticePointToPoint_injective
  have hv₁ := latticeStep_vector h₁
  have hv₂ := latticeStep_vector h₂
  rw [hstep] at hv₁
  rw [hv₁] at hv₂
  exact sub_left_injective hv₂

theorem horizontalWeight_of_adjacent {R : ℕ} {z w : LatticePoint}
    (h : faceLattice.Adj z w) :
    horizontalWeight R w = directionWeight R z (latticeStep z w) := by
  have hv := latticeStep_vector h
  cases hd : latticeStep z w with
  | east =>
      simp only [hd, Step.vector_east, latticePointToPoint, Prod.mk_sub_mk,
        Prod.mk.injEq] at hv
      have hx : w.1 = z.1 + 1 := by omega
      simp only [directionWeight, horizontalWeight]
      rw [hx]
      push_cast
      ring
  | west =>
      simp only [hd, Step.vector_west, latticePointToPoint, Prod.mk_sub_mk,
        Prod.mk.injEq] at hv
      have hx : z.1 = w.1 + 1 := by omega
      simp only [directionWeight, horizontalWeight]
      have hxR : (z.1 : ℝ) = (w.1 : ℝ) + 1 := by exact_mod_cast hx
      rw [hxR]
      ring
  | north =>
      simp only [hd, Step.vector_north, latticePointToPoint, Prod.mk_sub_mk,
        Prod.mk.injEq] at hv
      have hx : w.1 = z.1 := by omega
      simp only [directionWeight]
      unfold horizontalWeight
      rw [hx]
  | south =>
      simp only [hd, Step.vector_south, latticePointToPoint, Prod.mk_sub_mk,
        Prod.mk.injEq] at hv
      have hx : w.1 = z.1 := by omega
      simp only [directionWeight]
      unfold horizontalWeight
      rw [hx]

/-- The total barrier weight of the neighbors present in any induced
subgraph is strictly less than four times the central weight. -/
theorem sum_neighbor_horizontalWeight_le
    {R S : ℕ} {U : Finset LatticePoint}
    (hU : U ⊆ faceIndices R S) (z : {p // p ∈ U}) :
    ∑ w ∈ (faceGraph U).neighborFinset z, horizontalWeight R w.1 ≤
      4 * horizontalWeight R z.1 - 2 := by
  classical
  let step : {p // p ∈ U} → Step := fun w => latticeStep z.1 w.1
  have hz : z.1 ∈ faceIndices R S := hU z.2
  have hinj : Set.InjOn step (↑((faceGraph U).neighborFinset z) :
      Set {p // p ∈ U}) := by
    intro w₁ hw₁ w₂ hw₂ heq
    apply Subtype.ext
    have h₁ := ((faceGraph U).mem_neighborFinset z w₁).mp hw₁
    have h₂ := ((faceGraph U).mem_neighborFinset z w₂).mp hw₂
    change faceLattice.Adj z.1 w₁.1 at h₁
    change faceLattice.Adj z.1 w₂.1 at h₂
    exact latticeStep_injective_at h₁ h₂ heq
  calc
    ∑ w ∈ (faceGraph U).neighborFinset z, horizontalWeight R w.1 =
        ∑ w ∈ (faceGraph U).neighborFinset z,
          directionWeight R z.1 (step w) := by
      apply Finset.sum_congr rfl
      intro w hw
      have hadj := ((faceGraph U).mem_neighborFinset z w).mp hw
      change faceLattice.Adj z.1 w.1 at hadj
      exact horizontalWeight_of_adjacent hadj
    _ = ∑ d ∈ ((faceGraph U).neighborFinset z).image step,
          directionWeight R z.1 d := by
      exact (Finset.sum_image hinj).symm
    _ ≤ ∑ d : Step, directionWeight R z.1 d := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun d _hd _hnot => directionWeight_nonneg hz d)
    _ = 4 * horizontalWeight R z.1 - 2 :=
      sum_directionWeight R z.1

/-- Adjacency after conjugation by the positive diagonal barrier. -/
noncomputable def weightedAdjacency (R : ℕ) (U : Finset LatticePoint) :
    Matrix {p // p ∈ U} {p // p ∈ U} ℝ :=
  fun z w => (faceGraph U).adjMatrix ℝ z w *
    horizontalWeight R w.1 / horizontalWeight R z.1

theorem weightedAdjacency_rowRadius_lt_four
    {R S : ℕ} {U : Finset LatticePoint}
    (hU : U ⊆ faceIndices R S) (z : {p // p ∈ U}) :
    ∑ w ∈ Finset.univ.erase z, ‖weightedAdjacency R U z w‖ < 4 := by
  classical
  have hz : z.1 ∈ faceIndices R S := hU z.2
  have hzpos : 0 < horizontalWeight R z.1 := horizontalWeight_pos hz
  have hwpos (w : {p // p ∈ U}) : 0 < horizontalWeight R w.1 :=
    horizontalWeight_pos (hU w.2)
  have hdiag : ‖weightedAdjacency R U z z‖ = 0 := by
    simp [weightedAdjacency]
  calc
    ∑ w ∈ Finset.univ.erase z, ‖weightedAdjacency R U z w‖ =
        ∑ w : {p // p ∈ U}, ‖weightedAdjacency R U z w‖ := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ z), hdiag, sub_zero]
    _ = ∑ w ∈ (faceGraph U).neighborFinset z,
          horizontalWeight R w.1 / horizontalWeight R z.1 := by
      rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro w _hw
      by_cases hadj : natManhattanDist z.1 w.1 = 1
      · simp [weightedAdjacency, hadj, abs_of_pos hzpos,
          abs_of_pos (hwpos w)]
      · simp [weightedAdjacency, hadj]
    _ = (∑ w ∈ (faceGraph U).neighborFinset z,
          horizontalWeight R w.1) / horizontalWeight R z.1 := by
      rw [Finset.sum_div]
    _ ≤ (4 * horizontalWeight R z.1 - 2) /
          horizontalWeight R z.1 := by
      exact div_le_div_of_nonneg_right
        (sum_neighbor_horizontalWeight_le hU z) hzpos.le
    _ < 4 := by
      rw [div_lt_iff₀ hzpos]
      linarith

/-- Diagonal rescaling transports every adjacency eigenvalue to
`weightedAdjacency`. -/
theorem weightedAdjacency_hasEigenvalue
    {R S : ℕ} {U : Finset LatticePoint}
    (hU : U ⊆ faceIndices R S) (i : {p // p ∈ U}) :
    Module.End.HasEigenvalue (Matrix.toLin' (weightedAdjacency R U))
      (((faceGraph U).isHermitian_adjMatrix ℝ).eigenvalues i) := by
  classical
  let hA := (faceGraph U).isHermitian_adjMatrix ℝ
  let v : {p // p ∈ U} → ℝ := ⇑(hA.eigenvectorBasis i)
  let u : {p // p ∈ U} → ℝ :=
    fun z => v z / horizontalWeight R z.1
  have hwpos (z : {p // p ∈ U}) : 0 < horizontalWeight R z.1 :=
    horizontalWeight_pos (hU z.2)
  have heigen : Matrix.mulVec (weightedAdjacency R U) u =
      hA.eigenvalues i • u := by
    funext z
    calc
      Matrix.mulVec (weightedAdjacency R U) u z =
          (Matrix.mulVec ((faceGraph U).adjMatrix ℝ) v z) /
            horizontalWeight R z.1 := by
        simp only [Matrix.mulVec, dotProduct, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro w _hw
        dsimp only [weightedAdjacency, u]
        field_simp [ne_of_gt (hwpos z), ne_of_gt (hwpos w)]
      _ = ((hA.eigenvalues i • v) z) /
            horizontalWeight R z.1 := by
        rw [congrFun (hA.mulVec_eigenvectorBasis i) z]
      _ = (hA.eigenvalues i • u) z := by
        simp [u]
        ring
  have hu : u ≠ 0 := by
    intro hu0
    have hv0 : v = 0 := by
      funext z
      calc
        v z = (v z / horizontalWeight R z.1) *
            horizontalWeight R z.1 := by
          rw [div_mul_cancel₀ _ (ne_of_gt (hwpos z))]
        _ = 0 := by rw [show v z / horizontalWeight R z.1 = 0 by
          exact congrFun hu0 z]; simp
    have hvne : v ≠ 0 := by
      exact (ofLp_eq_zero 2).ne.2 <|
        hA.eigenvectorBasis.orthonormal.ne_zero i
    exact hvne hv0
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr (by
      simpa only [Matrix.toLin'_apply] using heigen), hu⟩

/-- Every induced subgraph of a finite rectangular face grid has all
adjacency eigenvalues strictly between `-4` and `4`. -/
theorem faceAdjacencySpectralBound_of_subset
    {R S : ℕ} {U : Finset LatticePoint}
    (hU : U ⊆ faceIndices R S) :
    DeterminantSeries.FaceAdjacencySpectralBound U := by
  classical
  unfold DeterminantSeries.FaceAdjacencySpectralBound
  dsimp only
  intro i
  have heigen := weightedAdjacency_hasEigenvalue hU i
  obtain ⟨z, hz⟩ := eigenvalue_mem_ball heigen
  have hdiag : weightedAdjacency R U z z = 0 := by
    simp [weightedAdjacency]
  have hle :
      |((faceGraph U).isHermitian_adjMatrix ℝ).eigenvalues i| ≤
        ∑ w ∈ Finset.univ.erase z, ‖weightedAdjacency R U z w‖ := by
    rw [mem_closedBall_iff_norm', hdiag, zero_sub, norm_neg,
      Real.norm_eq_abs] at hz
    exact hz
  exact hle.trans_lt (weightedAdjacency_rowRadius_lt_four hU z)

/-- The full rectangular face graph satisfies the strict spectral bound. -/
theorem faceIndices_spectralBound (R S : ℕ) :
    DeterminantSeries.FaceAdjacencySpectralBound (faceIndices R S) :=
  faceAdjacencySpectralBound_of_subset (Finset.Subset.rfl)

/-- Removing any collection of marked faces preserves the strict bound. -/
theorem unmarkedFaces_spectralBound (R S : ℕ)
    (V : Finset LatticePoint) :
    DeterminantSeries.FaceAdjacencySpectralBound (unmarkedFaces R S V) :=
  faceAdjacencySpectralBound_of_subset Finset.sdiff_subset

/-- The determinant-series log-ratio theorem with both former spectral
hypotheses discharged. -/
theorem logRatio_of_dualDeterminants
    {R S : ℕ} {A : Finset Point}
    (d : DeterminantSeries.BoundaryDualDeterminantIdentities R S A) :
    Real.log (tauRect (R + 1) (S + 1) : ℝ) -
        Real.log (tau (rectangle 0 0 (R + 1) (S + 1) \
          canonicalBoundary R S A) : ℝ) =
      (markedFaces R S
          (boundaryVacancies R S (encodedVacancies R S A))).card *
          Real.log 4 -
        ∑' a : ℕ, evenPlacementTerm R S
          (boundaryVacancies R S (encodedVacancies R S A)) a := by
  exact DeterminantSeries.logRatio_of_dualDeterminants d
    (faceIndices_spectralBound R S)
    (unmarkedFaces_spectralBound R S
      (boundaryVacancies R S (encodedVacancies R S A)))

/-- The manuscript-facing determinant-series package now needs only the two
rooted-dual determinant identities: the spectral estimates, trace bridge, and
walk-entropy series are all supplied by proved theorems. -/
theorem toBoundaryDeterminantSeriesInputs
    {κ : ℝ} {R S : ℕ} {A : Finset Point}
    (d : DeterminantSeries.BoundaryDualDeterminantIdentities R S A)
    (walkEntropy : HasSum evenClosedWordTerm (Real.log 4 - κ)) :
    BoundaryDeterminantSeriesInputs κ R S A where
  logRatio := logRatio_of_dualDeterminants d
  walkEntropy := walkEntropy

end SpectralBound
end Boundary
end SquareMaximality
