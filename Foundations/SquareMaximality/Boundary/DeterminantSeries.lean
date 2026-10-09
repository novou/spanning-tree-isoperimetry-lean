import SquareMaximality.Boundary.DeterminantReduction
import SquareMaximality.Boundary.TraceWalks
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Boundary face-adjacency determinant series

This module separates the two planar-duality/Matrix--Tree determinant
interfaces from the analytic logarithmic series.  The latter is
proved for every real Hermitian matrix whose eigenvalues have absolute value
strictly below `4`.  The already proved finite trace--walk theorem is then
used directly, rather than included in an input field, and the positive-length
series is reindexed to `evenPlacementTerm` using the vanishing of odd closed
walks.

This discharges the manuscript's equations `log-determinant` and
`trace-walks` up to the explicit spectral-radius bounds and the two
Matrix--Tree/cofactor identities.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Boundary
namespace DeterminantSeries

open scoped BigOperators

/-- Positive-length trace coefficient in the expansion of
`log det (4I-A)`, with `n` representing the length `n+1`. -/
noncomputable def matrixTraceTerm {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι ℝ) (n : ℕ) : ℝ :=
  Matrix.trace (A ^ (n + 1)) /
    (((n + 1 : ℕ) : ℝ) * (4 : ℝ) ^ (n + 1))

/-- Spectral decomposition computes every trace power. -/
theorem trace_pow_eq_sum_eigenvalues_pow {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (n : ℕ) :
    Matrix.trace (A ^ n) = ∑ i, hA.eigenvalues i ^ n := by
  let D : Matrix ι ι ℝ :=
    Matrix.diagonal (fun i => hA.eigenvalues i)
  have hspec : A =
      Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary D := by
    simpa [D, Function.comp_def] using hA.spectral_theorem
  have hpow := congrArg (fun M : Matrix ι ι ℝ => M ^ n) hspec
  calc
    Matrix.trace (A ^ n) =
        Matrix.trace ((Unitary.conjStarAlgAut ℝ _
          hA.eigenvectorUnitary D) ^ n) := congrArg Matrix.trace hpow
    _ = Matrix.trace (Unitary.conjStarAlgAut ℝ _
          hA.eigenvectorUnitary (D ^ n)) := by rw [map_pow]
    _ = Matrix.trace (D ^ n) := by
      rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
        Unitary.coe_star_mul_self, one_mul]
    _ = ∑ i, hA.eigenvalues i ^ n := by
      dsimp only [D]
      rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
      rfl

/-- Scalar logarithm series at one eigenvalue. -/
theorem hasSum_eigenvalue_traceTerm {x : ℝ} (hx : |x| < 4) :
    HasSum (fun n : ℕ => x ^ (n + 1) /
      (((n + 1 : ℕ) : ℝ) * (4 : ℝ) ^ (n + 1)))
      (-Real.log (1 - x / 4)) := by
  have hratio : |x / 4| < 1 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact (div_lt_one (by norm_num : (0 : ℝ) < 4)).2 hx
  have h := Real.hasSum_pow_div_log_of_abs_lt_one hratio
  refine HasSum.congr_fun h ?_
  intro n
  rw [div_pow]
  push_cast
  field_simp

private theorem hasSum_finset {α : Type*} (s : Finset α)
    (f : α → ℕ → ℝ) (g : α → ℝ)
    (h : ∀ i ∈ s, HasSum (f i) (g i)) :
    HasSum (fun n => ∑ i ∈ s, f i n) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        (h i (Finset.mem_insert_self i s)).add
          (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- Absolute spectral control below `4` gives the complete positive-length
trace series. -/
theorem hasSum_matrixTraceTerm {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hspec : ∀ i, |hA.eigenvalues i| < 4) :
    HasSum (matrixTraceTerm A)
      (∑ i, -Real.log (1 - hA.eigenvalues i / 4)) := by
  have hsum := hasSum_finset Finset.univ
    (fun i n => hA.eigenvalues i ^ (n + 1) /
      (((n + 1 : ℕ) : ℝ) * (4 : ℝ) ^ (n + 1)))
    (fun i => -Real.log (1 - hA.eigenvalues i / 4))
    (fun i _hi => hasSum_eigenvalue_traceTerm (hspec i))
  refine HasSum.congr_fun hsum ?_
  intro n
  rw [matrixTraceTerm, trace_pow_eq_sum_eigenvalues_pow hA]
  rw [Finset.sum_div]

/-- The characteristic polynomial evaluates the shifted determinant at the
same eigenvalues. -/
theorem det_fourI_sub_eq_prod_eigenvalues {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    Matrix.det ((4 : ℝ) • (1 : Matrix ι ι ℝ) - A) =
      ∏ i, (4 - hA.eigenvalues i) := by
  have hscalar : (4 : ℝ) • (1 : Matrix ι ι ℝ) =
      Matrix.scalar ι 4 := by
    classical
    ext i j
    by_cases hij : i = j <;>
      simp [hij, Matrix.scalar_apply]
  rw [hscalar]
  calc
    Matrix.det (Matrix.scalar ι 4 - A) =
        A.charpoly.eval 4 := by
      symm
      exact Matrix.eval_charpoly A 4
    _ = ∏ i, (4 - hA.eigenvalues i) := by
      rw [hA.charpoly_eq, Polynomial.eval_prod]
      simp

/-- Equation `log-determinant`: the rooted face-adjacency determinant has
the trace expansion, provided only the sharp spectral bound. -/
theorem hasSum_traceTerm_eq_card_log_four_sub_log_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hspec : ∀ i, |hA.eigenvalues i| < 4) :
    HasSum (matrixTraceTerm A)
      ((Fintype.card ι : ℝ) * Real.log 4 -
        Real.log (Matrix.det ((4 : ℝ) • (1 : Matrix ι ι ℝ) - A))) := by
  have hseries := hasSum_matrixTraceTerm hA hspec
  have hpos (i : ι) : 0 < 4 - hA.eigenvalues i := by
    have hi := (abs_lt.mp (hspec i)).2
    linarith
  have hfactor (i : ι) :
      Real.log (4 - hA.eigenvalues i) =
        Real.log 4 + Real.log (1 - hA.eigenvalues i / 4) := by
    have heq : 4 - hA.eigenvalues i =
        4 * (1 - hA.eigenvalues i / 4) := by ring
    have hone : 0 < 1 - hA.eigenvalues i / 4 := by
      have hi := hpos i
      linarith
    rw [heq, Real.log_mul (by norm_num)
      (ne_of_gt hone)]
  have hlogdet :
      Real.log (Matrix.det ((4 : ℝ) • (1 : Matrix ι ι ℝ) - A)) =
        ∑ i, (Real.log 4 + Real.log (1 - hA.eigenvalues i / 4)) := by
    rw [det_fourI_sub_eq_prod_eigenvalues hA, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro i _hi
      exact hfactor i
    · intro i _hi
      exact ne_of_gt (hpos i)
  convert hseries using 1
  rw [hlogdet, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_neg_distrib]
  ring

/-- The concrete face-adjacency trace coefficient. -/
noncomputable def faceTraceTerm (U : Finset LatticePoint) (n : ℕ) : ℝ :=
  matrixTraceTerm ((faceGraph U).adjMatrix ℝ) n

/-- The exact spectral condition needed by the logarithmic series. -/
def FaceAdjacencySpectralBound (U : Finset LatticePoint) : Prop :=
  let hA := (faceGraph U).isHermitian_adjMatrix ℝ
  ∀ i, |hA.eigenvalues i| < 4

/-- Concrete rooted face-adjacency form of equation `log-determinant`. -/
theorem hasSum_faceTraceTerm
    (U : Finset LatticePoint) (hspec : FaceAdjacencySpectralBound U) :
    HasSum (faceTraceTerm U)
      ((U.card : ℝ) * Real.log 4 -
        Real.log (Matrix.det (fourIminusAdjacency U))) := by
  classical
  let hA := (faceGraph U).isHermitian_adjMatrix ℝ
  have h := hasSum_traceTerm_eq_card_log_four_sub_log_det hA hspec
  change HasSum (matrixTraceTerm ((faceGraph U).adjMatrix ℝ))
    ((U.card : ℝ) * Real.log 4 -
      Real.log (Matrix.det (fourIminusAdjacency U)))
  simpa only [fourIminusAdjacency, Fintype.card_coe] using h

/-- Positive-length placement coefficient, before parity reindexing. -/
noncomputable def positivePlacementTerm
    (R S : ℕ) (V : Finset LatticePoint) (n : ℕ) : ℝ :=
  (closedPlacementCount R S V (n + 1) : ℝ) /
    (((n + 1 : ℕ) : ℝ) * (4 : ℝ) ^ (n + 1))

/-- The proved trace bridge identifies the difference of the two normalized
trace terms pointwise. -/
theorem faceTraceTerm_sub_eq_positivePlacementTerm
    (R S : ℕ) (V : Finset LatticePoint) (n : ℕ) :
    faceTraceTerm (faceIndices R S) n -
      faceTraceTerm (unmarkedFaces R S V) n =
        positivePlacementTerm R S V n := by
  unfold faceTraceTerm matrixTraceTerm positivePlacementTerm
  rw [← sub_div, trace_walks_real]

/-- Subtract the two proved face log-determinant series. -/
theorem hasSum_positivePlacementTerm
    (R S : ℕ) (V : Finset LatticePoint)
    (hfull : FaceAdjacencySpectralBound (faceIndices R S))
    (hunmarked : FaceAdjacencySpectralBound (unmarkedFaces R S V)) :
    HasSum (positivePlacementTerm R S V)
      ((markedFaces R S V).card * Real.log 4 -
        (Real.log (Matrix.det (fourIminusAdjacency (faceIndices R S))) -
          Real.log (Matrix.det
            (fourIminusAdjacency (unmarkedFaces R S V))))) := by
  have hfullSeries := hasSum_faceTraceTerm (faceIndices R S) hfull
  have hunmarkedSeries :=
    hasSum_faceTraceTerm (unmarkedFaces R S V) hunmarked
  have hsub := hfullSeries.sub hunmarkedSeries
  have hwalk := HasSum.congr_fun hsub
    (fun n => (faceTraceTerm_sub_eq_positivePlacementTerm R S V n).symm)
  convert hwalk using 1
  have hcards := card_markedFaces_add_card_unmarkedFaces R S V
  have hcardsR : ((markedFaces R S V).card : ℝ) +
      ((unmarkedFaces R S V).card : ℝ) = (R : ℝ) * (S : ℝ) := by
    exact_mod_cast hcards
  rw [card_faceIndices]
  push_cast
  rw [← hcardsR]
  ring

theorem positivePlacementTerm_even (R S : ℕ)
    (V : Finset LatticePoint) (a : ℕ) :
    positivePlacementTerm R S V (2 * a) = 0 := by
  simp [positivePlacementTerm, closedPlacementCount_odd]

theorem positivePlacementTerm_odd (R S : ℕ)
    (V : Finset LatticePoint) (a : ℕ) :
    positivePlacementTerm R S V (2 * a + 1) =
      evenPlacementTerm R S V a := by
  unfold positivePlacementTerm evenPlacementTerm
  rw [show 2 * a + 1 + 1 = 2 * (a + 1) by omega]

/-- Reindex the positive-length placement series by its nonzero even walk
lengths `2(a+1)`. -/
theorem hasSum_evenPlacementTerm_of_hasSum_positive
    {R S : ℕ} {V : Finset LatticePoint} {x : ℝ}
    (h : HasSum (positivePlacementTerm R S V) x) :
    HasSum (evenPlacementTerm R S V) x := by
  have hevenHas : HasSum
      (fun a => positivePlacementTerm R S V (2 * a)) 0 := by
    simpa only [positivePlacementTerm_even] using
      (hasSum_zero : HasSum (fun _a : ℕ => (0 : ℝ)) 0)
  have hoddSummable : Summable
      (fun a => positivePlacementTerm R S V (2 * a + 1)) := by
    have hinj : Function.Injective (fun a : ℕ => 2 * a + 1) := by
      intro a b hab
      exact Nat.mul_left_cancel (by norm_num)
        (Nat.add_right_cancel hab)
    change Summable
      (positivePlacementTerm R S V ∘ fun a : ℕ => 2 * a + 1)
    exact h.summable.comp_injective hinj
  have hparity := tsum_even_add_odd hevenHas.summable hoddSummable
  rw [hevenHas.tsum_eq, zero_add, h.tsum_eq] at hparity
  have hodd : HasSum
      (fun a => positivePlacementTerm R S V (2 * a + 1)) x := by
    rw [← hparity]
    exact hoddSummable.hasSum
  refine HasSum.congr_fun hodd ?_
  intro a
  exact (positivePlacementTerm_odd R S V a).symm

/-- The full proved determinant-series reduction, still expressed in terms
of the two face determinants. -/
theorem hasSum_evenPlacementTerm
    (R S : ℕ) (V : Finset LatticePoint)
    (hfull : FaceAdjacencySpectralBound (faceIndices R S))
    (hunmarked : FaceAdjacencySpectralBound (unmarkedFaces R S V)) :
    HasSum (evenPlacementTerm R S V)
      ((markedFaces R S V).card * Real.log 4 -
        (Real.log (Matrix.det (fourIminusAdjacency (faceIndices R S))) -
          Real.log (Matrix.det
            (fourIminusAdjacency (unmarkedFaces R S V))))) :=
  hasSum_evenPlacementTerm_of_hasSum_positive
    (hasSum_positivePlacementTerm R S V hfull hunmarked)

/-- The two planar-duality/Matrix--Tree identities used by this modular
reduction.  They are constructed downstream; no trace, series, or walk-count
statement is bundled into this input. -/
structure BoundaryDualDeterminantIdentities
    (R S : ℕ) (A : Finset Point) : Prop where
  rectangleDet :
    (tauRect (R + 1) (S + 1) : ℝ) =
      Matrix.det (fourIminusAdjacency (faceIndices R S))
  vacancyDet :
    (tau (rectangle 0 0 (R + 1) (S + 1) \
      canonicalBoundary R S A) : ℝ) =
      Matrix.det (fourIminusAdjacency
        (unmarkedFaces R S
          (boundaryVacancies R S (encodedVacancies R S A))))

/-- `BoundaryDeterminantSeriesInputs.logRatio` derived from the two
determinant identities, the spectral hypotheses, and the proved
trace--walk/reindexing bridge. -/
theorem logRatio_of_dualDeterminants
    {R S : ℕ} {A : Finset Point}
    (d : BoundaryDualDeterminantIdentities R S A)
    (hfull : FaceAdjacencySpectralBound (faceIndices R S))
    (hunmarked : FaceAdjacencySpectralBound
      (unmarkedFaces R S
        (boundaryVacancies R S (encodedVacancies R S A)))) :
    Real.log (tauRect (R + 1) (S + 1) : ℝ) -
        Real.log (tau (rectangle 0 0 (R + 1) (S + 1) \
          canonicalBoundary R S A) : ℝ) =
      (markedFaces R S
          (boundaryVacancies R S (encodedVacancies R S A))).card *
          Real.log 4 -
        ∑' a : ℕ, evenPlacementTerm R S
          (boundaryVacancies R S (encodedVacancies R S A)) a := by
  let V := boundaryVacancies R S (encodedVacancies R S A)
  have hseries := (hasSum_evenPlacementTerm R S V hfull hunmarked).tsum_eq
  rw [← d.rectangleDet, ← d.vacancyDet] at hseries
  dsimp only [V] at hseries
  linarith

/-- A strictly refined replacement for `BoundaryDeterminantSeriesInputs`:
the former `logRatio` field has been split into two determinant identities
and the exact spectral conditions. -/
structure RefinedBoundaryDeterminantSeriesInputs
    (R S : ℕ) (A : Finset Point) : Prop where
  dualDeterminants : BoundaryDualDeterminantIdentities R S A
  fullSpectral : FaceAdjacencySpectralBound (faceIndices R S)
  unmarkedSpectral : FaceAdjacencySpectralBound
    (unmarkedFaces R S
      (boundaryVacancies R S (encodedVacancies R S A)))

namespace RefinedBoundaryDeterminantSeriesInputs

variable {κ : ℝ} {R S : ℕ} {A : Finset Point}

/-- Constructor for the manuscript-facing boundary series package.  The
finite trace bridge and all analytic reindexing are theorem applications. -/
theorem toBoundaryDeterminantSeriesInputs
    (d : RefinedBoundaryDeterminantSeriesInputs R S A)
    (walkEntropy : HasSum evenClosedWordTerm (Real.log 4 - κ)) :
    BoundaryDeterminantSeriesInputs κ R S A where
  logRatio := logRatio_of_dualDeterminants d.dualDeterminants
    d.fullSpectral d.unmarkedSpectral
  walkEntropy := walkEntropy

end RefinedBoundaryDeterminantSeriesInputs

end DeterminantSeries
end Boundary
end SquareMaximality
