import SquareMaximality.Boundary.Euler
import SquareMaximality.Boundary.SeriesCharging
import SquareMaximality.Boundary.Canonical

/-!
# Boundary determinant-series reduction

This module assembles the marked-face count, the fixed-length walk charging
bound, and the two evaluated span series.  The remaining upstream inputs are
stated at their natural level: the rooted-dual log-determinant expansion and
the square-lattice closed-walk entropy series.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Boundary

open ClosedWalk

noncomputable def evenClosedWordTerm (a : ℕ) : ℝ :=
  (closedWordCount (2 * (a + 1)) : ℝ) /
    ((2 * (a + 1) : ℕ) * (4 : ℝ) ^ (2 * (a + 1)))

noncomputable def evenHorizontalSpanTerm (a : ℕ) : ℝ :=
  ((∑ omega ∈ closedWords (2 * (a + 1)), (spanX omega + 1) : ℕ) : ℝ) /
    ((2 * (a + 1) : ℕ) * (4 : ℝ) ^ (2 * (a + 1)))

noncomputable def evenVerticalSpanTerm (a : ℕ) : ℝ :=
  ((∑ omega ∈ closedWords (2 * (a + 1)), (spanY omega + 1) : ℕ) : ℝ) /
    ((2 * (a + 1) : ℕ) * (4 : ℝ) ^ (2 * (a + 1)))

noncomputable def evenPlacementTerm
    (R S : ℕ) (V : Finset LatticePoint) (a : ℕ) : ℝ :=
  (closedPlacementCount R S V (2 * (a + 1)) : ℝ) /
    ((2 * (a + 1) : ℕ) * (4 : ℝ) ^ (2 * (a + 1)))

/-- Exact remaining series inputs for the boundary determinant comparison.
The first field packages rooted planar duality, Matrix--Tree, the logdet
series, and the finite trace/placement identification.  The second is the
standard square-lattice walk-entropy identity. -/
structure BoundaryDeterminantSeriesInputs
    (κ : ℝ) (R S : ℕ) (A : Finset Point) : Prop where
  logRatio :
    Real.log (tauRect (R + 1) (S + 1) : ℝ) -
        Real.log (tau (rectangle 0 0 (R + 1) (S + 1) \
          canonicalBoundary R S A) : ℝ) =
      (markedFaces R S
          (boundaryVacancies R S (encodedVacancies R S A))).card * Real.log 4 -
        ∑' a : ℕ, evenPlacementTerm R S
          (boundaryVacancies R S (encodedVacancies R S A)) a
  walkEntropy :
    HasSum evenClosedWordTerm (Real.log 4 - κ)

namespace BoundaryDeterminantSeriesInputs

variable {κ : ℝ} {R S : ℕ} {A : Finset Point}

private theorem denominator_pos (a : ℕ) :
    0 < ((2 * (a + 1) : ℕ) : ℝ) * (4 : ℝ) ^ (2 * (a + 1)) := by
  positivity

private theorem placementTerm_nonneg (a : ℕ) :
    0 ≤ evenPlacementTerm R S
      (boundaryVacancies R S (encodedVacancies R S A)) a := by
  unfold evenPlacementTerm
  positivity

private theorem placementTerm_le (a : ℕ) :
    evenPlacementTerm R S
        (boundaryVacancies R S (encodedVacancies R S A)) a ≤
      (boundaryVacancies R S (encodedVacancies R S A)).card *
          evenClosedWordTerm a +
        horizontalInternalRunCount R S
            (boundaryVacancies R S (encodedVacancies R S A)) *
          evenHorizontalSpanTerm a +
        verticalInternalRunCount R S
            (boundaryVacancies R S (encodedVacancies R S A)) *
          evenVerticalSpanTerm a := by
  let V := boundaryVacancies R S (encodedVacancies R S A)
  have hnat := closedPlacementCount_encodedBoundaryVacancies_le
    R S A (2 * (a + 1))
  have hreal : (closedPlacementCount R S V (2 * (a + 1)) : ℝ) ≤
      (V.card * closedWordCount (2 * (a + 1)) +
        horizontalInternalRunCount R S V *
          (∑ omega ∈ closedWords (2 * (a + 1)), (spanX omega + 1)) +
        verticalInternalRunCount R S V *
          (∑ omega ∈ closedWords (2 * (a + 1)), (spanY omega + 1)) : ℕ) := by
    exact_mod_cast hnat
  have hdiv := div_le_div_of_nonneg_right hreal (denominator_pos a).le
  dsimp only [V] at hdiv
  unfold evenPlacementTerm evenClosedWordTerm evenHorizontalSpanTerm
    evenVerticalSpanTerm
  push_cast at hdiv ⊢
  calc
    (closedPlacementCount R S
        (boundaryVacancies R S (encodedVacancies R S A)) (2 * (a + 1)) : ℝ) /
        ((2 : ℝ) * (a + 1) * 4 ^ (2 * (a + 1))) ≤ _ := hdiv
    _ = _ := by
      field_simp [ne_of_gt (denominator_pos a)]

private theorem spanLog_le_logFour :
    Real.log (4 / (1 + Real.sqrt 2)) ≤ Real.log 4 := by
  have hden : 0 < 1 + Real.sqrt 2 := by positivity
  have hratioPos : 0 < (4 : ℝ) / (1 + Real.sqrt 2) := div_pos (by norm_num) hden
  apply Real.log_le_log hratioPos
  rw [div_le_iff₀ hden]
  nlinarith [Real.sqrt_nonneg 2]

/-- The two exact series inputs imply the full boundary logarithmic factor.
The finite Euler identity used in the marked-face count is proved in
`Boundary.Euler`, so it is no longer an input to this theorem. -/
theorem log_boundaryFactor
    (d : BoundaryDeterminantSeriesInputs κ R S A)
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    Real.log (tau (rectangle 0 0 (R + 1) (S + 1) \
        canonicalBoundary R S A) : ℝ) -
      Real.log (tauRect (R + 1) (S + 1) : ℝ) ≤
        -κ * (canonicalBoundary R S A).card := by
  let V := boundaryVacancies R S (encodedVacancies R S A)
  let gx := horizontalInternalRunCount R S V
  let gy := verticalInternalRunCount R S V
  let L := Real.log (4 / (1 + Real.sqrt 2))
  let majorant : ℕ → ℝ := fun a =>
    V.card * evenClosedWordTerm a + gx * evenHorizontalSpanTerm a +
      gy * evenVerticalSpanTerm a
  have hx : HasSum evenHorizontalSpanTerm L := by
    refine HasSum.congr_fun hasSum_horizontalSpanEven ?_
    intro a
    rfl
  have hy : HasSum evenVerticalSpanTerm L := by
    refine HasSum.congr_fun hasSum_verticalSpanEven ?_
    intro a
    rfl
  have hmajorant : HasSum majorant
      (V.card * (Real.log 4 - κ) + gx * L + gy * L) := by
    have hclosed : HasSum (fun a =>
        (V.card : ℝ) * evenClosedWordTerm a)
        ((V.card : ℝ) * (Real.log 4 - κ)) :=
      HasSum.mul_left (V.card : ℝ) d.walkEntropy
    have hhoriz : HasSum (fun a =>
        (gx : ℝ) * evenHorizontalSpanTerm a) ((gx : ℝ) * L) :=
      HasSum.mul_left (gx : ℝ) hx
    have hvert : HasSum (fun a =>
        (gy : ℝ) * evenVerticalSpanTerm a) ((gy : ℝ) * L) :=
      HasSum.mul_left (gy : ℝ) hy
    exact HasSum.congr_fun ((hclosed.add hhoriz).add hvert) (fun _ => rfl)
  have hplacementSummable : Summable (fun a =>
      evenPlacementTerm R S V a) := by
    apply Summable.of_nonneg_of_le
    · intro a
      exact placementTerm_nonneg a
    · intro a
      exact placementTerm_le a
    · exact hmajorant.summable
  have hseries : (∑' a : ℕ, evenPlacementTerm R S V a) ≤
      V.card * (Real.log 4 - κ) + gx * L + gy * L := by
    calc
      (∑' a : ℕ, evenPlacementTerm R S V a) ≤ ∑' a : ℕ, majorant a :=
        hplacementSummable.tsum_le_tsum (fun a => placementTerm_le a)
          hmajorant.summable
      _ = V.card * (Real.log 4 - κ) + gx * L + gy * L :=
        hmajorant.tsum_eq
  have hfaces := card_markedFaces_encodedBoundaryVacancies
    hHull hconn
  have hVcard : V.card = (canonicalBoundary R S A).card := by
    dsimp only [V, canonicalBoundary, canonicalVacancies]
    exact (Finset.card_image_of_injective _ ofNatPoint_injective).symm
  have hmargin : 0 ≤ Real.log 4 - L := sub_nonneg.mpr spanLog_le_logFour
  have hgxy :
      0 ≤ ((gx : ℝ) + (gy : ℝ)) * (Real.log 4 - L) :=
    mul_nonneg (by positivity) hmargin
  have hbase : κ * (V.card : ℝ) ≤
      ((V.card : ℝ) + (gx : ℝ) + (gy : ℝ)) * Real.log 4 -
        ((V.card : ℝ) * (Real.log 4 - κ) +
          (gx : ℝ) * L + (gy : ℝ) * L) := by
    calc
      κ * (V.card : ℝ) ≤
          κ * (V.card : ℝ) +
            ((gx : ℝ) + (gy : ℝ)) * (Real.log 4 - L) :=
        le_add_of_nonneg_right hgxy
      _ = ((V.card : ℝ) + (gx : ℝ) + (gy : ℝ)) * Real.log 4 -
          ((V.card : ℝ) * (Real.log 4 - κ) +
            (gx : ℝ) * L + (gy : ℝ) * L) := by ring
  have hlower : κ * (canonicalBoundary R S A).card ≤
      Real.log (tauRect (R + 1) (S + 1) : ℝ) -
        Real.log (tau (rectangle 0 0 (R + 1) (S + 1) \
          canonicalBoundary R S A) : ℝ) := by
    rw [d.logRatio]
    have hfaces' :
        ((markedFaces R S V).card : ℝ) = (V.card : ℝ) + gx + gy := by
      exact_mod_cast hfaces
    rw [show boundaryVacancies R S (encodedVacancies R S A) = V from rfl]
    rw [hfaces']
    rw [← hVcard]
    exact hbase.trans (sub_le_sub_left hseries _)
  linarith

end BoundaryDeterminantSeriesInputs

end Boundary
end SquareMaximality
