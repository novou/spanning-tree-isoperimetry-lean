import SquareMaximality.Boundary.DeterminantReduction
import SquareMaximality.Boundary.SpectralBound
import SquareMaximality.Dual.PlanarComplement
import SquareMaximality.ClosedWalk.EntropySeries
import SquareMaximality.Inputs.MatrixTreeTheorem

/-!
# Boundary deletion with the full gap cost

This strengthens the boundary factor proved in the included public foundation
by retaining its nonnegative row/column gap contribution. The proof is adapted
from Jiechen Zhang's `SquareMaximality/Boundary/DeterminantReduction.lean`,
revision b1d30cdb3334aa7bff7834b22b342393cdc97df8 of
https://github.com/novou/square-maximality-palomar (Apache-2.0;
see `Foundations/LICENSE-SquareMaximality`). All source dependencies are included
and checked locally.
-/

namespace SpanningTreeIsoperimetry.EnhancedBoundary

open SquareMaximality SquareMaximality.Boundary SquareMaximality.ClosedWalk

/-- The horizontal and vertical internal vacancy-run count in the boundary
component union. This is the `g_x + g_y` in the boundary gap estimate. -/
noncomputable def boundaryGapCount (R S : ℕ) (A : Finset Point) : ℕ :=
  horizontalInternalRunCount R S
    (boundaryVacancies R S (encodedVacancies R S A)) +
  verticalInternalRunCount R S
    (boundaryVacancies R S (encodedVacancies R S A))

section Series
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

/-- Assembly lemma exposing the strengthened boundary estimate from the two
exact series inputs. The closed geometric theorem below constructs these inputs
rather than assuming them. -/
theorem gap_cost_of_series
    (d : BoundaryDeterminantSeriesInputs κ R S A)
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    κ * (canonicalBoundary R S A).card +
        Real.log (1 + Real.sqrt 2) * boundaryGapCount R S A ≤
      Real.log (tauRect (R + 1) (S + 1) : ℝ) -
        Real.log (tau (rectangle 0 0 (R + 1) (S + 1) \
          canonicalBoundary R S A) : ℝ) := by
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
  have hconstant : Real.log 4 - L = Real.log (1 + Real.sqrt 2) := by
    dsimp only [L]
    rw [Real.log_div (by norm_num) (by positivity)]
    ring
  have hfaces' :
      ((markedFaces R S V).card : ℝ) = (V.card : ℝ) + gx + gy := by
    exact_mod_cast hfaces
  rw [d.logRatio,
    show boundaryVacancies R S (encodedVacancies R S A) = V from rfl, hfaces']
  rw [← hVcard]
  change κ * (V.card : ℝ) + Real.log (1 + Real.sqrt 2) * ((gx + gy : ℕ) : ℝ) ≤ _
  push_cast
  rw [← hconstant]
  linarith only [hseries]

end Series

/-- Assembly helper requiring only Matrix--Tree; the planar, spectral, and
entropy identities are supplied by proofs in the included foundation. -/
theorem gap_cost_of_matrixTree
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0})
    {R S : ℕ} {A : Finset Point} (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    squareLatticeEntropy * (canonicalBoundary R S A).card +
        Real.log (1 + Real.sqrt 2) * boundaryGapCount R S A ≤
      Real.log (tauRect (R + 1) (S + 1) : ℝ) -
        Real.log (tau (rectangle 0 0 (R + 1) (S + 1) \
          canonicalBoundary R S A) : ℝ) := by
  let dualDeterminants :=
    Dual.boundaryDualDeterminantIdentities_of_planarTreeComplement
      hMatrixTree R S A
        (Dual.canonicalBoundaryPlanarTreeComplement hR hS hHull hconn)
  let series := SpectralBound.toBoundaryDeterminantSeriesInputs
    dualDeterminants ClosedWalk.hasSum_evenClosedWordTerm
  exact gap_cost_of_series series hHull hconn

/-- The boundary-gap proposition for every nondegenerate normalized connected
hull. All Matrix--Tree, planar-duality, spectral, and series inputs are supplied
by locally checked proofs; only the stated geometric hypotheses remain. -/
theorem boundary_gap_cost
    {R S : ℕ} {A : Finset Point} (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    squareLatticeEntropy * (canonicalBoundary R S A).card +
        Real.log (1 + Real.sqrt 2) * boundaryGapCount R S A ≤
      Real.log (tauRect (R + 1) (S + 1) : ℝ) -
        Real.log (tau (rectangle 0 0 (R + 1) (S + 1) \
          canonicalBoundary R S A) : ℝ) :=
  gap_cost_of_matrixTree labeledMultigraphCofactorInput hR hS hHull hconn

private theorem gap_cost_of_full_rectangle
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (hfull : A = rectangle 0 0 (R + 1) (S + 1)) :
    squareLatticeEntropy * (canonicalBoundary R S A).card +
        Real.log (1 + Real.sqrt 2) * boundaryGapCount R S A ≤
      Real.log (tauRect (R + 1) (S + 1) : ℝ) -
        Real.log (tau (rectangle 0 0 (R + 1) (S + 1) \
          canonicalBoundary R S A) : ℝ) := by
  have hv : encodedVacancies R S A = ∅ := by
    apply Finset.card_eq_zero.mp
    rw [card_encodedVacancies, hfull, Finset.sdiff_self, Finset.card_empty]
  have hb : boundaryVacancies R S (encodedVacancies R S A) = ∅ :=
    by
    apply Finset.subset_empty.mp
    simpa only [hv] using boundaryVacancies_subset R S (encodedVacancies R S A)
  have hcanonical : canonicalBoundary R S A = ∅ := by
    simp only [canonicalBoundary, canonicalVacancies, hb, Finset.image_empty]
  have hfaces := card_markedFaces_encodedBoundaryVacancies hHull hconn
  have hgap : boundaryGapCount R S A = 0 := by
    unfold boundaryGapCount
    rw [hb] at hfaces ⊢
    simpa [markedFaces] using hfaces.symm
  simp [hcanonical, hgap, tauRect]

/-- The boundary-gap proposition also includes one-row and one-column hulls:
connectivity fills those hulls, so both vacancy and gap charges vanish. -/
theorem boundary_gap_cost_all
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    squareLatticeEntropy * (canonicalBoundary R S A).card +
        Real.log (1 + Real.sqrt 2) * boundaryGapCount R S A ≤
      Real.log (tauRect (R + 1) (S + 1) : ℝ) -
        Real.log (tau (rectangle 0 0 (R + 1) (S + 1) \
          canonicalBoundary R S A) : ℝ) := by
  by_cases hR : R = 0
  · subst R
    exact gap_cost_of_full_rectangle hHull hconn
      (hHull.eq_rectangle_of_width_one hconn)
  by_cases hS : S = 0
  · subst S
    exact gap_cost_of_full_rectangle hHull hconn
      (hHull.eq_rectangle_of_height_one hconn)
  exact boundary_gap_cost (by omega) (by omega) hHull hconn

end SpanningTreeIsoperimetry.EnhancedBoundary
