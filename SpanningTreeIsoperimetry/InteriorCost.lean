import SpanningTreeIsoperimetry.WiredPairs
import SpanningTreeIsoperimetry.InteriorSquareGain
import SpanningTreeIsoperimetry.EnhancedBoundary
import SpanningTreeIsoperimetry.FoundationsBridge
import SpanningTreeIsoperimetry.VacancyCounts
import SquareMaximality.Boundary.MatrixTreeCompletion

/-! The interior surcharge and the combined boundary/interior hull bound. -/
namespace SpanningTreeIsoperimetry.InteriorCost

open SquareMaximality SquareMaximality.Dual SquareMaximality.Boundary SquareMaximality.Multigraph
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

/-- The local face-star events have total probability at most the strict
perpendicular-pair factor. No local avoidance inequality remains assumed. -/
theorem interior_containment_sum_le (R S : ℕ) (A : Finset Point)
    (i : Fin (canonicalInteriorCount R S A)) :
    (∑ j, (rectangleDual (R+1) (S+1)).containmentRatio (interiorEventBlock R S A i j)) ≤
      ((13 : ℝ)/16)^2 :=
  InteriorAvoidance.interior_containment_sum_le_of_pair_avoidance R S A i
    (WiredPairs.interiorLow_avoidance_gt R S A i).le
    (WiredPairs.interiorHigh_avoidance_gt R S A i).le

/-- Every interior component pays the paper's uniform surcharge `3/5`, in
addition to the bulk deletion cost. -/
theorem interior_log_factor_lt {R S : ℕ} {A : Finset Point}
    (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hHull : IsRectHull A 0 0 (R+1) (S+1)) (hconn : (inducedGrid A).Connected)
    (i : Fin (canonicalInteriorCount R S A)) :
    Real.log (tau (SquareMaximality.rectangle 0 0 (R+1) (S+1) \ canonicalInterior R S A i) : ℝ) -
      Real.log (tauRect (R+1) (S+1) : ℝ) <
      -squareLatticeEntropy * (canonicalInterior R S A i).card - 3/5 := by
  let d := canonicalVacancyDeletionTreeEquivs hR hS hHull hconn
  let events := d.canonicalForestEvents hR hS
  let q : ℝ := (tau (SquareMaximality.rectangle 0 0 (R+1) (S+1) \ canonicalInterior R S A i) : ℝ) /
    (tauRect (R+1) (S+1) : ℝ)
  have hsum := interior_containment_sum_le R S A i
  have hratio := (d.interiorPlanarDuality hR hS i).eventRatio
  simp_rw [hratio] at hsum
  have hsum' : (interiorFaceStarTreeCount R S A i : ℝ) * q ≤ ((13 : ℝ)/16)^2 := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hsum
  have hT := InteriorSquareGain.interiorFaceStarTreeCount_lower_bound R S A i
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hproduct := (mul_le_mul_of_nonneg_right hT hq).trans hsum'
  have hden : 0 < 4 * Real.exp (squareLatticeEntropy * ((canonicalInterior R S A i).card - 1 : ℝ)) := by
    positivity
  have hbound : q ≤ ((13 : ℝ)/16)^2 / 4 *
      Real.exp (-squareLatticeEntropy * ((canonicalInterior R S A i).card - 1 : ℝ)) := by
    have hdiv : q ≤ ((13 : ℝ)/16)^2 /
        (4 * Real.exp (squareLatticeEntropy * ((canonicalInterior R S A i).card - 1 : ℝ))) := by
      apply (le_div_iff₀ hden).mpr
      simpa only [mul_comm] using hproduct
    convert hdiv using 1
    rw [neg_mul, Real.exp_neg]
    ring
  have hscalar := LocalBounds.vacancy_factor_with_entropy ((canonicalInterior R S A i).card : ℝ)
  rw [entropy_eq_foundation] at hscalar
  have hstrict : q < Real.exp (-squareLatticeEntropy * (canonicalInterior R S A i).card - 3/5) :=
    hbound.trans_lt hscalar
  have ha : (0 : ℝ) < tau (SquareMaximality.rectangle 0 0 (R+1) (S+1) \ canonicalInterior R S A i) := by
    exact_mod_cast events.interiorTau_pos i
  have hb : (0 : ℝ) < tauRect (R+1) (S+1) := by
    exact_mod_cast tauRect_pos (by omega : 0 < R+1) (by omega : 0 < S+1)
  have hlog := Real.log_lt_log (div_pos ha hb) hstrict
  rwa [Real.log_div ha.ne' hb.ne', Real.log_exp] at hlog

/-- Combined bulk, boundary-gap, and interior-component costs for a
nondegenerate genuine rectangular hull. -/
theorem enhanced_hull_bound {R S : ℕ} {A : Finset Point}
    (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hHull : IsRectHull A 0 0 (R+1) (S+1)) (hconn : (inducedGrid A).Connected) :
    squareLatticeEntropy * (((R+1)*(S+1)-A.card : ℕ) : ℝ) +
      Real.log (1+Real.sqrt 2) * EnhancedBoundary.boundaryGapCount R S A +
      (3 : ℝ)/5 * canonicalInteriorCount R S A ≤
      Real.log (tauRect (R+1) (S+1) : ℝ) - Real.log (tau A : ℝ) := by
  let d := canonicalVacancyDeletionTreeEquivs hR hS hHull hconn
  let events := d.canonicalForestEvents hR hS
  let transfer := rectangleDualSuccTransferCurrentDeterminantInput labeledMultigraphCofactorInput R S
  have hprod := events.log_component_product hconn transfer.forestBlockNegativeCorrelation
  have hboundary := EnhancedBoundary.boundary_gap_cost_all hHull hconn
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (canonicalInteriorCount R S A))))
    (fun i _ => (interior_log_factor_lt hR hS hHull hconn i).le)
  have hcards : ((R+1)*(S+1)-A.card : ℕ) =
      (canonicalBoundary R S A).card + ∑ i, (canonicalInterior R S A i).card := by
    rw [← rectangle_sdiff_card_of_subset hHull.2.2.1, canonical_partition,
      Finset.card_union_of_disjoint (canonicalBoundary_disjoint_interiorUnion R S A),
      Finset.card_biUnion (canonicalInterior_pairwise R S A)]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum hprod
  rw [← Finset.mul_sum] at hsum
  rw [hcards]
  push_cast
  nlinarith

/-- The full enhanced hull estimate, including one-row and one-column hulls. -/
theorem enhanced_hull_bound_all {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R+1) (S+1)) (hconn : (inducedGrid A).Connected) :
    squareLatticeEntropy * (((R+1)*(S+1)-A.card : ℕ) : ℝ) +
      Real.log (1+Real.sqrt 2) * EnhancedBoundary.boundaryGapCount R S A +
      (3 : ℝ)/5 * canonicalInteriorCount R S A ≤
      Real.log (tauRect (R+1) (S+1) : ℝ) - Real.log (tau A : ℝ) := by
  by_cases hR : 1 ≤ R
  · by_cases hS : 1 ≤ S
    · exact enhanced_hull_bound hR hS hHull hconn
    · have hS0 : S = 0 := by omega
      subst S
      have hA := hHull.eq_rectangle_of_height_one hconn
      subst A
      have hc := vacancy_counts_full_rectangle R 0
      simp [hc.1,hc.2,SquareMaximality.rectangle_card,tauRect]
  · have hR0 : R = 0 := by omega
    subst R
    have hA := hHull.eq_rectangle_of_width_one hconn
    subst A
    have hc := vacancy_counts_full_rectangle 0 S
    simp [hc.1,hc.2,SquareMaximality.rectangle_card,tauRect]

end
end SpanningTreeIsoperimetry.InteriorCost
