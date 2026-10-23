module

public import SpanningTreeIsoperimetry.NormalizedSourceError
public import SpanningTreeIsoperimetry.CoupledRectangleBounds

@[expose] public section

/-! Actual normalized rectangle-error absorption for all canonical short
sides at least four, using the fully checked coupled-error estimate. -/
namespace SpanningTreeIsoperimetry.NormalizedRectangleError
open SourceHullArithmetic NormalizedSourceError CanonicalRectangleBounds RectangularRemainder
open Ferrers CornerEnergy SquareMaximality.Boundary
noncomputable section

theorem source_absorption {N t : ℕ} (hN : 0<N)
    (hR : 4≤(canonicalParameters N).1) (ht : t<canonicalIndex N) :
    error (sourceParameters N t).1 (sourceParameters N t).2.1-
      error (canonicalParameters N).1 (canonicalParameters N).2.1 <
      (((sourceParameters N t).2.2 : ℝ)-(canonicalParameters N).2.2)*
        correction (faceRectangle ((sourceParameters N t).1-1)
          ((sourceParameters N t).2.1-1)) {(0,0)} := by
  have hf := source_hull_facts hN ht.le
  have hc := selected_hull_properties_of_ceil hN
  change 0<(canonicalParameters N).1 ∧
    (canonicalParameters N).1≤(canonicalParameters N).2.1 ∧
    (canonicalParameters N).1+(canonicalParameters N).2.1=minimumSideSum N ∧
    (canonicalParameters N).1*(canonicalParameters N).2.1=N+(canonicalParameters N).2.2 ∧
    (canonicalParameters N).2.2<(canonicalParameters N).1 at hc
  have hshort := source_short_eq hN ht.le
  have haspect := admissible_aspect_le_three (ceil_sqrt_is_minimum_side_sum hN)
    hc.1 (hc.1.trans_le hc.2.1) (by omega) hc.2.2.1
  exact source_absorption_of_coupled hN hR ht
    (CoupledRectangleBounds.refined_rectangle_error hR (by omega) hf.ordered
      hf.long_le_canonical (hf.side_sum.trans hc.2.2.1.symm) haspect).le

theorem normalized_rectangle_error {N r s k : ℕ} (hN : 0<N)
    (hR : 4≤(canonicalParameters N).1) (hr : 0<r) (hrs : r≤s)
    (harea : r*s=N+k) (hsum : r+s=minimumSideSum N) :
    error r s-error (canonicalParameters N).1 (canonicalParameters N).2.1 ≤
      ((r*s-(canonicalParameters N).1*(canonicalParameters N).2.1 : ℕ) : ℝ)*
        correction (faceRectangle (r-1) (s-1)) {(0,0)} := by
  obtain ⟨ht,hp⟩ := source_parameters_of_hull hN hr hrs harea hsum
  let t := minimumSideSum N/2-r
  by_cases he : t=canonicalIndex N
  · change sourceParameters N t=(r,s,k) at hp
    rw [he,source_at_canonical] at hp
    rw [hp]
    simp
  · have htt : t<canonicalIndex N := by omega
    have hh := source_absorption hN hR htt
    rw [source_deficit_gap hN htt.le,← source_area_gap hN htt.le] at hh
    change sourceParameters N t=(r,s,k) at hp
    rw [hp] at hh
    exact hh.le

end
end SpanningTreeIsoperimetry.NormalizedRectangleError
