import SpanningTreeIsoperimetry.NormalizedErrorAssembly
import SpanningTreeIsoperimetry.SourceHullArithmetic

/-! Actual selector parameters for the normalized remainder comparison.
The final coupled analytic bound is still supplied explicitly here. -/
namespace SpanningTreeIsoperimetry.NormalizedSourceError
open SourceHullArithmetic CanonicalRectangleBounds RectangularRemainder
open Ferrers CornerEnergy SquareMaximality.Boundary
noncomputable section

theorem source_short_eq {N t : ℕ} (hN : 0<N) (ht : t≤canonicalIndex N) :
    (sourceParameters N t).1=(canonicalParameters N).1+canonicalIndex N-t := by
  have hc := selected_hull_properties_of_ceil hN
  change 0<(canonicalParameters N).1 ∧ _ at hc
  dsimp [sourceParameters,canonicalParameters,canonicalIndex] at hc ht ⊢
  omega

theorem source_area_gap {N t : ℕ} (hN : 0<N) (ht : t≤canonicalIndex N) :
    (sourceParameters N t).1*(sourceParameters N t).2.1-
      (canonicalParameters N).1*(canonicalParameters N).2.1=
      canonicalIndex N*(canonicalIndex N+minimumSideSum N%2)-t*(t+minimumSideSum N%2) := by
  have hs := (source_hull_facts hN ht).area
  have hc := (source_hull_facts hN (le_refl (canonicalIndex N))).area
  rw [source_at_canonical] at hc
  let e := minimumSideSum N%2
  let d := (minimumSideSum N/2)*(minimumSideSum N/2+e)-N
  let T := canonicalIndex N
  have hfeas : T*(T+e)≤d := (selectorIndex_bounds d e).1
  have htfeas : t*(t+e)≤d := selector_index_feasible hfeas ht
  change (sourceParameters N t).1*(sourceParameters N t).2.1=N+(d-t*(t+e)) at hs
  change (canonicalParameters N).1*(canonicalParameters N).2.1=N+(d-T*(T+e)) at hc
  change _=T*(T+e)-t*(t+e)
  omega

theorem source_deficit_gap {N t : ℕ} (hN : 0<N) (ht : t≤canonicalIndex N) :
    ((sourceParameters N t).2.2 : ℝ)-(canonicalParameters N).2.2=
      ((canonicalIndex N*(canonicalIndex N+minimumSideSum N%2)-
        t*(t+minimumSideSum N%2) : ℕ) : ℝ) := by
  let e := minimumSideSum N%2
  let d := (minimumSideSum N/2)*(minimumSideSum N/2+e)-N
  let T := canonicalIndex N
  have hfeas : T*(T+e)≤d := (selectorIndex_bounds d e).1
  have hmono : t*(t+e)≤T*(T+e) := Nat.mul_le_mul ht (Nat.add_le_add_right ht e)
  have hh : d-t*(t+e)=(d-T*(T+e))+(T*(T+e)-t*(t+e)) := by omega
  change ((d-t*(t+e) : ℕ) : ℝ)-((d-T*(T+e) : ℕ) : ℝ)=_
  rw [hh,Nat.cast_add]
  ring

theorem source_absorption_of_coupled {N t : ℕ} (hN : 0<N)
    (hR : 4≤(canonicalParameters N).1) (ht : t<canonicalIndex N)
    (hbound : error (sourceParameters N t).1 (sourceParameters N t).2.1-
      error (canonicalParameters N).1 (canonicalParameters N).2.1 ≤
      (((sourceParameters N t).1*(sourceParameters N t).2.1-
        (canonicalParameters N).1*(canonicalParameters N).2.1 : ℕ) : ℝ)/
        (2*((canonicalParameters N).1 : ℝ)^2*((sourceParameters N t).1 : ℝ)^2)+
      1/(4*((sourceParameters N t).1 : ℝ)^4)+1/(4*((canonicalParameters N).1 : ℝ)^4)) :
    error (sourceParameters N t).1 (sourceParameters N t).2.1-
      error (canonicalParameters N).1 (canonicalParameters N).2.1 <
      (((sourceParameters N t).2.2 : ℝ)-(canonicalParameters N).2.2)*
        correction (faceRectangle ((sourceParameters N t).1-1)
          ((sourceParameters N t).2.1-1)) {(0,0)} := by
  have hsize := canonical_size_relation hN
  change (canonicalIndex N)^2-canonicalIndex N+
    canonicalIndex N*(minimumSideSum N%2)+(canonicalParameters N).2.2+1≤
      (canonicalParameters N).1 at hsize
  rw [source_area_gap hN ht.le] at hbound
  rw [source_deficit_gap hN ht.le]
  exact NormalizedErrorAssembly.normalized_error_of_coupled hR (by omega) ht
    (source_short_eq hN ht.le) (source_hull_facts hN ht.le).ordered hbound

end
end SpanningTreeIsoperimetry.NormalizedSourceError
