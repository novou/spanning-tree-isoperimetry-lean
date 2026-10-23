module

public import SpanningTreeIsoperimetry.NormalizedSourceError
public import SpanningTreeIsoperimetry.LargeImbalanceCountBridge

@[expose] public section

/-! Exact selector coordinates for the small single-corner reductions. -/
namespace SpanningTreeIsoperimetry.SingleCornerSelectorGeometry
open SourceHullArithmetic NormalizedSourceError CanonicalRectangleBounds
open CrossHullCountComparison
noncomputable section

theorem canonical_data {N : ℕ} (hN : 0<N) :
    let T := canonicalIndex N
    let e := minimumSideSum N%2
    let R := (canonicalParameters N).1
    let S := (canonicalParameters N).2.1
    let j := (canonicalParameters N).2.2
    S=R+2*T+e ∧ j≤2*T+e ∧ T^2-T+T*e+j+1≤R := by
  have hs := (source_hull_facts hN (le_refl (canonicalIndex N))).side_difference
  rw [source_at_canonical] at hs
  have hsize := canonical_size_relation hN
  let e := minimumSideSum N%2
  let d := minimumSideSum N/2*(minimumSideSum N/2+e)-N
  have hj := selector_remainder_lt_step (selectorIndex_bounds d e).1 (selectorIndex_bounds d e).2
  change (canonicalParameters N).2.2<2*canonicalIndex N+e+1 at hj
  exact ⟨hs,by omega,hsize⟩

theorem source_deficit_eq {N t : ℕ} (hN : 0<N) (ht : t≤canonicalIndex N) :
    (sourceParameters N t).2.2=(canonicalParameters N).2.2+
      (canonicalIndex N-t)*(canonicalIndex N+t+minimumSideSum N%2) := by
  let e := minimumSideSum N%2
  let d := minimumSideSum N/2*(minimumSideSum N/2+e)-N
  let T := canonicalIndex N
  have hfeas : T*(T+e)≤d := (selectorIndex_bounds d e).1
  let g := T-t
  have hT : T=g+t := by dsimp [g]; omega
  have hid : T*(T+e)=t*(t+e)+g*(T+t+e) := by rw [hT]; ring
  change d-t*(t+e)=(d-T*(T+e))+g*(T+t+e)
  omega

theorem two_middle_data {N : ℕ} (hN : 0<N) (hT : canonicalIndex N=2) :
    let e := minimumSideSum N%2
    let R := (canonicalParameters N).1
    let j := (canonicalParameters N).2.2
    let r := (sourceParameters N 1).1
    let s := (sourceParameters N 1).2.1
    let k := (sourceParameters N 1).2.2
    r=R+1 ∧ s=r+2+e ∧ k=j+3+e ∧ j≤4+e ∧ j+4+2*e≤r := by
  have hc := canonical_data hN
  have hr := source_short_eq hN (show 1≤canonicalIndex N by omega)
  have hs := (source_hull_facts hN (show 1≤canonicalIndex N by omega)).side_difference
  have hk := source_deficit_eq hN (show 1≤canonicalIndex N by omega)
  rw [hT] at hc hr hk
  norm_num at hc hr hs hk
  dsimp only
  omega

theorem three_data {N : ℕ} (hN : 0<N) (hT : canonicalIndex N=3) :
    let e := minimumSideSum N%2
    let R := (canonicalParameters N).1
    let S := (canonicalParameters N).2.1
    let j := (canonicalParameters N).2.2
    S=R+6+e ∧ j≤6+e ∧ j+7+3*e≤R := by
  have hc := canonical_data hN
  rw [hT] at hc
  norm_num at hc
  dsimp only
  omega

theorem three_first_data {N : ℕ} (hN : 0<N) (hT : canonicalIndex N=3) :
    let e := minimumSideSum N%2
    let R := (canonicalParameters N).1
    let j := (canonicalParameters N).2.2
    let r := (sourceParameters N 1).1
    let s := (sourceParameters N 1).2.1
    let k := (sourceParameters N 1).2.2
    r=R+2 ∧ s=r+2+e ∧ k=j+8+2*e ∧ j+9+3*e≤r := by
  have hc := three_data hN hT
  have hr := source_short_eq hN (show 1≤canonicalIndex N by omega)
  have hs := (source_hull_facts hN (show 1≤canonicalIndex N by omega)).side_difference
  have hk := source_deficit_eq hN (show 1≤canonicalIndex N by omega)
  rw [hT] at hr hk
  norm_num at hc hr hs hk
  dsimp only
  omega

theorem three_second_data {N : ℕ} (hN : 0<N) (hT : canonicalIndex N=3) :
    let e := minimumSideSum N%2
    let R := (canonicalParameters N).1
    let j := (canonicalParameters N).2.2
    let r := (sourceParameters N 2).1
    let s := (sourceParameters N 2).2.1
    let k := (sourceParameters N 2).2.2
    r=R+1 ∧ s=r+4+e ∧ k=j+5+e ∧ j+8+3*e≤r := by
  have hc := three_data hN hT
  have hr := source_short_eq hN (show 2≤canonicalIndex N by omega)
  have hs := (source_hull_facts hN (show 2≤canonicalIndex N by omega)).side_difference
  have hk := source_deficit_eq hN (show 2≤canonicalIndex N by omega)
  rw [hT] at hr hk
  norm_num at hc hr hs hk
  dsimp only
  omega

theorem three_odd_source_aspect {N t : ℕ} (hN : 0<N) (hT : canonicalIndex N=3)
    (he : minimumSideSum N%2=1) (ht : 1≤t) (ht2 : t≤2) :
    (3 : ℝ)/((canonicalParameters N).1+2)≤
      aspectOffset (sourceParameters N t).1 (sourceParameters N t).2.1 := by
  have hf := source_hull_facts hN (show t≤canonicalIndex N by omega)
  rw [LargeImbalanceCountBridge.offset_of_sides hf.short_pos hf.side_difference,he]
  interval_cases t
  · have hh := (three_first_data hN hT).1
    rw [hh]
    push_cast
    norm_num
  · have hh := (three_second_data hN hT).1
    rw [hh]
    push_cast
    norm_num
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ)<(canonicalParameters N).1+2)
      (by positivity : (0 : ℝ)<(canonicalParameters N).1+1)).mpr
    have hR := Nat.cast_nonneg (α := ℝ) (canonicalParameters N).1
    nlinarith

end
end SpanningTreeIsoperimetry.SingleCornerSelectorGeometry
