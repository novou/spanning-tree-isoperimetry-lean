module

public import SpanningTreeIsoperimetry.CanonicalRectangleBounds
public import SpanningTreeIsoperimetry.CanonicalStrips

@[expose] public section

/-! Actual canonical-selector geometry at the short deficits used by the
finite concentration comparison. Side lengths here are primal lengths. -/
namespace SpanningTreeIsoperimetry.CanonicalConcentrationArithmetic
open CanonicalRectangleBounds

theorem parameters_properties {N r s k : ℕ} (hN : 0<N) (hp : canonicalParameters N=(r,s,k)) :
    0<r ∧ r≤s ∧ r+s=minimumSideSum N ∧ r*s=N+k ∧ k<r := by
  have h := selected_hull_properties_of_ceil hN
  change 0<(canonicalParameters N).1 ∧ (canonicalParameters N).1≤(canonicalParameters N).2.1 ∧
    (canonicalParameters N).1+(canonicalParameters N).2.1=minimumSideSum N ∧
    (canonicalParameters N).1*(canonicalParameters N).2.1=N+(canonicalParameters N).2.2 ∧
    (canonicalParameters N).2.2<(canonicalParameters N).1 at h
  simpa only [hp] using h

theorem selector_data {N r s k : ℕ} (hN : 0<N) (hp : canonicalParameters N=(r,s,k)) :
    ∃ T e : ℕ, e≤1 ∧ k≤2*T+e ∧ r+2*T+e=s ∧ T^2-T+T*e+k+1≤r := by
  let L := minimumSideSum N
  let m := L/2
  let e := L%2
  let d := m*(m+e)-N
  let T := selectorIndex d e
  have he : e≤1 := by dsimp [e]; omega
  have hr := congrArg Prod.fst hp
  have hs := congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) hp
  have hk := congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hp
  change m-T=r at hr
  change m+e+T=s at hs
  change d-T*(T+e)=k at hk
  have hstep := selector_remainder_lt_step (selectorIndex_bounds d e).1 (selectorIndex_bounds d e).2
  change d-T*(T+e)<2*T+e+1 at hstep
  rw [hk] at hstep
  have hsize := canonical_size_relation hN
  change T^2-T+T*e+(canonicalParameters N).2.2+1≤(canonicalParameters N).1 at hsize
  rw [hp] at hsize
  have hr0 := (parameters_properties hN hp).1
  have hTm : T≤m := by omega
  have hback := Nat.sub_add_cancel hTm
  exact ⟨T,e,he,by omega,by omega,hsize⟩

theorem canonical_gap {N r s k : ℕ} (hN : 0<N) (hp : canonicalParameters N=(r,s,k)) : r+k≤s := by
  obtain ⟨T,e,he,hstep,hside,hsize⟩ := selector_data hN hp
  omega

theorem canonical_two_min {N r s : ℕ} (hN : 18≤N) (hp : canonicalParameters N=(r,s,2)) : 4≤r := by
  obtain ⟨T,e,he,hstep,hside,hsize⟩ := selector_data (by omega) hp
  have hprop := parameters_properties (by omega) hp
  have hsub : T^2-T+T=T^2 := Nat.sub_add_cancel (by simpa only [pow_two] using Nat.le_mul_self T)
  by_contra hn
  have hr : r=3 := by omega
  interval_cases e
  · norm_num at hstep hside hsize
    have hT0 : 1≤T := by omega
    have hT1 : T=1 := by
      by_contra hnot
      have hT2 : 2≤T := by omega
      have hm := Nat.mul_le_mul_right T hT2
      nlinarith
    have hs : s=5 := by omega
    rw [hr,hs] at hprop
    omega
  · norm_num at hstep hside hsize
    have hT0 : 1≤T := by omega
    have hm := Nat.mul_le_mul hT0 hT0
    nlinarith

theorem canonical_three_min {N r s : ℕ} (hN : 0<N) (hp : canonicalParameters N=(r,s,3)) : 5≤r := by
  obtain ⟨T,e,he,hstep,hside,hsize⟩ := selector_data hN hp
  have hsub : T^2-T+T=T^2 := Nat.sub_add_cancel (by simpa only [pow_two] using Nat.le_mul_self T)
  interval_cases e
  · norm_num at hstep hsize
    have hT : 2≤T := by omega
    have hm := Nat.mul_le_mul_right T hT
    nlinarith
  · norm_num at hstep hsize
    have hT : 1≤T := by omega
    have hm := Nat.mul_le_mul hT hT
    nlinarith

theorem canonical_four_min {N r s : ℕ} (hN : 0<N) (hp : canonicalParameters N=(r,s,4)) : 7≤r := by
  obtain ⟨T,e,he,hstep,hside,hsize⟩ := selector_data hN hp
  have hsub : T^2-T+T=T^2 := Nat.sub_add_cancel (by simpa only [pow_two] using Nat.le_mul_self T)
  interval_cases e
  · norm_num at hstep hsize
    have hT : 2≤T := by omega
    have hm := Nat.mul_le_mul_right T hT
    nlinarith
  · norm_num at hstep hsize
    have hT : 2≤T := by omega
    have hm := Nat.mul_le_mul hT hT
    nlinarith

theorem canonical_five_min {N r s : ℕ} (hN : 0<N) (hp : canonicalParameters N=(r,s,5)) : 10≤r := by
  obtain ⟨T,e,he,hstep,hside,hsize⟩ := selector_data hN hp
  have hsub : T^2-T+T=T^2 := Nat.sub_add_cancel (by simpa only [pow_two] using Nat.le_mul_self T)
  interval_cases e
  · norm_num at hstep hsize
    have hT : 3≤T := by omega
    have hm := Nat.mul_le_mul_right T hT
    nlinarith
  · norm_num at hstep hsize
    have hT : 2≤T := by omega
    have hm := Nat.mul_le_mul hT hT
    nlinarith

theorem canonical_six_min {N r s : ℕ} (hN : 0<N) (hp : canonicalParameters N=(r,s,6)) : 13≤r := by
  obtain ⟨T,e,he,hstep,hside,hsize⟩ := selector_data hN hp
  have hsub : T^2-T+T=T^2 := Nat.sub_add_cancel (by simpa only [pow_two] using Nat.le_mul_self T)
  interval_cases e
  · norm_num at hstep hsize
    have hT : 3≤T := by omega
    have hm := Nat.mul_le_mul_right T hT
    nlinarith
  · norm_num at hstep hsize
    have hT : 3≤T := by omega
    have hm := Nat.mul_le_mul hT hT
    nlinarith

end SpanningTreeIsoperimetry.CanonicalConcentrationArithmetic
