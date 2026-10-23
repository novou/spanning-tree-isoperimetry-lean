module

public import SpanningTreeIsoperimetry.LargeImbalanceScalarChecks
public import SpanningTreeIsoperimetry.LargeImbalanceGeometry
public import SpanningTreeIsoperimetry.RefinedCornerEnvelope

@[expose] public section

/-! The normalized corner test at the actual canonical selector parameters.
This closes the scalar side of large-imbalance exclusion; the finite rectangle
error absorption is a separate count-comparison interface. -/
namespace SpanningTreeIsoperimetry.LargeImbalanceTest
open Ferrers CornerEnergy FluxBounds AspectCost LargeImbalanceBounds
open LargeImbalanceGeometry LargeImbalanceScalarChecks CanonicalRectangleBounds
open RefinedCornerEnvelope
noncomputable section
set_option maxHeartbeats 1000000

theorem bound_of_nine_le {k : ℕ} (hk : 9≤k) : bound k=(7421 : ℝ)/100000 := by
  simp [bound,show k≠2 by omega,show k≠3 by omega,show k≠4 by omega,
    show k≠6 by omega,show k≠8 by omega]

theorem bound_ge_seven {k : ℕ} (hk : 7≤k) : (7054 : ℝ)/100000≤bound k := by
  unfold bound
  split_ifs <;> norm_num <;> omega

theorem parameter_test {T e R S j k : ℕ} (hT : 4≤T) (he : e≤1)
    (hj : j≤2*T+e) (hsize : T^2-T+T*e+j+1≤R) (hside : S=R+2*T+e)
    (hk : 2*T+e-1+j≤k) :
    realEnergy (horizontalStrip j)+D ((2*(T : ℝ)+e)/R)+fluxBound R S j < bound k := by
  have ha := canonical_aspect_bound hT he hj hsize
  have hratio0 : (0 : ℝ)≤(2*(T : ℝ)+e)/R := by positivity
  by_cases hT4 : T=4
  · subst T
    have hj9 : j≤9 := by omega
    have hsize' : 12+4*e+j+1≤R := by simpa using hsize
    have hside' : S=R+8+e := by simpa using hside
    have hB := four_flux_bound he (by simpa using hj) hsize' hside'
    norm_num at ha hratio0 ⊢
    simp only [show (12 : ℝ)+j+1=13+j by ring] at ha
    have hD := D_mono_nonneg hratio0 ha
    have hh := actual_four_cost ⟨j,by omega⟩
    change realEnergy (horizontalStrip j)+D (8/(13+(j : ℝ)))+fluxBound 22 30 9 <
      if j≤1 then (7054 : ℝ)/100000 else 7421/100000 at hh
    by_cases hj1 : j≤1
    · rw [if_pos hj1] at hh
      have hb := bound_ge_seven (show 7≤k by omega)
      linarith
    · rw [if_neg hj1] at hh
      rw [bound_of_nine_le (show 9≤k by omega)]
      linarith
  · have hT5 : 5≤T := by omega
    have hk9 : 9≤k := by omega
    rw [bound_of_nine_le hk9]
    have ht2 : T≤T^2 := by simpa only [pow_two] using Nat.le_mul_self T
    have hweak : T^2-T+j+1≤R := by omega
    have hr : (T : ℝ)^2-T+j+1≤R := by
      have hh : ((T^2-T+j+1 : ℕ) : ℝ)≤R := by exact_mod_cast hweak
      simpa only [Nat.cast_add,Nat.cast_sub ht2,Nat.cast_pow,Nat.cast_one] using hh
    have hB := fluxBound_large_imbalance (T := (T : ℝ)) (r := (R : ℝ)) (s := (S : ℝ))
      (k := (j : ℝ)) (by exact_mod_cast hT) (Nat.cast_nonneg j)
      (by exact_mod_cast (show j≤2*T+1 by omega)) hr
      (by exact_mod_cast (show R+j≤S by omega))
    change fluxBound R S j<fluxCap T at hB
    by_cases hj11 : j≤11
    · have har := aspect_ratio_five (T := (T : ℝ)) (j := (j : ℝ))
        (by exact_mod_cast hT5) (Nat.cast_nonneg j) (by exact_mod_cast hj11)
      have hD := D_mono_nonneg hratio0 (ha.trans har)
      have hb := fluxCap_antitone (a := (5 : ℝ)) (b := (T : ℝ))
        (by norm_num) (by exact_mod_cast hT5)
      have hh := actual_five_cost ⟨j,by omega⟩
      change realEnergy (horizontalStrip j)+D (10/(21+(j : ℝ)))+fluxCap 5 <
        (7421 : ℝ)/100000 at hh
      linarith
    · have hj12 : 12≤j := by omega
      have hT6 : 6≤T := by omega
      have har := aspect_ratio_tail (T := (T : ℝ)) (j := (j : ℝ))
        (by exact_mod_cast hT6) (by exact_mod_cast hj12)
      have hD := D_mono_nonneg hratio0 (ha.trans har)
      have hb := fluxCap_antitone (a := (6 : ℝ)) (b := (T : ℝ))
        (by norm_num) (by exact_mod_cast hT6)
      have hh := actual_tail_cost j
      linarith

/-- The exact scalar inequality in the manuscript's normalized corner test,
with all selector arithmetic discharged for the actual cardinality N. -/
theorem actual_selector_test {N t : ℕ} (hN : 0<N) :
    let L := minimumSideSum N
    let m := L/2
    let e := L%2
    let d := m*(m+e)-N
    let T := selectorIndex d e
    let R := (canonicalParameters N).1
    let S := (canonicalParameters N).2.1
    let j := (canonicalParameters N).2.2
    4≤T → t<T →
      realEnergy (horizontalStrip j)+D ((2*(T : ℝ)+e)/R)-
        D ((2*(t : ℝ)+e)/(m-t : ℕ))+fluxBound R S j < bound (d-t*(t+e)) := by
  let L := minimumSideSum N
  let m := L/2
  let e := L%2
  let d := m*(m+e)-N
  let T := selectorIndex d e
  let R := (canonicalParameters N).1
  let S := (canonicalParameters N).2.1
  let j := (canonicalParameters N).2.2
  change 4≤T → t<T → realEnergy (horizontalStrip j)+D ((2*(T : ℝ)+e)/R)-
    D ((2*(t : ℝ)+e)/(m-t : ℕ))+fluxBound R S j < bound (d-t*(t+e))
  intro hT ht
  have he : e≤1 := by dsimp [e]; omega
  have hj0 := selector_remainder_lt_step (selectorIndex_bounds d e).1 (selectorIndex_bounds d e).2
  change j<2*T+e+1 at hj0
  have hj : j≤2*T+e := by omega
  have hsize := canonical_size_relation hN
  change T^2-T+T*e+j+1≤R at hsize
  have hpos := (canonical_flux_hypotheses hN).1
  change 0<R at hpos
  have hR : R=m-T := rfl
  have hS : S=m+e+T := rfl
  have hside : S=R+2*T+e := by rw [hR,hS]; rw [hR] at hpos; omega
  have hk := source_deficit_lower (selectorIndex_bounds d e).1 ht
  change 2*T+e-1+j≤d-t*(t+e) at hk
  have hh := parameter_test hT he hj hsize hside hk
  have hsource : 0≤D ((2*(t : ℝ)+e)/(m-t : ℕ)) := D_nonneg (by positivity)
  linarith

end
end SpanningTreeIsoperimetry.LargeImbalanceTest
