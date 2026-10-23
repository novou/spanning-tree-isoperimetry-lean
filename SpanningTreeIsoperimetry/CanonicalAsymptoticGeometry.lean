module

public import SpanningTreeIsoperimetry.CanonicalCountExpansion
public import SpanningTreeIsoperimetry.FluxBounds

@[expose] public section

/-! Actual canonical-selector bounds at the scale needed for the extremal
asymptotic. No rate for a hypothetical hull is assumed. -/
namespace SpanningTreeIsoperimetry.CanonicalAsymptoticGeometry
open Ferrers CornerEnergy CanonicalCountExpansion CanonicalConcentrationArithmetic
open CanonicalRectangleBounds Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000

def shortSide (N : ℕ) : ℕ := (canonicalParameters N).1
def longSide (N : ℕ) : ℕ := (canonicalParameters N).2.1
def stripLength (N : ℕ) : ℕ := (canonicalParameters N).2.2
def aspect (N : ℕ) : ℝ := (longSide N : ℝ)/shortSide N

theorem parameters (N : ℕ) : canonicalParameters N=(shortSide N,longSide N,stripLength N) := rfl

theorem properties {N : ℕ} (hN : 0<N) :
    0<shortSide N ∧ shortSide N≤longSide N ∧ shortSide N+longSide N=minimumSideSum N ∧
      shortSide N*longSide N=N+stripLength N ∧ stripLength N<shortSide N :=
  parameters_properties hN (parameters N)

theorem long_le_three_short {N : ℕ} (hN : 0<N) : longSide N≤3*shortSide N := by
  have hp := properties hN
  exact admissible_aspect_le_three (ceil_sqrt_is_minimum_side_sum hN) hp.1
    (hp.1.trans_le hp.2.1) (by omega) hp.2.2.1

theorem area_le_three_short_sq {N : ℕ} (hN : 0<N) : N≤3*(shortSide N)^2 := by
  have hp := properties hN
  have hm := Nat.mul_le_mul_left (shortSide N) (long_le_three_short hN)
  have harea := hp.2.2.2.1
  nlinarith

theorem shortSide_tendsto : Tendsto shortSide atTop atTop := by
  refine tendsto_atTop.2 (fun b => ?_)
  filter_upwards [eventually_ge_atTop (3*b^2+1)] with N hN
  have hp := area_le_three_short_sq (show 0<N by omega)
  by_contra hh
  have hle : shortSide N≤b := by omega
  have hsq := Nat.mul_le_mul hle hle
  nlinarith

theorem aspect_ge_one {N : ℕ} (hN : 0<N) : 1≤aspect N := by
  have hp := properties hN
  exact (one_le_div (by exact_mod_cast hp.1 : (0 : ℝ)<shortSide N)).mpr (by exact_mod_cast hp.2.1)

theorem aspect_offset_sq_le {N : ℕ} (hN : 0<N) :
    (aspect N-1)^2≤18/(shortSide N : ℝ) := by
  obtain ⟨T,e,he,hk,hside,hsize⟩ := selector_data hN (parameters N)
  have hp := properties hN
  have hr0 : (0 : ℝ)<shortSide N := by exact_mod_cast hp.1
  have hr1 : (1 : ℝ)≤shortSide N := by exact_mod_cast (show 1≤shortSide N by omega)
  have hweak : T^2-T+1≤shortSide N := by omega
  have ht2 : T≤T^2 := by simpa only [pow_two] using Nat.le_mul_self T
  have hcast : (T : ℝ)^2-T+1≤shortSide N := by
    have hh : ((T^2-T+1 : ℕ) : ℝ)≤shortSide N := by exact_mod_cast hweak
    simpa only [Nat.cast_add,Nat.cast_sub ht2,Nat.cast_pow,Nat.cast_one] using hh
  have hT2 : (T : ℝ)^2≤2*shortSide N := by nlinarith [sq_nonneg ((T : ℝ)-1)]
  have heR : (e : ℝ)≤1 := by exact_mod_cast he
  have hT0 : (0 : ℝ)≤T := Nat.cast_nonneg T
  have he0 : (0 : ℝ)≤e := Nat.cast_nonneg e
  have hdelta : (2*(T : ℝ)+e)^2≤(2*(T : ℝ)+1)^2 := by gcongr
  have hnum : (2*(T : ℝ)+e)^2≤18*shortSide N := by
    nlinarith [sq_nonneg (2*(T : ℝ)-1)]
  have hsideR : (shortSide N : ℝ)+2*T+e=longSide N := by exact_mod_cast hside
  have hoff : aspect N-1=(2*(T : ℝ)+e)/shortSide N := by
    unfold aspect
    rw [← hsideR]
    field_simp [hr0.ne'] <;> ring
  rw [hoff,div_pow]
  calc
    _≤(18*(shortSide N : ℝ))/(shortSide N : ℝ)^2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _=_ := by field_simp [hr0.ne'] <;> ring

theorem reciprocal_short_tendsto :
    Tendsto (fun N => (shortSide N : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp shortSide_tendsto)

theorem aspect_tendsto : Tendsto aspect atTop (𝓝 1) := by
  have hb : Tendsto (fun N => Real.sqrt (18/(shortSide N : ℝ))) atTop (𝓝 0) := by
    have hi : Tendsto (fun N => (18 : ℝ)*(shortSide N : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using reciprocal_short_tendsto.const_mul 18
    have hh := (Real.continuous_sqrt.tendsto 0).comp hi
    simpa only [Function.comp_def,Real.sqrt_zero,div_eq_mul_inv] using hh
  have hd : Tendsto (fun N => aspect N-1) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hb
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (aspect_ge_one (by omega)))]
    exact Real.le_sqrt_of_sq_le (aspect_offset_sq_le (by omega))
  exact tendsto_sub_nhds_zero_iff.mp hd

theorem reciprocal_short_le_sqrt {N : ℕ} (hN : 0<N) :
    1/(shortSide N : ℝ)≤2/Real.sqrt (N : ℝ) := by
  have hr : (0 : ℝ)<shortSide N := by exact_mod_cast (properties hN).1
  have hN' : (0 : ℝ)<N := by exact_mod_cast hN
  have ha : (N : ℝ)≤3*(shortSide N : ℝ)^2 := by exact_mod_cast area_le_three_short_sq hN
  have hs : Real.sqrt (N : ℝ)≤2*shortSide N := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (shortSide N : ℝ)]
  apply (div_le_div_iff₀ hr (Real.sqrt_pos.mpr hN')).mpr
  simpa only [one_mul] using hs

theorem short_sq_le_two_area {N : ℕ} (hN : 0<N) : (shortSide N : ℝ)^2≤2*N := by
  have hp := properties hN
  have hr : (0 : ℝ)<shortSide N := by exact_mod_cast hp.1
  have harea : (shortSide N : ℝ)*longSide N=(N : ℝ)+stripLength N := by exact_mod_cast hp.2.2.2.1
  have horder : (shortSide N : ℝ)≤longSide N := by exact_mod_cast hp.2.1
  have hk : (stripLength N : ℝ)+1≤shortSide N := by
    exact_mod_cast (show stripLength N+1≤shortSide N by omega)
  have hmul := mul_le_mul_of_nonneg_left horder hr.le
  nlinarith [sq_nonneg ((shortSide N : ℝ)-1)]

theorem stripLength_sq_le_short {N : ℕ} (hN : 0<N) :
    (stripLength N : ℝ)^2≤18*shortSide N := by
  have hr : (0 : ℝ)<shortSide N := by exact_mod_cast (properties hN).1
  have hgap := canonical_gap hN (parameters N)
  have hgapR : (stripLength N : ℝ)+shortSide N≤longSide N := by
    exact_mod_cast (show stripLength N+shortSide N≤longSide N by omega)
  have hd := div_le_div_of_nonneg_right hgapR hr.le
  rw [add_div,div_self hr.ne'] at hd
  have hk : (stripLength N : ℝ)/shortSide N≤aspect N-1 := by unfold aspect; linarith
  have hs := (pow_le_pow_left₀ (by positivity : (0 : ℝ)≤(stripLength N : ℝ)/shortSide N) hk 2).trans
    (aspect_offset_sq_le hN)
  rw [div_pow] at hs
  calc
    (stripLength N : ℝ)^2≤(18/(shortSide N : ℝ))*(shortSide N : ℝ)^2 :=
      (div_le_iff₀ (pow_pos hr 2)).mp hs
    _=18*shortSide N := by field_simp [hr.ne'] <;> ring

/-- An explicit polynomial form of the selected-strip O(N^(1/4)) bound. -/
theorem stripLength_fourth_le_area {N : ℕ} (hN : 0<N) : (stripLength N : ℝ)^4≤648*N := by
  have hk := stripLength_sq_le_short hN
  have hr := short_sq_le_two_area hN
  calc
    (stripLength N : ℝ)^4=((stripLength N : ℝ)^2)^2 := by ring
    _≤(18*(shortSide N : ℝ))^2 := pow_le_pow_left₀ (sq_nonneg _) hk 2
    _≤648*N := by nlinarith

theorem log_area_ratio_bound {N : ℕ} (hN : 0<N) :
    |Real.log (1+(stripLength N : ℝ)/N)|≤2/(shortSide N : ℝ) := by
  have hp := properties hN
  have hr : (0 : ℝ)<shortSide N := by exact_mod_cast hp.1
  have hN' : (0 : ℝ)<N := by exact_mod_cast hN
  have hk : (stripLength N : ℝ)+1≤shortSide N := by
    exact_mod_cast (show stripLength N+1≤shortSide N by omega)
  have hNlower := short_sq_le_two_area hN
  have hratio : (stripLength N : ℝ)/N≤2/(shortSide N : ℝ) := by
    apply (div_le_div_iff₀ hN' hr).mpr
    have hprod := mul_le_mul_of_nonneg_right (show (stripLength N : ℝ)≤shortSide N by linarith) hr.le
    nlinarith
  have hnonneg : 0≤Real.log (1+(stripLength N : ℝ)/N) := Real.log_nonneg (by
    have hh : 0≤(stripLength N : ℝ)/N := by positivity
    linarith)
  rw [abs_of_nonneg hnonneg]
  have hh := Real.log_le_sub_one_of_pos (show 0<1+(stripLength N : ℝ)/N by positivity)
  linarith

theorem stripCorrection_le_reciprocal {N : ℕ} (hN : 0<N) (hr4 : 4≤shortSide N) :
    |stripCorrection N|≤(16*Real.pi^3/45)/(shortSide N : ℝ) := by
  have hp := properties hN
  have hrR : (4 : ℝ)≤shortSide N := by exact_mod_cast hr4
  have hr0 : (0 : ℝ)<shortSide N := by linarith
  have hk : (stripLength N : ℝ)+1≤shortSide N := by
    exact_mod_cast (show stripLength N+1≤shortSide N by omega)
  have hgap := canonical_gap hN (parameters N)
  have hB := FluxBounds.fluxBound_lt_fourth (r := (shortSide N : ℝ))
    (s := (longSide N : ℝ)) (k := (stripLength N : ℝ)) (by linarith)
    (Nat.cast_nonneg _) (by exact_mod_cast hgap)
  have hupper : FluxBounds.fluxBound (shortSide N) (longSide N) (stripLength N)≤
      (16*Real.pi^3/45)/(shortSide N : ℝ) := by
    apply hB.le.trans
    calc
      _≤Real.pi^3/45*((shortSide N : ℝ)^3/((shortSide N : ℝ)/2)^4) := by
        gcongr <;> linarith
      _=_ := by field_simp [hr0.ne'] <;> ring
  obtain ⟨h0,hb⟩ := stripCorrection_bounds hN (parameters N) (by omega)
  rw [abs_of_nonneg h0]
  exact hb.trans hupper

end
end SpanningTreeIsoperimetry.CanonicalAsymptoticGeometry
