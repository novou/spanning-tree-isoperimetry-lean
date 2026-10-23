module

public import SpanningTreeIsoperimetry.SecondProfileCurvature
public import SpanningTreeIsoperimetry.SecondProfileModular

@[expose] public section

set_option backward.privateInPublic true

/-! Actual second-profile symmetry and curvature imply the coupled hull cost. -/
namespace SpanningTreeIsoperimetry.SecondProfileComparison

open Set Filter RectangularSecondProfile SecondProfileCalculus SecondProfileCurvature
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem K2D1_one_zero : K2D1 1=0 := by
  have hd := hasDerivAt_K2 (by norm_num : (0 : ℝ)<1)
  have hd' : HasDerivAt K2 (K2D1 1) ((1 : ℝ)⁻¹) := by simpa only [inv_one] using hd
  have hi : HasDerivAt (fun u : ℝ => u⁻¹) (-1) 1 := by
    simpa using hasDerivAt_inv (by norm_num : (1 : ℝ)≠0)
  have hc : HasDerivAt (fun u : ℝ => K2 (u⁻¹)) (-K2D1 1) 1 := by
    convert! hd'.scomp 1 hi using 1 <;> simp
  have he : K2=ᶠ[𝓝 (1 : ℝ)] (fun u => K2 (u⁻¹)) := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ)<1)] with u hu
    exact (SecondProfileModular.K2_inv hu).symm
  have hh := hd.unique (hc.congr_of_eventuallyEq he)
  linarith

private theorem hasDerivAt_offset {u : ℝ} (hu : 0<u) :
    HasDerivAt (fun v : ℝ => K2D1 v-(v-1)) (K2D2 u-1) u :=
  (hasDerivAt_K2D1 hu).fun_sub ((hasDerivAt_id u).sub_const 1)

private theorem offset_strictAnti : StrictAntiOn (fun u : ℝ => K2D1 u-(u-1)) (Icc 1 3) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 1 3)
  · intro u hu
    exact (hasDerivAt_offset (by linarith [hu.1] : 0<u)).continuousAt.continuousWithinAt
  · intro u hu
    have hu' : u∈Ioo 1 3 := by simpa only [interior_Icc] using hu
    rw [(hasDerivAt_offset (by linarith [hu'.1] : 0<u)).deriv]
    have h := K2D2_lt_one ⟨hu'.1.le,hu'.2.le⟩
    linarith

theorem K2D1_lt_offset {u : ℝ} (hu : u∈Ioc 1 3) : K2D1 u<u-1 := by
  have h := offset_strictAnti (show (1 : ℝ)∈Icc 1 3 by norm_num) ⟨hu.1.le,hu.2⟩ hu.1
  dsimp only at h
  rw [K2D1_one_zero] at h
  linarith

private theorem hasDerivAt_adjusted {u : ℝ} (hu : 0<u) :
    HasDerivAt (fun v : ℝ => K2 v-(v-1)^2/2) (K2D1 u-(u-1)) u := by
  have hp : HasDerivAt (fun v : ℝ => (v-1)^2/2) (u-1) u := by
    convert (((hasDerivAt_id u).sub_const 1).fun_pow 2).div_const 2 using 1 <;>
      simp only [id_eq,Nat.cast_ofNat,pow_one,mul_one] <;> ring
  exact (hasDerivAt_K2 hu).fun_sub hp

theorem adjusted_strictAnti : StrictAntiOn (fun u : ℝ => K2 u-(u-1)^2/2) (Icc 1 3) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 1 3)
  · intro u hu
    exact (hasDerivAt_adjusted (by linarith [hu.1] : 0<u)).continuousAt.continuousWithinAt
  · intro u hu
    have hu' : u∈Ioo 1 3 := by simpa only [interior_Icc] using hu
    rw [(hasDerivAt_adjusted (by linarith [hu'.1] : 0<u)).deriv]
    have h := K2D1_lt_offset ⟨hu'.1,hu'.2.le⟩
    linarith

theorem K2_difference_lt {a b : ℝ} (ha : 1≤a) (hab : a<b) (hb : b≤3) :
    K2 b-K2 a<((b-1)^2-(a-1)^2)/2 := by
  have h := adjusted_strictAnti ⟨ha,hab.le.trans hb⟩ ⟨ha.trans hab.le,hb⟩ hab
  dsimp only at h
  linarith

/-- The actual profile comparison at equal perimeter; all analytic hypotheses
come from the genuine series, modular symmetry and checked curvature bounds. -/
theorem coupled_profile_lt {R r s S : ℝ} (hR : 0<R) (hRr : R<r) (hrs : r≤s) (hsS : s≤S)
    (hsum : r+s=R+S) (haspect : S≤3*R) :
    (K2 (S/R)-K2 (s/r))/(r+s)^2<(r*s-R*S)/(2*R^2*r^2) := by
  have hr : 0<r := hR.trans hRr
  have hs : 0<s := hr.trans_le hrs
  have hS : 0<S := hs.trans_le hsS
  have hL : 0<r+s := by linarith
  have hu : 1≤s/r := (one_le_div hr).mpr hrs
  have hv : S/R≤3 := (div_le_iff₀ hR).mpr haspect
  have huv : s/r<S/R := by
    apply (div_lt_div_iff₀ hr hR).mpr
    exact (mul_lt_mul_of_pos_left hRr hs).trans_le (mul_le_mul_of_nonneg_right hsS hr.le)
  have hprofile := K2_difference_lt hu huv hv
  have hd := div_lt_div_of_pos_right hprofile (sq_pos_of_pos hL)
  have hid : (((S/R-1)^2-(s/r-1)^2)/2)/(r+s)^2=
      (r*s-R*S)/(2*R^2*r^2)-((r-R)*(s-r)*(S-R))/(2*(r+s)*R^2*r^2) := by
    have hSe : S=r+s-R := by linarith
    rw [hSe]
    field_simp [hR.ne',hr.ne',hL.ne'] <;> ring
  rw [hid] at hd
  have hdelta : 0≤r-R := sub_nonneg.mpr hRr.le
  have hsr : 0≤s-r := sub_nonneg.mpr hrs
  have hSR : 0≤S-R := by linarith
  have hnonneg : 0≤((r-R)*(s-r)*(S-R))/(2*(r+s)*R^2*r^2) := by positivity
  linarith

end
end SpanningTreeIsoperimetry.SecondProfileComparison
