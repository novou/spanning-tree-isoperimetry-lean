import SpanningTreeIsoperimetry.LatticeKernelDerivatives
import Mathlib.Analysis.Calculus.Taylor

/-! Cubic and fifth-order angular-kernel bounds derived from its checked
actual derivative chain and the real Taylor theorem. -/
namespace SpanningTreeIsoperimetry.AngularKernelTaylor

open Set RectangularRemainder LatticeKernelDerivatives
open scoped Interval
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

/-- Concavity of the actual angular kernel on its quadrature interval. -/
theorem gamma_concaveOn : ConcaveOn ℝ (Set.Icc 0 Real.pi) gamma := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := gammaDeriv) (f'' := gammaD2)
    (convex_Icc 0 Real.pi)
  · exact contDiff_gamma.continuous.continuousOn
  · exact fun x _ => (hasDerivAt_gamma x).hasDerivWithinAt
  · exact fun x _ => (hasDerivAt_gammaDeriv x).hasDerivWithinAt
  · intro x hx
    have hx' : x∈Set.Ioo 0 Real.pi := by simpa only [interior_Icc] using hx
    have hs := (halfSin_mem ⟨hx'.1.le,hx'.2.le⟩).1
    have hd := kernelRoot_pos x
    simp only [gammaD2,evenForm,P2,Polynomial.eval_neg,Polynomial.eval_one,mul_neg_one]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (by positivity)

/-- The gamma secant slope decreases. This controls every retained mode as
its rectangle side grows, including the sharp low-mode exponential bounds. -/
theorem gamma_ratio_antitone : AntitoneOn (fun x : ℝ => gamma x/x) (Set.Ioc 0 Real.pi) := by
  intro x hx y hy hxy
  by_cases heq : x=y
  · simp [heq]
  · have hxy' : x<y := lt_of_le_of_ne hxy heq
    have h := gamma_concaveOn.slope_anti_adjacent
      (show (0 : ℝ)∈Set.Icc 0 Real.pi from ⟨le_rfl,Real.pi_pos.le⟩)
      (show y∈Set.Icc 0 Real.pi from ⟨hy.1.le,hy.2⟩) hx.1 hxy'
    rw [gamma_zero,sub_zero,sub_zero] at h
    have hh := (div_le_div_iff₀ (sub_pos.mpr hxy') hx.1).mp h
    apply (div_le_div_iff₀ hy.1 hx.1).mpr
    nlinarith

/-- Increasing the short side increases the scaled angular exponent of each
fixed retained mode. -/
theorem scaled_gamma_mono {r s t : ℝ} (hr : 0<r) (hrs : r≤s) (ht : 0<t)
    (htr : t≤Real.pi*r) : r*gamma (t/r)≤s*gamma (t/s) := by
  have hs : 0<s := hr.trans_le hrs
  have hx : t/s∈Set.Ioc 0 Real.pi := by
    refine ⟨div_pos ht hs,(div_le_iff₀ hs).mpr ?_⟩
    exact htr.trans (mul_le_mul_of_nonneg_left hrs Real.pi_pos.le)
  have hy : t/r∈Set.Ioc 0 Real.pi := ⟨div_pos ht hr,(div_le_iff₀ hr).mpr htr⟩
  have hxy : t/s≤t/r := div_le_div_of_nonneg_left ht.le hr hrs
  have h := gamma_ratio_antitone hx hy hxy
  have hm := mul_le_mul_of_nonneg_left h ht.le
  convert hm using 1 <;> field_simp <;> ring

private theorem within_at_zero {θ : ℝ} (hθ : 0<θ) (n : ℕ) :
    iteratedDerivWithin n gamma (uIcc 0 θ) 0=iteratedDeriv n gamma 0 :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hθ.ne)
    (contDiff_gamma.of_le le_top).contDiffAt (by simp)

private theorem deriv_gamma_zero : deriv gamma 0=1 := by
  rw [(hasDerivAt_gamma 0).deriv]
  norm_num [gammaDeriv]

private theorem taylor_two {θ : ℝ} (hθ : 0<θ) :
    taylorWithinEval gamma 2 (uIcc 0 θ) 0 θ=θ := by
  rw [taylor_within_apply]
  norm_num [Finset.sum_range_succ,within_at_zero hθ,iteratedDeriv_zero,deriv_gamma_zero,
    iteratedDeriv_gamma_one,iteratedDeriv_gamma_two,gamma_zero,gammaD2_zero,gammaDeriv,smul_eq_mul]

private theorem taylor_four {θ : ℝ} (hθ : 0<θ) :
    taylorWithinEval gamma 4 (uIcc 0 θ) 0 θ=θ-θ^3/12 := by
  rw [taylor_within_apply]
  norm_num [Finset.sum_range_succ,within_at_zero hθ,iteratedDeriv_zero,deriv_gamma_zero,
    iteratedDeriv_gamma_one,iteratedDeriv_gamma_two,iteratedDeriv_gamma_three,iteratedDeriv_gamma_four,
    gamma_zero,gammaD2_zero,gammaD3_zero,gammaD4_zero,gammaDeriv,smul_eq_mul]
  ring

/-- The exact lattice kernel differs from its tangent by at most theta³/12. -/
theorem gamma_cubic_defect {θ : ℝ} (hθ : θ∈Set.Icc 0 Real.pi) :
    0≤θ-gamma θ ∧ θ-gamma θ≤θ^3/12 := by
  refine ⟨sub_nonneg.mpr (gamma_le_theta hθ),?_⟩
  by_cases hz : θ=0
  · simp [hz]
  · have hp : 0<θ := lt_of_le_of_ne hθ.1 (Ne.symm hz)
    have hc : ContDiffOn ℝ 3 gamma (uIcc 0 θ) := (contDiff_gamma.of_le le_top).contDiffOn
    obtain ⟨c,hcθ,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hp.ne hc
    have hc' : c∈Set.Ioo 0 θ := by simpa only [uIoo_of_lt hp] using hcθ
    rw [taylor_two hp,iteratedDeriv_gamma_three] at he
    norm_num only [sub_zero,Nat.factorial] at he
    have hb := (abs_le.mp (gammaD3_abs_le ⟨hc'.1.le,hc'.2.le.trans hθ.2⟩)).1
    have hm := mul_le_mul_of_nonneg_right hb (pow_nonneg hp.le 3)
    nlinarith

/-- The next angular Taylor correction has its explicit global fifth-order
bound; no derivative estimate is left as an input. -/
theorem gamma_fifth_defect {θ : ℝ} (hθ : θ∈Set.Icc 0 Real.pi) :
    0≤θ^3/12-(θ-gamma θ) ∧ θ^3/12-(θ-gamma θ)≤θ^5/96 := by
  refine ⟨by have h := (gamma_cubic_defect hθ).2; linarith,?_⟩
  by_cases hz : θ=0
  · simp [hz]
  · have hp : 0<θ := lt_of_le_of_ne hθ.1 (Ne.symm hz)
    have hc : ContDiffOn ℝ 5 gamma (uIcc 0 θ) := (contDiff_gamma.of_le le_top).contDiffOn
    obtain ⟨c,hcθ,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 4) hp.ne hc
    have hc' : c∈Set.Ioo 0 θ := by simpa only [uIoo_of_lt hp] using hcθ
    rw [taylor_four hp,iteratedDeriv_gamma_five] at he
    norm_num only [sub_zero,Nat.factorial] at he
    have hb := (abs_le.mp (gammaD5_abs_le ⟨hc'.1.le,hc'.2.le.trans hθ.2⟩)).2
    have hm := mul_le_mul_of_nonneg_right hb (pow_nonneg hp.le 5)
    nlinarith

end
end SpanningTreeIsoperimetry.AngularKernelTaylor
