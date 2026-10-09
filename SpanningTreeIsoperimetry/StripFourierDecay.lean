import SpanningTreeIsoperimetry.StripFourierCoefficients
import SpanningTreeIsoperimetry.LatticeKernelDerivatives
import Mathlib.Analysis.PSeries

/-! Absolute decay of the actual critical strip-symbol coefficients. -/
namespace SpanningTreeIsoperimetry.StripFourierDecay
open StripFourierCoefficients RectangularRemainder LatticeKernelDerivatives
open Set MeasureTheory
noncomputable section

theorem gammaD2_nonpos {θ : ℝ} (hθ : θ∈Icc 0 Real.pi) : gammaD2 θ≤0 := by
  have hs : 0≤halfSin θ := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2,Real.pi_pos])
  unfold gammaD2 evenForm P2
  norm_num only [Polynomial.eval_neg,Polynomial.eval_one]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (pow_nonneg (kernelRoot_pos θ).le _)

theorem integral_abs_gammaD2 : (∫ θ in (0 : ℝ)..Real.pi, |gammaD2 θ|)=1 := by
  have hc : Continuous gammaD2 := continuous_iff_continuousAt.mpr
    (fun θ => (hasDerivAt_gammaD2 θ).continuousAt)
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := Real.pi) (fun θ _ => hasDerivAt_gammaDeriv θ) (hc.intervalIntegrable _ _)
  have he : (∫ θ in (0 : ℝ)..Real.pi, |gammaD2 θ|)=
      -(∫ θ in (0 : ℝ)..Real.pi, gammaD2 θ) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro θ hθ
    exact abs_of_nonpos (gammaD2_nonpos (by simpa only [uIcc_of_le Real.pi_pos.le] using hθ))
  rw [he,ht]
  norm_num [gammaDeriv]

theorem coefficient_twice_by_parts {j : ℕ} (hj : 0<j) :
    coefficient j=(1+(∫ θ in (0 : ℝ)..Real.pi, gammaD2 θ*Real.cos ((j : ℝ)*θ)))/
      (Real.pi*(j : ℝ)^2) := by
  have hj0 : (j : ℝ)≠0 := by exact_mod_cast hj.ne'
  have hc2 : Continuous gammaD2 := continuous_iff_continuousAt.mpr
    (fun θ => (hasDerivAt_gammaD2 θ).continuousAt)
  have hc : Continuous (fun θ : ℝ => Real.cos ((j : ℝ)*θ)) := by fun_prop
  have hs : Continuous (fun θ : ℝ => -Real.sin ((j : ℝ)*θ)*(j : ℝ)) := by fun_prop
  have hd (θ : ℝ) : HasDerivAt (fun x : ℝ => Real.cos ((j : ℝ)*x))
      (-Real.sin ((j : ℝ)*θ)*(j : ℝ)) θ := by
    simpa using ((hasDerivAt_id θ).const_mul (j : ℝ)).cos
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := Real.pi) continuous_gammaDeriv.continuousOn hc.continuousOn
    (fun θ _ => hasDerivAt_gammaDeriv θ) (fun θ _ => hd θ)
    (hc2.intervalIntegrable _ _) (hs.intervalIntegrable _ _)
  have hg0 : gammaDeriv 0=1 := by norm_num [gammaDeriv]
  have hgp : gammaDeriv Real.pi=0 := by norm_num [gammaDeriv]
  simp only [hg0,hgp,mul_zero,zero_mul,Real.cos_zero,mul_one,zero_sub] at hi
  have he : (∫ θ in (0 : ℝ)..Real.pi, gammaDeriv θ*(-Real.sin ((j : ℝ)*θ)*(j : ℝ)))=
      -(∫ θ in (0 : ℝ)..Real.pi, gammaDeriv θ*Real.sin ((j : ℝ)*θ))*(j : ℝ) := by
    simp only [← mul_assoc,mul_neg,intervalIntegral.integral_mul_const,intervalIntegral.integral_neg]
  rw [he] at hi
  rw [coefficient_by_parts hj]
  field_simp
  nlinarith only [hi]

theorem coefficient_bound {j : ℕ} (hj : 0<j) :
    0≤coefficient j ∧ coefficient j≤2/(Real.pi*(j : ℝ)^2) := by
  have hc2 : Continuous gammaD2 := continuous_iff_continuousAt.mpr
    (fun θ => (hasDerivAt_gammaD2 θ).continuousAt)
  have hprod : Continuous (fun θ : ℝ => gammaD2 θ*Real.cos ((j : ℝ)*θ)) := hc2.mul (by fun_prop)
  have hq : |∫ θ in (0 : ℝ)..Real.pi, gammaD2 θ*Real.cos ((j : ℝ)*θ)|≤1 := by
    apply (intervalIntegral.abs_integral_le_integral_abs Real.pi_pos.le).trans
    rw [← integral_abs_gammaD2]
    apply intervalIntegral.integral_mono_on Real.pi_pos.le (hprod.abs.intervalIntegrable _ _) (hc2.abs.intervalIntegrable _ _)
    intro θ _
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  rw [coefficient_twice_by_parts hj]
  have hd : 0<Real.pi*(j : ℝ)^2 := by positivity
  constructor
  · exact div_nonneg (by linarith [(abs_le.mp hq).1]) hd.le
  · exact div_le_div_of_nonneg_right (by linarith [(abs_le.mp hq).2]) hd.le


theorem coefficient_summable : Summable (fun n : ℕ => coefficient (n+1)) := by
  have hs := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by decide : 1<2))
  have hmajor : Summable (fun n : ℕ => 2/(Real.pi*((n+1 : ℕ) : ℝ)^2)) := by
    convert hs.mul_left (2/Real.pi) using 1
    funext n
    ring
  exact Summable.of_nonneg_of_le (fun n => (coefficient_bound (by omega : 0<n+1)).1)
    (fun n => (coefficient_bound (by omega : 0<n+1)).2) hmajor

theorem weighted_square_summable :
    Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ)*coefficient (n+1)^2) := by
  have hs := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by decide : 1<3))
  have hmajor : Summable (fun n : ℕ => 4/(Real.pi^2*((n+1 : ℕ) : ℝ)^3)) := by
    convert hs.mul_left (4/Real.pi^2) using 1
    funext n
    ring
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hmajor
  intro n
  have hn : (0 : ℝ)<(n+1 : ℕ) := by positivity
  have hc := coefficient_bound (by omega : 0<n+1)
  calc
    ((n+1 : ℕ) : ℝ)*coefficient (n+1)^2≤
        ((n+1 : ℕ) : ℝ)*(2/(Real.pi*((n+1 : ℕ) : ℝ)^2))^2 := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc.1 hc.2 2) hn.le
    _=4/(Real.pi^2*((n+1 : ℕ) : ℝ)^3) := by
      field_simp
      <;> ring

end
end SpanningTreeIsoperimetry.StripFourierDecay
