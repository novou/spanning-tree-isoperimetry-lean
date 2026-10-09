import SpanningTreeIsoperimetry.RegularizedSymbolVariation
import SpanningTreeIsoperimetry.StripFourierDecay

/-! Uniform inverse-square decay of the actual regularized strip-symbol
coefficients, including the critical parameter. -/
namespace SpanningTreeIsoperimetry.RegularizedFourierDecay
open RegularizedStripSymbol RegularizedSymbolVariation Set MeasureTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem coefficient_by_parts {z : ℝ} (hz : 4<z) {j : ℕ} (hj : 0<j) :
    coefficientZ z j=(1/(Real.pi*(j : ℝ)))*
      (∫ θ in (0 : ℝ)..Real.pi,first z θ*Real.sin ((j : ℝ)*θ)) := by
  have hj0 : (j : ℝ)≠0 := by exact_mod_cast hj.ne'
  have hg := (contDiff_gammaZ hz).continuous
  have hs : Continuous (fun θ : ℝ => Real.sin ((j : ℝ)*θ)) := by fun_prop
  have hc : Continuous (fun θ : ℝ => Real.cos ((j : ℝ)*θ)*(j : ℝ)) := by fun_prop
  have hd (θ : ℝ) : HasDerivAt (fun x : ℝ => Real.sin ((j : ℝ)*x))
      (Real.cos ((j : ℝ)*θ)*(j : ℝ)) θ := by
    simpa using ((hasDerivAt_id θ).const_mul (j : ℝ)).sin
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := Real.pi) hg.continuousOn hs.continuousOn
    (fun θ _ => hasDerivAt_gamma hz θ) (fun θ _ => hd θ)
    ((continuous_first hz).intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  have hsin : Real.sin ((j : ℝ)*Real.pi)=0 := Real.sin_nat_mul_pi j
  simp only [hsin,mul_zero,Real.sin_zero,sub_zero,zero_sub] at hi
  have hp : (∫ θ in (0 : ℝ)..Real.pi,gammaZ z θ*(Real.cos ((j : ℝ)*θ)*(j : ℝ)))=
      (∫ θ in (0 : ℝ)..Real.pi,gammaZ z θ*Real.cos ((j : ℝ)*θ))*(j : ℝ) := by
    simp only [← mul_assoc,intervalIntegral.integral_mul_const]
  rw [hp] at hi
  have hn : (∫ θ in (0 : ℝ)..Real.pi,-gammaZ z θ*Real.cos ((j : ℝ)*θ))=
      -(∫ θ in (0 : ℝ)..Real.pi,gammaZ z θ*Real.cos ((j : ℝ)*θ)) := by
    simp only [neg_mul,intervalIntegral.integral_neg]
  rw [coefficientZ,hn]
  field_simp
  nlinarith only [hi]

theorem coefficient_twice_by_parts {z : ℝ} (hz : 4<z) {j : ℕ} (hj : 0<j) :
    coefficientZ z j=(∫ θ in (0 : ℝ)..Real.pi,second z θ*Real.cos ((j : ℝ)*θ))/
      (Real.pi*(j : ℝ)^2) := by
  have hj0 : (j : ℝ)≠0 := by exact_mod_cast hj.ne'
  have hc : Continuous (fun θ : ℝ => Real.cos ((j : ℝ)*θ)) := by fun_prop
  have hs : Continuous (fun θ : ℝ => -Real.sin ((j : ℝ)*θ)*(j : ℝ)) := by fun_prop
  have hd (θ : ℝ) : HasDerivAt (fun x : ℝ => Real.cos ((j : ℝ)*x))
      (-Real.sin ((j : ℝ)*θ)*(j : ℝ)) θ := by
    simpa using ((hasDerivAt_id θ).const_mul (j : ℝ)).cos
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := Real.pi) (continuous_first hz).continuousOn hc.continuousOn
    (fun θ _ => hasDerivAt_first hz θ) (fun θ _ => hd θ)
    ((continuous_second hz).intervalIntegrable _ _) (hs.intervalIntegrable _ _)
  simp only [first_zero,first_pi,mul_zero,zero_mul,sub_zero,zero_sub] at hi
  have he : (∫ θ in (0 : ℝ)..Real.pi,first z θ*(-Real.sin ((j : ℝ)*θ)*(j : ℝ)))=
      -(∫ θ in (0 : ℝ)..Real.pi,first z θ*Real.sin ((j : ℝ)*θ))*(j : ℝ) := by
    simp only [← mul_assoc,mul_neg,intervalIntegral.integral_mul_const,intervalIntegral.integral_neg]
  rw [he] at hi
  rw [coefficient_by_parts hz hj]
  field_simp
  nlinarith only [hi]

theorem coefficient_bound_strict {z : ℝ} (hz : 4<z) {j : ℕ} (hj : 0<j) :
    |coefficientZ z j|≤2/(Real.pi*(j : ℝ)^2) := by
  have hg := continuous_second hz
  have hp : Continuous (fun θ : ℝ => second z θ*Real.cos ((j : ℝ)*θ)) := hg.mul (by fun_prop)
  have hq : |∫ θ in (0 : ℝ)..Real.pi,second z θ*Real.cos ((j : ℝ)*θ)|≤2 := by
    apply (intervalIntegral.abs_integral_le_integral_abs Real.pi_pos.le).trans
    apply le_trans _ (integral_abs_second_le hz)
    apply intervalIntegral.integral_mono_on Real.pi_pos.le
      (hp.abs.intervalIntegrable _ _) (hg.abs.intervalIntegrable _ _)
    intro θ _
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  rw [coefficient_twice_by_parts hz hj,abs_div,abs_of_pos (by positivity : 0<Real.pi*(j : ℝ)^2)]
  exact div_le_div_of_nonneg_right hq (by positivity)

/-- Actual uniform coefficient estimate, with no variation or regularity
hypothesis supplied by the caller. -/
theorem coefficient_bound {z : ℝ} (hz : 4≤z) {j : ℕ} (hj : 0<j) :
    |coefficientZ z j|≤2/(Real.pi*(j : ℝ)^2) := by
  rcases eq_or_lt_of_le hz with h|h
  · rw [← h,coefficientZ_four,abs_of_nonneg (StripFourierDecay.coefficient_bound hj).1]
    exact (StripFourierDecay.coefficient_bound hj).2
  · exact coefficient_bound_strict h hj

end
end SpanningTreeIsoperimetry.RegularizedFourierDecay
