import SpanningTreeIsoperimetry.StripFourierDecay
import SpanningTreeIsoperimetry.KernelDerivativeVariation

/-! The displayed fourth-order asymptotic bound for the actual critical
Fourier coefficients. Our coefficient is that of minus gamma, so its
leading term is positive. -/
namespace SpanningTreeIsoperimetry.StripFourierFourthOrder
open StripFourierCoefficients StripFourierDecay RectangularRemainder
open LatticeKernelDerivatives KernelDerivativeVariation MeasureTheory Set
noncomputable section

private theorem second_mode_identity {j : ℕ} (hj : 0<j) :
    (∫ θ in (0 : ℝ)..Real.pi,gammaD2 θ*Real.cos ((j : ℝ)*θ))*(j : ℝ)^2=
      1/2-(∫ θ in (0 : ℝ)..Real.pi,gammaD4 θ*Real.cos ((j : ℝ)*θ)) := by
  have h2 : Continuous gammaD2 := continuous_iff_continuousAt.mpr
    (fun θ => (hasDerivAt_gammaD2 θ).continuousAt)
  have h3 : Continuous gammaD3 := continuous_iff_continuousAt.mpr
    (fun θ => (hasDerivAt_gammaD3 θ).continuousAt)
  have h4 : Continuous gammaD4 := continuous_iff_continuousAt.mpr
    (fun θ => (hasDerivAt_gammaD4 θ).continuousAt)
  have hs : Continuous (fun θ : ℝ => Real.sin ((j : ℝ)*θ)) := by fun_prop
  have hc : Continuous (fun θ : ℝ => Real.cos ((j : ℝ)*θ)) := by fun_prop
  have hds (θ : ℝ) : HasDerivAt (fun x : ℝ => Real.sin ((j : ℝ)*x))
      (Real.cos ((j : ℝ)*θ)*(j : ℝ)) θ := by
    simpa using ((hasDerivAt_id θ).const_mul (j : ℝ)).sin
  have hdc (θ : ℝ) : HasDerivAt (fun x : ℝ => Real.cos ((j : ℝ)*x))
      (-Real.sin ((j : ℝ)*θ)*(j : ℝ)) θ := by
    simpa using ((hasDerivAt_id θ).const_mul (j : ℝ)).cos
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := Real.pi) h2.continuousOn hs.continuousOn
    (fun θ _ => hasDerivAt_gammaD2 θ) (fun θ _ => hds θ)
    (h3.intervalIntegrable _ _) ((hc.mul_const _).intervalIntegrable _ _)
  have hj' := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := Real.pi) h3.continuousOn hc.continuousOn
    (fun θ _ => hasDerivAt_gammaD3 θ) (fun θ _ => hdc θ)
    (h4.intervalIntegrable _ _) ((hs.neg.mul_const _).intervalIntegrable _ _)
  have hsin : Real.sin ((j : ℝ)*Real.pi)=0 := Real.sin_nat_mul_pi j
  simp only [hsin,mul_zero,Real.sin_zero,sub_zero,zero_sub] at hi
  simp only [gammaD3_zero,gammaD3_pi,zero_mul,mul_zero,Real.cos_zero,mul_one] at hj'
  have he1 : (∫ θ in (0 : ℝ)..Real.pi,gammaD2 θ*(Real.cos ((j : ℝ)*θ)*(j : ℝ)))=
      (∫ θ in (0 : ℝ)..Real.pi,gammaD2 θ*Real.cos ((j : ℝ)*θ))*(j : ℝ) := by
    simp only [← mul_assoc,intervalIntegral.integral_mul_const]
  have he2 : (∫ θ in (0 : ℝ)..Real.pi,gammaD3 θ*(-Real.sin ((j : ℝ)*θ)*(j : ℝ)))=
      -(∫ θ in (0 : ℝ)..Real.pi,gammaD3 θ*Real.sin ((j : ℝ)*θ))*(j : ℝ) := by
    simp only [← mul_assoc,mul_neg,intervalIntegral.integral_mul_const,intervalIntegral.integral_neg]
  rw [he1] at hi
  rw [he2] at hj'
  nlinarith [hi,hj']

theorem coefficient_four_by_parts {j : ℕ} (hj : 0<j) :
    coefficient j=1/(Real.pi*(j : ℝ)^2)+
      (1/2-(∫ θ in (0 : ℝ)..Real.pi,gammaD4 θ*Real.cos ((j : ℝ)*θ)))/(Real.pi*(j : ℝ)^4) := by
  have hj0 : (j : ℝ)≠0 := by exact_mod_cast hj.ne'
  have he : (∫ θ in (0 : ℝ)..Real.pi,gammaD2 θ*Real.cos ((j : ℝ)*θ))=
      (1/2-(∫ θ in (0 : ℝ)..Real.pi,gammaD4 θ*Real.cos ((j : ℝ)*θ)))/(j : ℝ)^2 :=
    (eq_div_iff (pow_ne_zero 2 hj0)).mpr (second_mode_identity hj)
  rw [coefficient_twice_by_parts hj,he]
  field_simp
  <;> ring

/-- Equivalently, for the cosine coefficient gamma_j of plus gamma,
|gamma_j + 1/(pi*j^2)| is bounded by 2/(pi*j^4). -/
theorem coefficient_fourth_order_bound {j : ℕ} (hj : 0<j) :
    |coefficient j-1/(Real.pi*(j : ℝ)^2)|≤2/(Real.pi*(j : ℝ)^4) := by
  have h4 : Continuous gammaD4 := continuous_iff_continuousAt.mpr
    (fun θ => (hasDerivAt_gammaD4 θ).continuousAt)
  have hp : Continuous (fun θ : ℝ => gammaD4 θ*Real.cos ((j : ℝ)*θ)) := h4.mul (by fun_prop)
  have hb : |∫ θ in (0 : ℝ)..Real.pi,gammaD4 θ*Real.cos ((j : ℝ)*θ)|≤3/2 := by
    apply (intervalIntegral.abs_integral_le_integral_abs Real.pi_pos.le).trans
    apply le_trans _ integral_abs_gammaD4_le
    apply intervalIntegral.integral_mono_on Real.pi_pos.le
      (hp.abs.intervalIntegrable _ _) (h4.abs.intervalIntegrable _ _)
    intro θ _
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hn : |1/2-(∫ θ in (0 : ℝ)..Real.pi,gammaD4 θ*Real.cos ((j : ℝ)*θ))|≤2 := by
    have h := abs_sub_le (1/2 : ℝ) 0 (∫ θ in (0 : ℝ)..Real.pi,gammaD4 θ*Real.cos ((j : ℝ)*θ))
    norm_num only [sub_zero,zero_sub,abs_neg,abs_of_pos (by norm_num : (0 : ℝ)<1/2)] at h
    linarith
  rw [coefficient_four_by_parts hj,add_sub_cancel_left,abs_div,
    abs_of_pos (by positivity : 0<Real.pi*(j : ℝ)^4)]
  exact div_le_div_of_nonneg_right hn (by positivity)

end
end SpanningTreeIsoperimetry.StripFourierFourthOrder
