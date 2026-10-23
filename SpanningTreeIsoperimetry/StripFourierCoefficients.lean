module

public import SpanningTreeIsoperimetry.TrapezoidalKernelError
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

/-! Actual cosine coefficients of the logarithmic half-plane symbol.
These definitions use the angular lattice kernel itself; no determinant
limit or Fourier identity is assumed. -/
namespace SpanningTreeIsoperimetry.StripFourierCoefficients
open SquareMaximality RectangularRemainder TrapezoidalKernelError
open MeasureTheory Set
noncomputable section

def coefficient (j : ℕ) : ℝ :=
  (1/Real.pi)*(∫ θ in (0 : ℝ)..Real.pi, -gamma θ*Real.cos ((j : ℝ)*θ))

theorem coefficient_zero : coefficient 0= -squareLatticeEntropy := by
  rw [coefficient]
  simp only [Nat.cast_zero,zero_mul,Real.cos_zero,mul_one,intervalIntegral.integral_neg]
  rw [integral_gamma]
  field_simp
  <;> ring

theorem coefficient_by_parts {j : ℕ} (hj : 0<j) :
    coefficient j=(1/(Real.pi*(j : ℝ)))*
      (∫ θ in (0 : ℝ)..Real.pi, gammaDeriv θ*Real.sin ((j : ℝ)*θ)) := by
  have hj0 : (j : ℝ)≠0 := by exact_mod_cast hj.ne'
  have hg : Continuous gamma := contDiff_gamma.continuous
  have hs : Continuous (fun θ : ℝ => Real.sin ((j : ℝ)*θ)) := by fun_prop
  have hc : Continuous (fun θ : ℝ => Real.cos ((j : ℝ)*θ)*(j : ℝ)) := by fun_prop
  have hd (θ : ℝ) : HasDerivAt (fun x : ℝ => Real.sin ((j : ℝ)*x))
      (Real.cos ((j : ℝ)*θ)*(j : ℝ)) θ := by
    simpa using ((hasDerivAt_id θ).const_mul (j : ℝ)).sin
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := Real.pi) hg.continuousOn hs.continuousOn
    (fun θ _ => hasDerivAt_gamma θ) (fun θ _ => hd θ)
    (continuous_gammaDeriv.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  have hsin : Real.sin ((j : ℝ)*Real.pi)=0 := Real.sin_nat_mul_pi j
  simp only [hsin,mul_zero,Real.sin_zero,sub_zero,zero_sub] at hi
  have hp : (∫ θ in (0 : ℝ)..Real.pi, gamma θ*(Real.cos ((j : ℝ)*θ)*(j : ℝ)))=
      (∫ θ in (0 : ℝ)..Real.pi, gamma θ*Real.cos ((j : ℝ)*θ))*(j : ℝ) := by
    simp only [← mul_assoc,intervalIntegral.integral_mul_const]
  rw [hp] at hi
  have hn : (∫ θ in (0 : ℝ)..Real.pi, -gamma θ*Real.cos ((j : ℝ)*θ))=
      -(∫ θ in (0 : ℝ)..Real.pi, gamma θ*Real.cos ((j : ℝ)*θ)) := by
    simp only [neg_mul,intervalIntegral.integral_neg]
  rw [coefficient,hn]
  field_simp
  nlinarith [hi]

end
end SpanningTreeIsoperimetry.StripFourierCoefficients
