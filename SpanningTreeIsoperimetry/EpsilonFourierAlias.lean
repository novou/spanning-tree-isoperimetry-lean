module

public import SpanningTreeIsoperimetry.StripFourierLaplace
public import SpanningTreeIsoperimetry.StripFourierDecay
public import SpanningTreeIsoperimetry.EpsilonBounds
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Actual periodic trapezoidal alias identity. The already checked
log-integral and Fourier--Laplace identity meet through absolutely summable
integrals; the singular endpoint is excluded only on a null set. -/
namespace SpanningTreeIsoperimetry.EpsilonFourierAlias
open SquareMaximality SquareMaximality.Rectangle Concrete
open RectangularRemainder StripFourierCoefficients StripFourierDecay StripFourierLaplace
open MeasureTheory Set
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem epsilon_angular_integral {r : ℕ} (hr : 0<r) :
    epsilon squareLatticeEntropy r= -(1/Real.pi)*
      (∫ θ in (0 : ℝ)..Real.pi,Real.log (1-Real.exp (-2*(r : ℝ)*gamma θ))) := by
  rw [EpsilonBounds.epsilon_eq_neg_integral hr]
  have he : (∫ x in (0 : ℝ)..1,Real.log (1-Real.exp ((-2*kernel x)*r)))=
      (1/Real.pi)*(∫ θ in (0 : ℝ)..Real.pi,Real.log (1-Real.exp (-2*(r : ℝ)*gamma θ))) := by
    calc
      _=(∫ x in (0 : ℝ)..1,Real.log (1-Real.exp (-2*(r : ℝ)*gamma (Real.pi*x)))) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x∈Icc (0 : ℝ) 1 := by simpa using hx
        have ht : Real.pi*x∈Icc 0 Real.pi :=
          ⟨mul_nonneg Real.pi_pos.le hx'.1,by nlinarith [hx'.2,Real.pi_pos]⟩
        dsimp only
        rw [gamma_eq_kernel ht]
        have hh : Real.pi*x/Real.pi=x := by field_simp
        rw [hh]
        congr 3
        ring
      _=_ := by
        rw [intervalIntegral.integral_comp_mul_left (f := fun θ : ℝ =>
          Real.log (1-Real.exp (-2*(r : ℝ)*gamma θ))) Real.pi_ne_zero]
        simp only [mul_zero,mul_one,smul_eq_mul,one_div]
  rw [he]
  ring

def logMode (r n : ℕ) (θ : ℝ) : ℝ :=
  Real.exp (-2*(r : ℝ)*((n : ℝ)+1)*gamma θ)/((n : ℝ)+1)

theorem logMode_nonneg (r n : ℕ) (θ : ℝ) : 0≤logMode r n θ := by unfold logMode; positivity

theorem logMode_continuous (r n : ℕ) : Continuous (logMode r n) :=
  (Real.continuous_exp.comp (contDiff_gamma.continuous.const_mul (-2*(r : ℝ)*((n : ℝ)+1)))).div_const _

theorem integral_logMode {r : ℕ} (hr : 0<r) (n : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi,logMode r n θ)=
      (2*Real.pi*r)*coefficient (2*r*(n+1)) := by
  have hj : 0<2*r*(n+1) := by positivity
  have hc := coefficient_laplace hj
  have he : (fun θ : ℝ => Real.exp (-((2*r*(n+1) : ℕ) : ℝ)*gamma θ))=
      (fun θ => Real.exp (-2*(r : ℝ)*((n : ℝ)+1)*gamma θ)) := by
    funext θ
    congr 1
    push_cast
    ring
  rw [he] at hc
  unfold logMode
  rw [intervalIntegral.integral_div]
  have hn : (n : ℝ)+1≠0 := by positivity
  have hrR : (r : ℝ)≠0 := by exact_mod_cast hr.ne'
  push_cast at hc
  field_simp at hc ⊢
  nlinarith [hc]

theorem sampled_coefficients_summable {r : ℕ} (hr : 0<r) :
    Summable (fun n : ℕ => coefficient (2*r*(n+1))) := by
  have hall : Summable coefficient := (summable_nat_add_iff 1).mp coefficient_summable
  apply hall.comp_injective
  intro a b hab
  have hh : a+1=b+1 := mul_left_cancel₀ (by positivity : (2*r : ℕ)≠0) hab
  omega

theorem logMode_sum {r : ℕ} (hr : 0<r) {θ : ℝ} (hθ : θ∈Ioc 0 Real.pi) :
    (∑' n : ℕ,logMode r n θ)= -Real.log (1-Real.exp (-2*(r : ℝ)*gamma θ)) := by
  have hg : 0<gamma θ := by
    have h := gamma_strictMonoOn ⟨le_rfl,Real.pi_pos.le⟩ ⟨hθ.1.le,hθ.2⟩ hθ.1
    simpa only [gamma_zero] using h
  have hq : |Real.exp (-2*(r : ℝ)*gamma θ)|<1 := by
    rw [abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]
    have hrR : (0 : ℝ)<r := by exact_mod_cast hr
    nlinarith
  have hs := (Real.hasSum_pow_div_log_of_abs_lt_one hq).tsum_eq
  convert hs using 1
  apply tsum_congr
  intro n
  rw [logMode,← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- Sign convention: v_j is the coefficient of minus gamma. Thus this is
exactly epsilon_r = -2r sum gamma_(2ra) in the manuscript. -/
theorem epsilon_fourier_alias {r : ℕ} (hr : 0<r) :
    epsilon squareLatticeEntropy r=(2*(r : ℝ))*(∑' n : ℕ,coefficient (2*r*(n+1))) := by
  let μ := volume.restrict (Ioc (0 : ℝ) Real.pi)
  have hi (n : ℕ) : Integrable (logMode r n) μ :=
    ((logMode_continuous r n).intervalIntegrable (0 : ℝ) Real.pi).1
  have hint (n : ℕ) : (∫ θ,logMode r n θ ∂μ)=(2*Real.pi*r)*coefficient (2*r*(n+1)) := by
    simpa only [μ,← intervalIntegral.integral_of_le Real.pi_pos.le] using integral_logMode hr n
  have hnorm (n : ℕ) : (∫ θ,‖logMode r n θ‖ ∂μ)=(2*Real.pi*r)*coefficient (2*r*(n+1)) := by
    simp only [Real.norm_eq_abs,abs_of_nonneg (logMode_nonneg r n _)]
    exact hint n
  have hs : Summable (fun n : ℕ => ∫ θ,‖logMode r n θ‖ ∂μ) := by
    simpa only [hnorm] using (sampled_coefficients_summable hr).mul_left (2*Real.pi*r)
  have hswap := integral_tsum_of_summable_integral_norm hi hs
  have he : (∫ θ,(∑' n : ℕ,logMode r n θ) ∂μ)=
      ∫ θ,-Real.log (1-Real.exp (-2*(r : ℝ)*gamma θ)) ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    exact logMode_sum hr hθ
  rw [he] at hswap
  simp_rw [hint] at hswap
  rw [tsum_mul_left,integral_neg] at hswap
  change (2*Real.pi*r)*(∑' n : ℕ,coefficient (2*r*(n+1)))=
    -(∫ θ,Real.log (1-Real.exp (-2*(r : ℝ)*gamma θ)) ∂volume.restrict (Ioc 0 Real.pi)) at hswap
  rw [← intervalIntegral.integral_of_le Real.pi_pos.le] at hswap
  rw [epsilon_angular_integral hr]
  calc
    _=(1/Real.pi)*(-(∫ θ in (0 : ℝ)..Real.pi,Real.log (1-Real.exp (-2*(r : ℝ)*gamma θ)))) := by ring
    _=(1/Real.pi)*((2*Real.pi*r)*(∑' n : ℕ,coefficient (2*r*(n+1)))) := by rw [← hswap]
    _=_ := by field_simp

end
end SpanningTreeIsoperimetry.EpsilonFourierAlias
