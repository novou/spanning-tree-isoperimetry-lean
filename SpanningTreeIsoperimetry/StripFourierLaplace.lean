import SpanningTreeIsoperimetry.RegularizedLogPotential
import SpanningTreeIsoperimetry.LogCosineFourier
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Fourier--Laplace identity for the actual angular kernel. Above four,
continuous symmetric log-potential integrals may be interchanged. A compact
parameter-integral limit then reaches the critical endpoint. -/
namespace SpanningTreeIsoperimetry.StripFourierLaplace
open RegularizedStripSymbol RegularizedLogPotential RectangularRemainder
open StripFourierCoefficients MeasureTheory Set Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def laplaceIntegral (z : ℝ) (j : ℕ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi,Real.exp (-(j : ℝ)*gammaZ z θ)

private theorem integral_cos_nat {j : ℕ} (hj : 0<j) :
    (∫ θ in (0 : ℝ)..Real.pi,Real.cos ((j : ℝ)*θ))=0 := by
  have hj0 : (j : ℝ)≠0 := by exact_mod_cast hj.ne'
  rw [intervalIntegral.integral_comp_mul_left (f := Real.cos) hj0,integral_cos]
  simp [Real.sin_nat_mul_pi]

private theorem potential_as_logCosine {z : ℝ} (hz : 4<z) (θ φ : ℝ) :
    potential z θ φ=gammaZ z φ+
      Real.log (1-2*Real.exp (-gammaZ z φ)*Real.cos θ+Real.exp (-gammaZ z φ)^2) := by
  let g := gammaZ z φ
  let q := Real.exp (-g)
  have hq0 : 0<q := Real.exp_pos _
  have hq : q<1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (gammaZ_pos hz φ))
  have heq : Real.exp g*q=1 := by dsimp only [q]; rw [← Real.exp_add]; simp
  have hsum : Real.exp g+q=z-2*Real.cos φ := by
    have h := cosh_gamma hz φ
    rw [Real.cosh_eq] at h
    change (Real.exp g+q)/2=z/2-Real.cos φ at h
    linarith
  have harg : z-2*Real.cos θ-2*Real.cos φ=
      Real.exp g*(1-2*q*Real.cos θ+q^2) := by
    calc
      _=Real.exp g-2*Real.cos θ+q := by linarith [hsum]
      _=Real.exp g-2*(Real.exp g*q)*Real.cos θ+(Real.exp g*q)*q := by rw [heq]; ring
      _=_ := by ring
  have hp : 0<1-2*q*Real.cos θ+q^2 := LogCosineFourier.argument_pos hq0.le hq θ
  change Real.log (z-2*Real.cos θ-2*Real.cos φ)=g+Real.log (1-2*q*Real.cos θ+q^2)
  rw [harg,Real.log_mul (Real.exp_ne_zero _) hp.ne',Real.log_exp]

private theorem potential_cosine {z : ℝ} (hz : 4<z) {j : ℕ} (hj : 0<j) (φ : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi,potential z θ φ*Real.cos ((j : ℝ)*θ))=
      -(Real.pi/(j : ℝ))*Real.exp (-(j : ℝ)*gammaZ z φ) := by
  let q := Real.exp (-gammaZ z φ)
  have hq0 : 0<q := Real.exp_pos _
  have hq : q<1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (gammaZ_pos hz φ))
  have hc : Continuous (fun θ : ℝ => Real.log (1-2*q*Real.cos θ+q^2)) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    have hi : ContinuousAt (fun x : ℝ => 1-2*q*Real.cos x+q^2) θ := by fun_prop
    exact (Real.continuousAt_log (LogCosineFourier.argument_pos hq0.le hq θ).ne').comp_of_eq hi rfl
  have hcos : Continuous (fun θ : ℝ => Real.cos ((j : ℝ)*θ)) := by fun_prop
  have hf := LogCosineFourier.cosine_coefficient hq0.le hq hj
  have hpow : q^j=Real.exp (-(j : ℝ)*gammaZ z φ) := by
    dsimp only [q]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [potential_as_logCosine hz,add_mul]
  change (∫ θ in (0 : ℝ)..Real.pi,
    gammaZ z φ*Real.cos ((j : ℝ)*θ)+Real.log (1-2*q*Real.cos θ+q^2)*Real.cos ((j : ℝ)*θ))=_
  have hi1 : IntervalIntegrable (fun θ : ℝ => gammaZ z φ*Real.cos ((j : ℝ)*θ)) volume 0 Real.pi :=
    (hcos.const_mul (gammaZ z φ)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun θ : ℝ => Real.log (1-2*q*Real.cos θ+q^2)*Real.cos ((j : ℝ)*θ))
      volume 0 Real.pi := (hc.mul hcos).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1 hi2,intervalIntegral.integral_const_mul,
    integral_cos_nat hj,mul_zero,zero_add]
  rw [hpow] at hf
  have hpi := Real.pi_ne_zero
  have hj0 : (j : ℝ)≠0 := by exact_mod_cast hj.ne'
  field_simp at hf ⊢
  nlinarith [hf]

/-- Regularized identity, with every Fourier and potential integral actual. -/
theorem regularized_laplace {z : ℝ} (hz : 4<z) {j : ℕ} (hj : 0<j) :
    coefficientZ z j=(1/(Real.pi*(j : ℝ)))*laplaceIntegral z j := by
  have hdouble : (∫ θ in (0 : ℝ)..Real.pi,∫ φ in (0 : ℝ)..Real.pi,
      potential z θ φ*Real.cos ((j : ℝ)*θ))=
      Real.pi*(∫ θ in (0 : ℝ)..Real.pi,gammaZ z θ*Real.cos ((j : ℝ)*θ)) := by
    simp_rw [intervalIntegral.integral_mul_const,potential_integral hz]
    simp only [mul_assoc,intervalIntegral.integral_const_mul]
  have he := potential_cosine_swap hz j
  simp_rw [potential_cosine hz hj] at he
  rw [intervalIntegral.integral_const_mul] at he
  change _= -(Real.pi/(j : ℝ))*laplaceIntegral z j at he
  rw [hdouble] at he
  have hcoeff : coefficientZ z j= -(1/Real.pi)*
      (∫ θ in (0 : ℝ)..Real.pi,gammaZ z θ*Real.cos ((j : ℝ)*θ)) := by
    simp only [coefficientZ,neg_mul,intervalIntegral.integral_neg]
    ring
  rw [hcoeff]
  have hj0 : (j : ℝ)≠0 := by exact_mod_cast hj.ne'
  field_simp at he ⊢
  nlinarith [he]

theorem continuous_clipped_laplace (j : ℕ) : Continuous (fun z => laplaceIntegral (max 4 z) j) := by
  have hi : Continuous (fun p : ℝ×ℝ => Real.exp (-(j : ℝ)*gammaZ (max 4 p.1) p.2)) :=
    Real.continuous_exp.comp (continuous_clipped_gamma.const_mul (-(j : ℝ)))
  have hc := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun z θ : ℝ => Real.exp (-(j : ℝ)*gammaZ (max 4 z) θ))
    hi (isCompact_Icc : IsCompact (Icc (0 : ℝ) Real.pi))
  simpa only [laplaceIntegral,intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_Icc_eq_integral_Ioc] using hc

/-- Appendix A's coefficient formula. Its gamma_j is minus our coefficient. -/
theorem coefficient_laplace {j : ℕ} (hj : 0<j) :
    coefficient j=(1/(Real.pi*(j : ℝ)))*
      (∫ θ in (0 : ℝ)..Real.pi,Real.exp (-(j : ℝ)*gamma θ)) := by
  let z : ℕ → ℝ := fun n => 4+1/((n : ℝ)+1)
  have hz (n : ℕ) : 4<z n := by
    have hp : (0 : ℝ)<1/((n : ℝ)+1) := by positivity
    dsimp only [z]
    linarith
  have ht : Tendsto z atTop (𝓝 4) := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop := by
      simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
    have h : Tendsto (fun n : ℕ => (1 : ℝ)/((n : ℝ)+1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hn
    convert tendsto_const_nhds.add h using 1 <;> norm_num [z]
  have hm (n : ℕ) : max 4 (z n)=z n := max_eq_right (hz n).le
  have hc := (continuous_clipped_coefficient j).continuousAt.tendsto.comp ht
  have hl := (continuous_clipped_laplace j).continuousAt.tendsto.comp ht
  simp only [Function.comp_def,hm,max_self,coefficientZ_four] at hc hl
  have he : (fun n => coefficientZ (z n) j)=(fun n => (1/(Real.pi*(j : ℝ)))*laplaceIntegral (z n) j) :=
    funext (fun n => regularized_laplace (hz n) hj)
  rw [he] at hc
  have hu := tendsto_nhds_unique hc (hl.const_mul (1/(Real.pi*(j : ℝ))))
  rw [hu]
  congr 1
  unfold laplaceIntegral
  apply intervalIntegral.integral_congr
  intro θ hθ
  dsimp only
  rw [gammaZ_four (by simpa only [uIcc_of_le Real.pi_pos.le] using hθ)]

end
end SpanningTreeIsoperimetry.StripFourierLaplace
