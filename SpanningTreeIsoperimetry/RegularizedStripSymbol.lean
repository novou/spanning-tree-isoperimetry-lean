module

public import SpanningTreeIsoperimetry.StripFourierCoefficients
public import Mathlib.Analysis.SpecialFunctions.Arcosh

@[expose] public section

/-! The actual regularized even strip symbol. Smoothness is asserted only
for z>4; its critical coefficient agrees with the checked angular kernel. -/
namespace SpanningTreeIsoperimetry.RegularizedStripSymbol
open RectangularRemainder Set MeasureTheory
noncomputable section

def gammaZ (z θ : ℝ) : ℝ := Real.arcosh (z/2-Real.cos θ)
def symbol (z θ : ℝ) : ℝ := Real.exp (-gammaZ z θ)
def coefficientZ (z : ℝ) (j : ℕ) : ℝ :=
  (1/Real.pi)*(∫ θ in (0 : ℝ)..Real.pi, -gammaZ z θ*Real.cos ((j : ℝ)*θ))

theorem gammaZ_nonneg {z : ℝ} (hz : 4≤z) (θ : ℝ) : 0≤gammaZ z θ := by
  apply Real.arcosh_nonneg
  linarith [Real.cos_le_one θ]

theorem gammaZ_pos {z : ℝ} (hz : 4<z) (θ : ℝ) : 0<gammaZ z θ := by
  apply Real.arcosh_pos
  linarith [Real.cos_le_one θ]

theorem gammaZ_even (z : ℝ) : Function.Even (gammaZ z) := by
  intro θ
  simp [gammaZ]

theorem gammaZ_periodic (z : ℝ) : Function.Periodic (gammaZ z) (2*Real.pi) := by
  intro θ
  simp [gammaZ,Real.cos_add_two_pi]

theorem symbol_bounds {z : ℝ} (hz : 4<z) (θ : ℝ) : 0<symbol z θ ∧ symbol z θ<1 := by
  refine ⟨Real.exp_pos _,?_⟩
  apply Real.exp_lt_one_iff.mpr
  linarith [gammaZ_pos hz θ]

theorem contDiff_gammaZ {z : ℝ} (hz : 4<z) : ContDiff ℝ ⊤ (gammaZ z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  have hi : ContDiff ℝ ⊤ (fun θ : ℝ => z/2-Real.cos θ) := by fun_prop
  exact (Real.contDiffAt_arcosh (show z/2-Real.cos θ∈Ioi 1 by
    change 1<z/2-Real.cos θ
    linarith [Real.cos_le_one θ])).comp θ hi.contDiffAt

theorem hasDerivAt_gammaZ {z : ℝ} (hz : 4<z) (θ : ℝ) :
    HasDerivAt (gammaZ z) (Real.sin θ/Real.sqrt ((z/2-Real.cos θ)^2-1)) θ := by
  have hi := (hasDerivAt_const θ (z/2)).sub (Real.hasDerivAt_cos θ)
  have h := (Real.hasDerivAt_arcosh (show z/2-Real.cos θ∈Ioi 1 by
    change 1<z/2-Real.cos θ
    linarith [Real.cos_le_one θ])).comp θ hi
  change HasDerivAt (fun x => Real.arcosh (z/2-Real.cos x)) _ θ
  simpa only [Function.comp_def,Pi.sub_apply,zero_sub,neg_neg,div_eq_mul_inv,mul_comm] using h

theorem deriv_gammaZ_zero {z : ℝ} (hz : 4<z) : deriv (gammaZ z) 0=0 := by
  rw [(hasDerivAt_gammaZ hz 0).deriv]
  simp

theorem deriv_gammaZ_pi {z : ℝ} (hz : 4<z) : deriv (gammaZ z) Real.pi=0 := by
  rw [(hasDerivAt_gammaZ hz Real.pi).deriv]
  simp

theorem gammaZ_four {θ : ℝ} (hθ : θ∈Icc 0 Real.pi) : gammaZ 4 θ=gamma θ := by
  rw [gamma_eq_kernel hθ]
  unfold gammaZ SquareMaximality.Rectangle.Concrete.kernel
  have he : Real.pi*(θ/Real.pi)=θ := by field_simp
  rw [he]
  norm_num

theorem coefficientZ_four (j : ℕ) : coefficientZ 4 j=StripFourierCoefficients.coefficient j := by
  unfold coefficientZ StripFourierCoefficients.coefficient
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  have ht : θ∈Icc 0 Real.pi := by simpa only [uIcc_of_le Real.pi_pos.le] using hθ
  dsimp only
  rw [gammaZ_four ht]

theorem gammaZ_upper {z : ℝ} (hz : 4≤z) (hz5 : z≤5) (θ : ℝ) :
    gammaZ z θ≤Real.arcosh (7/2) := by
  unfold gammaZ
  apply (Real.arcosh_le_arcosh
    (by linarith [Real.cos_le_one θ] : 0<z/2-Real.cos θ)
    (by norm_num : (0 : ℝ)<7/2)).mpr
  linarith [Real.neg_one_le_cos θ]


/-- A continuous extension across the critical parameter, obtained by keeping
its value fixed below four. -/
theorem continuous_clipped_gamma :
    Continuous (fun p : ℝ×ℝ => gammaZ (max 4 p.1) p.2) := by
  have hi : Continuous (fun p : ℝ×ℝ => max 4 p.1/2-Real.cos p.2) := by fun_prop
  exact Real.continuousOn_arcosh.comp_continuous hi (fun p => by
    change 1≤max 4 p.1/2-Real.cos p.2
    linarith [le_max_left (4 : ℝ) p.1,Real.cos_le_one p.2])

theorem continuous_clipped_coefficient (j : ℕ) :
    Continuous (fun z : ℝ => coefficientZ (max 4 z) j) := by
  have hi : Continuous (fun p : ℝ×ℝ =>
      -gammaZ (max 4 p.1) p.2*Real.cos ((j : ℝ)*p.2)) :=
    continuous_clipped_gamma.neg.mul (by fun_prop)
  have hc := continuous_parametric_integral_of_continuous
    (μ := volume)
    (f := fun z θ : ℝ => -gammaZ (max 4 z) θ*Real.cos ((j : ℝ)*θ))
    hi (isCompact_Icc : IsCompact (Icc (0 : ℝ) Real.pi))
  simpa only [coefficientZ,intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_Icc_eq_integral_Ioc] using hc.const_mul (1/Real.pi)

theorem coefficient_continuousOn (j : ℕ) : ContinuousOn (fun z => coefficientZ z j) (Ici 4) := by
  apply (continuous_clipped_coefficient j).continuousOn.congr
  intro z hz
  dsimp only
  rw [max_eq_right hz]

theorem coefficient_critical_limit (j : ℕ) :
    Filter.Tendsto (fun z => coefficientZ z j) (nhdsWithin 4 (Ici 4))
      (nhds (StripFourierCoefficients.coefficient j)) := by
  rw [← coefficientZ_four j]
  exact coefficient_continuousOn j 4 (by simp)

end
end SpanningTreeIsoperimetry.RegularizedStripSymbol
