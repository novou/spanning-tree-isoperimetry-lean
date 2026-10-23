module

public import SpanningTreeIsoperimetry.PowerSeriesCircleExponential
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Fourier coefficients of the actual circle evaluation, including the
vanishing negative frequencies. Termwise integration is justified by the
absolute coefficient majorant on Haar probability measure. -/
namespace SpanningTreeIsoperimetry.PowerSeriesCircle
open PowerSeries WeightedPowerSeries MeasureTheory AddCircle
open scoped BigOperators
noncomputable section

local instance : Fact (0<(2*Real.pi : ℝ)) := ⟨by positivity⟩

theorem fourierCoeff_value_series {p : PowerSeries ℝ} (hp : SummableWeighted p) (m : ℤ) :
    fourierCoeff (value p) m=∑' n,fourierCoeff (mode p n) m := by
  let F : ℕ → CircleDomain → ℂ := fun n x => fourier (-m) x*mode p n x
  have hc (n : ℕ) : Continuous (F n) :=
    (fourier (-m)).continuous.mul (continuous_const.mul (fourier (n : ℤ)).continuous)
  have hi (n : ℕ) : Integrable (F n) haarAddCircle :=
    (hc n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hn (n : ℕ) (x : CircleDomain) : ‖F n x‖=|PowerSeries.coeff n p| := by
    dsimp only [F]
    rw [norm_mul,norm_mode]
    have hf : ‖fourier (-m) x‖=1 := Circle.norm_coe _
    rw [hf,one_mul]
  have hni (n : ℕ) : (∫ x,‖F n x‖ ∂haarAddCircle)=|PowerSeries.coeff n p| := by
    simp only [hn]
    simp
  have hs : Summable (fun n => ∫ x,‖F n x‖ ∂haarAddCircle) := by
    simpa only [hni] using coefficients_summable hp
  have he := integral_tsum_of_summable_integral_norm hi hs
  unfold fourierCoeff value
  simp only [smul_eq_mul]
  simp_rw [← tsum_mul_left]
  exact he.symm

theorem fourierCoeff_mode (p : PowerSeries ℝ) (n : ℕ) (m : ℤ) :
    fourierCoeff (mode p n) m=((PowerSeries.coeff n p : ℝ) : ℂ)*((Pi.single (n : ℤ) (1 : ℂ) : ℤ → ℂ) m) := by
  change fourierCoeff (fun x : CircleDomain => ((PowerSeries.coeff n p : ℝ) : ℂ)*fourier (n : ℤ) x) m=_
  rw [fourierCoeff.const_mul,fourierCoeff_fourier]

/-- The nonnegative Fourier frequencies are exactly the original formal
coefficients. -/
theorem fourierCoeff_value_nat {p : PowerSeries ℝ} (hp : SummableWeighted p) (k : ℕ) :
    fourierCoeff (value p) (k : ℤ)=((PowerSeries.coeff k p : ℝ) : ℂ) := by
  rw [fourierCoeff_value_series hp]
  have he (n : ℕ) : fourierCoeff (mode p n) (k : ℤ)=
      if n=k then ((PowerSeries.coeff k p : ℝ) : ℂ) else 0 := by
    rw [fourierCoeff_mode]
    by_cases hn : n=k
    · subst n
      simp
    · have hnk : (n : ℤ)≠(k : ℤ) := by exact_mod_cast hn
      simp [hn,hnk,Ne.symm hnk]
  simp_rw [he]
  simp

/-- Strictly negative Fourier frequencies vanish. -/
theorem fourierCoeff_value_neg {p : PowerSeries ℝ} (hp : SummableWeighted p) (k : ℕ) :
    fourierCoeff (value p) (-((k+1 : ℕ) : ℤ))=0 := by
  rw [fourierCoeff_value_series hp]
  have hn (n : ℕ) : fourierCoeff (mode p n) (-((k+1 : ℕ) : ℤ))=0 := by
    rw [fourierCoeff_mode]
    have hnk : (n : ℤ)≠-((k+1 : ℕ) : ℤ) := by omega
    rw [Pi.single_eq_of_ne (Ne.symm hnk),mul_zero]
  simp_rw [hn]
  exact tsum_zero

end
end SpanningTreeIsoperimetry.PowerSeriesCircle
