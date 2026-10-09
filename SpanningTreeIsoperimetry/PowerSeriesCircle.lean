import SpanningTreeIsoperimetry.WeightedPowerSeries
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Actual circle evaluation of absolutely summable real power-series
coefficients. The multiplication proof is the absolutely convergent Cauchy
product, not an assumed evaluation homomorphism. -/
namespace SpanningTreeIsoperimetry.PowerSeriesCircle
open PowerSeries WeightedPowerSeries
open scoped BigOperators
noncomputable section

local instance : Fact (0<(2*Real.pi : ℝ)) := ⟨by positivity⟩
abbrev CircleDomain := AddCircle (2*Real.pi)

def mode (p : PowerSeries ℝ) (n : ℕ) (x : CircleDomain) : ℂ :=
  ((PowerSeries.coeff n p : ℝ) : ℂ)*fourier (n : ℤ) x

def value (p : PowerSeries ℝ) (x : CircleDomain) : ℂ := ∑' n,mode p n x

theorem norm_mode (p : PowerSeries ℝ) (n : ℕ) (x : CircleDomain) :
    ‖mode p n x‖=|PowerSeries.coeff n p| := by
  rw [mode,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have h : ‖fourier (n : ℤ) x‖=1 := Circle.norm_coe _
  rw [h,mul_one]

theorem mode_norm_summable {p : PowerSeries ℝ} (hp : SummableWeighted p)
    (x : CircleDomain) : Summable (fun n => ‖mode p n x‖) := by
  simpa only [norm_mode] using coefficients_summable hp

theorem mode_summable {p : PowerSeries ℝ} (hp : SummableWeighted p)
    (x : CircleDomain) : Summable (fun n => mode p n x) := (mode_norm_summable hp x).of_norm

theorem continuous_value {p : PowerSeries ℝ} (hp : SummableWeighted p) : Continuous (value p) := by
  change Continuous (fun x => ∑' n : ℕ,mode p n x)
  apply continuous_tsum (fun n : ℕ => continuous_const.mul (fourier (n : ℤ)).continuous)
    (coefficients_summable hp)
  intro n x
  exact (norm_mode p n x).le

theorem norm_value_le {p : PowerSeries ℝ} (hp : SummableWeighted p) (x : CircleDomain) :
    ‖value p x‖≤mass p := by
  apply (norm_tsum_le_tsum_norm (mode_norm_summable hp x)).trans
  simpa only [norm_mode] using coefficients_mass_le hp

@[simp] theorem value_one (x : CircleDomain) : value (1 : PowerSeries ℝ) x=1 := by
  rw [value,tsum_eq_single 0]
  · simp [mode]
  · intro n hn
    simp [mode,PowerSeries.coeff_C,hn]

@[simp] theorem value_C (r : ℝ) (x : CircleDomain) : value (PowerSeries.C r) x=(r : ℂ) := by
  rw [value,tsum_eq_single 0]
  · simp [mode]
  · intro n hn
    simp [mode,PowerSeries.coeff_C,hn]

theorem mode_mul (p q : PowerSeries ℝ) (n : ℕ) (x : CircleDomain) :
    mode (p*q) n x=∑ a∈Finset.antidiagonal n,mode p a.1 x*mode q a.2 x := by
  rw [mode,PowerSeries.coeff_mul]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have hn : (n : ℤ)=(a.1 : ℤ)+a.2 := by exact_mod_cast (Finset.mem_antidiagonal.mp ha).symm
  rw [hn,fourier_add]
  unfold mode
  ring

theorem value_mul {p q : PowerSeries ℝ} (hp : SummableWeighted p)
    (hq : SummableWeighted q) (x : CircleDomain) : value (p*q) x=value p x*value q x := by
  unfold value
  simp_rw [mode_mul]
  exact (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (mode_norm_summable hp x) (mode_norm_summable hq x)).symm

theorem value_pow {p : PowerSeries ℝ} (hp : SummableWeighted p)
    (m : ℕ) (x : CircleDomain) : value (p^m) x=(value p x)^m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ,value_mul (pow_control hp m).1 hp,ih,pow_succ]

end
end SpanningTreeIsoperimetry.PowerSeriesCircle
