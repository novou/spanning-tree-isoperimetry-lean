module

public import SquareMaximality.Rectangle.SharpTrapezoid
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-! A closed lower bound for the concrete rectangular trapezoidal error.
The proof uses a finite logarithmic sum, avoiding an unevaluated integral or
an external asymptotic estimate. -/
namespace SpanningTreeIsoperimetry.EpsilonBounds

open Set MeasureTheory
open SquareMaximality SquareMaximality.Rectangle
open Concrete Kernel Trapezoid

/-- Elementary linear majorant for the hyperbolic lattice kernel. -/
theorem kernel_le_pi_mul {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    kernel x ≤ Real.pi * x := by
  rw [kernel_eq_two_mul_arsinh_halfSine hx]
  have ha : Real.arsinh (halfSine x) ≤ halfSine x := by
    rw [← Real.sinh_le_sinh, Real.sinh_arsinh]
    exact Real.self_le_sinh_iff.mpr (halfSine_mem_Icc hx).1
  have hs : halfSine x ≤ (Real.pi / 2) * x :=
    Real.sin_le (mul_nonneg (by positivity) hx.1)
  linarith

/-- The concrete error is the integral of the logarithmic correction. -/
theorem epsilon_eq_neg_integral {r : ℕ} (hr : 0 < r) :
    epsilon squareLatticeEntropy r =
      -(∫ x in (0 : ℝ)..1, Real.log (1 - Real.exp ((-2 * kernel x) * r))) := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hid := SharpTrapezoid.sharpTrapezoidFormula.formula hr
  rw [trapezoid, Entropy.kernelIntegral_eq_squareLatticeEntropy] at hid
  have hm : (∫ x in (0 : ℝ)..1,
      Real.log (1 - Real.exp ((-2 * kernel x) * r))) =
      (r : ℝ) * ∫ x in (0 : ℝ)..1, scaledCorrection (r : ℝ) (kernel x) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    unfold scaledCorrection
    field_simp
  rw [div_eq_iff hr0] at hid
  unfold epsilon
  linarith

/-- Integrability includes the logarithmic singularity at zero. -/
theorem correction_integrable {r : ℕ} (hr : 0 < r) :
    IntervalIntegrable
      (fun x => -Real.log (1 - Real.exp ((-2 * kernel x) * r))) volume (0 : ℝ) 1 := by
  have h := (scaledCorrection_kernel_intervalIntegrable hr).const_mul (-(r : ℝ))
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  convert h using 1
  funext x
  unfold scaledCorrection
  field_simp

/-- A decaying exponential integrates without any limiting operation. -/
theorem integral_exp_decay {c : ℝ} (hc : 0 < c) :
    (∫ x in (0 : ℝ)..1, Real.exp (-c * x)) = (1 - Real.exp (-c)) / c := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hc.ne'),
    integral_exp]
  simp only [mul_zero, mul_one, Real.exp_zero, smul_eq_mul, inv_neg]
  field_simp
  ring

/-- The twenty positive exponential terms used in the lower bound. -/
noncomputable def lowerTerm (r n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-(2 * Real.pi * r * (n + 1)) * x) / (n + 1)

theorem lowerTerm_integrable (r n : ℕ) :
    IntervalIntegrable (lowerTerm r n) volume (0 : ℝ) 1 := by
  apply Continuous.intervalIntegrable
  unfold lowerTerm
  fun_prop

theorem integral_lowerTerm {r : ℕ} (hr : 0 < r) (n : ℕ) :
    (∫ x in (0 : ℝ)..1, lowerTerm r n x) =
      (1 - Real.exp (-(2 * Real.pi * r * (n + 1)))) /
        (2 * Real.pi * r * (n + 1)^2) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  unfold lowerTerm
  rw [intervalIntegral.integral_div,
    integral_exp_decay (by positivity : 0 < 2 * Real.pi * r * (n + 1))]
  field_simp

/-- Twenty logarithmic terms lie below the correction on the open interval. -/
theorem lowerSum_le_correction {r : ℕ} (hr : 0 < r)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (∑ n ∈ Finset.range 20, lowerTerm r n x) ≤
      -Real.log (1 - Real.exp ((-2 * kernel x) * r)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hkpos : 0 < kernel x := by
    rw [← Kernel.kernel_zero]
    exact Kernel.kernel_strictMonoOn (by simp) ⟨hx.1.le, hx.2.le⟩ hx.1
  have hz : |Real.exp ((-2 * kernel x) * r)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    nlinarith
  have hlog := sum_le_hasSum (Finset.range 20)
    (fun n _ => by positivity : ∀ n ∉ Finset.range 20,
      0 ≤ Real.exp ((-2 * kernel x) * r) ^ (n + 1) / (n + 1))
    (Real.hasSum_pow_div_log_of_abs_lt_one hz)
  refine le_trans (Finset.sum_le_sum fun n _ => ?_) hlog
  unfold lowerTerm
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hk := kernel_le_pi_mul ⟨hx.1.le, hx.2.le⟩
  have hm := mul_le_mul_of_nonneg_right hk (by positivity : 0 ≤ 2 * (r : ℝ) * (n + 1))
  push_cast
  nlinarith only [hm]

/-- The correction dominates the integral of the finite exponential sum. -/
theorem sum_integrals_le_epsilon {r : ℕ} (hr : 0 < r) :
    (∑ n ∈ Finset.range 20, ∫ x in (0 : ℝ)..1, lowerTerm r n x) ≤
      epsilon squareLatticeEntropy r := by
  rw [← intervalIntegral.integral_finsetSum
    (fun n _ => lowerTerm_integrable r n)]
  rw [epsilon_eq_neg_integral hr, ← intervalIntegral.integral_neg]
  have hi : IntervalIntegrable
      (fun x => ∑ n ∈ Finset.range 20, lowerTerm r n x) volume (0 : ℝ) 1 := by
    apply Continuous.intervalIntegrable
    unfold lowerTerm
    fun_prop
  apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hi
    (correction_integrable hr)
  exact fun x hx => lowerSum_le_correction hr hx

/-- A short exponential sum makes the endpoint loss less than one percent. -/
theorem exp_endpoint_lt_hundredth {r : ℕ} (hr : 0 < r) (n : ℕ) :
    Real.exp (-(2 * Real.pi * r * (n + 1))) < (1 : ℝ) / 100 := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h1 : 2 * Real.pi ≤ 2 * Real.pi * r :=
    le_mul_of_one_le_right (by positivity) hrR
  have h2 : 2 * Real.pi * r ≤ 2 * Real.pi * r * (n + 1) :=
    le_mul_of_one_le_right (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have h6 : (6 : ℝ) ≤ 2 * Real.pi * r * (n + 1) := by
    linarith [Real.pi_gt_three]
  have hseries := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 6) 5
  norm_num [Finset.sum_range_succ] at hseries
  have h100 : (100 : ℝ) < Real.exp (2 * Real.pi * r * (n + 1)) :=
    lt_of_lt_of_le (by linarith) (Real.exp_le_exp.mpr h6)
  rw [Real.exp_neg]
  simpa only [one_div] using
    (inv_lt_inv₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 100)).mpr h100

/-- Each integrated term has a uniform rational lower bound after scaling. -/
theorem lowerTerm_integral_bound {r : ℕ} (hr : 0 < r) (n : ℕ) :
    ((11 : ℝ) / 70) / (n + 1)^2 <
      (r : ℝ) * ∫ x in (0 : ℝ)..1, lowerTerm r n x := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have he := exp_endpoint_lt_hundredth hr n
  have hp := Real.pi_lt_d2
  have hcoef : (11 : ℝ) / 70 <
      (1 - Real.exp (-(2 * Real.pi * r * (n + 1)))) / (2 * Real.pi) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    linarith
  calc
    ((11 : ℝ) / 70) / (n + 1)^2 <
        ((1 - Real.exp (-(2 * Real.pi * r * (n + 1)))) / (2 * Real.pi)) /
          (n + 1)^2 := div_lt_div_of_pos_right hcoef (by positivity)
    _ = (r : ℝ) * ∫ x in (0 : ℝ)..1, lowerTerm r n x := by
      rw [integral_lowerTerm hr]
      field_simp

/-- The explicit finite sum supplies the quarter margin. -/
theorem quarter_lt_twenty_terms :
    (1 : ℝ) / 4 < ∑ n ∈ Finset.range 20, ((11 : ℝ) / 70) / (n + 1)^2 := by
  norm_num [Finset.sum_range_succ]

/-- Closed lower bound for the concrete rectangular error at every positive width. -/
theorem quarter_div_lt_epsilon {r : ℕ} (hr : 0 < r) :
    (1 : ℝ) / (4 * r) < epsilon squareLatticeEntropy r := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hsum :
      (∑ n ∈ Finset.range 20, ((11 : ℝ) / 70) / (n + 1)^2) ≤
        (r : ℝ) * epsilon squareLatticeEntropy r := by
    calc
      _ ≤ ∑ n ∈ Finset.range 20,
          (r : ℝ) * ∫ x in (0 : ℝ)..1, lowerTerm r n x :=
        Finset.sum_le_sum (fun n _ => (lowerTerm_integral_bound hr n).le)
      _ = (r : ℝ) * ∑ n ∈ Finset.range 20,
          ∫ x in (0 : ℝ)..1, lowerTerm r n x := (Finset.mul_sum ..).symm
      _ ≤ (r : ℝ) * epsilon squareLatticeEntropy r :=
        mul_le_mul_of_nonneg_left (sum_integrals_le_epsilon hr) hrR.le
  have hquarter := quarter_lt_twenty_terms.trans_le hsum
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * r)).mpr
  nlinarith

/-- The second conclusion of the manuscript's error lemma. -/
theorem epsilon_div_antitone {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) :
    epsilon squareLatticeEntropy s / s ≤ epsilon squareLatticeEntropy r / r := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have h := SharpTrapezoid.sharpTrapezoidFormula.epsilon_scaled_antitone hr hrs
  rw [Entropy.kernelIntegral_eq_squareLatticeEntropy] at h
  exact (div_le_div_iff₀ hsR hrR).mpr (by simpa only [mul_comm] using h)

end SpanningTreeIsoperimetry.EpsilonBounds
