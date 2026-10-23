module

public import SquareMaximality.Boundary.DeterminantReduction
public import SquareMaximality.ClosedWalk.Series
public import SquareMaximality.Rectangle.Entropy
public import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric

@[expose] public section

set_option autoImplicit false

/-!
# The square-lattice closed-walk entropy series

This file evaluates the scalar closed-walk series left by the boundary
determinant reduction.  The combinatorial coefficient is first converted to
the square of a normalized central binomial coefficient.  We then use the
one-variable central-binomial logarithmic generating function under a sine
moment integral.
-/

namespace SquareMaximality
namespace ClosedWalk

open Set MeasureTheory Filter
open scoped Interval Topology

/-- The normalized central binomial coefficient. -/
noncomputable def normalizedCentralBinom (n : ℕ) : ℝ :=
  (Nat.centralBinom n : ℝ) / (4 : ℝ) ^ n

/-- The positive-index logarithmic central-binomial term. -/
noncomputable def centralLogTerm (n : ℕ) : ℝ :=
  normalizedCentralBinom (n + 1) / (n + 1 : ℝ)

lemma centralLogGenerating_eq_tsum (t : ℝ) :
    centralLogGenerating t =
      ∑' n : ℕ, centralLogTerm n * t ^ (n + 1) := by
  rw [centralLogGenerating]
  apply tsum_congr
  intro n
  rfl

lemma normalizedCentralBinom_nonneg (n : ℕ) :
    0 ≤ normalizedCentralBinom n := by
  exact div_nonneg (by positivity) (by positivity)

lemma normalizedCentralBinom_succ (n : ℕ) :
    normalizedCentralBinom (n + 1) =
      ((2 * n + 1 : ℝ) / (2 * (n + 1))) * normalizedCentralBinom n := by
  have hrec : (n + 1 : ℝ) * Nat.centralBinom (n + 1) =
      (2 * (2 * n + 1) : ℝ) * Nat.centralBinom n := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  unfold normalizedCentralBinom
  rw [pow_succ]
  field_simp
  nlinarith

/-- A Wallis-type bound sufficient for absolute convergence of the squared
central-binomial logarithmic series. -/
lemma normalizedCentralBinom_sq_le (n : ℕ) :
    normalizedCentralBinom n ^ 2 ≤ 1 / (n + 1 : ℝ) := by
  induction n with
  | zero => norm_num [normalizedCentralBinom, Nat.centralBinom_zero]
  | succ n ih =>
      rw [normalizedCentralBinom_succ]
      have hn : (0 : ℝ) ≤ n := by positivity
      have hn1 : (0 : ℝ) < n + 1 := by positivity
      have hn2 : (0 : ℝ) < n + 2 := by positivity
      calc
        (((2 * n + 1 : ℝ) / (2 * (n + 1))) *
            normalizedCentralBinom n) ^ 2 ≤
            ((2 * n + 1 : ℝ) / (2 * (n + 1))) ^ 2 *
              (1 / (n + 1 : ℝ)) := by
                rw [mul_pow]
                gcongr
        _ ≤ 1 / (n + 2 : ℝ) := by
              field_simp
              nlinarith [sq_nonneg (n : ℝ)]
        _ = 1 / ((n + 1 : ℕ) + 1 : ℝ) := by push_cast; ring

lemma boundary_evenClosedWordTerm_eq (a : ℕ) :
    Boundary.evenClosedWordTerm a =
      normalizedCentralBinom (a + 1) ^ 2 / (2 * (a + 1 : ℝ)) := by
  unfold Boundary.evenClosedWordTerm normalizedCentralBinom
  rw [closedWordCount_even, ← Nat.centralBinom_eq_two_mul_choose]
  have hpow : (4 : ℝ) ^ (2 * (a + 1)) = ((4 : ℝ) ^ (a + 1)) ^ 2 := by
    rw [show 2 * (a + 1) = (a + 1) * 2 by omega, pow_mul]
  push_cast
  rw [hpow]
  field_simp

lemma boundary_evenClosedWordTerm_nonneg (a : ℕ) :
    0 ≤ Boundary.evenClosedWordTerm a := by
  rw [boundary_evenClosedWordTerm_eq]
  positivity

lemma boundary_evenClosedWordTerm_norm_le (a : ℕ) :
    ‖Boundary.evenClosedWordTerm a‖ ≤ 1 / (a + 1 : ℝ) ^ 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (boundary_evenClosedWordTerm_nonneg a),
    boundary_evenClosedWordTerm_eq]
  have hm : (0 : ℝ) < a + 1 := by positivity
  have hm' : (0 : ℝ) < a + 2 := by positivity
  calc
    normalizedCentralBinom (a + 1) ^ 2 / (2 * (a + 1 : ℝ)) ≤
        (1 / (a + 2 : ℝ)) / (2 * (a + 1 : ℝ)) := by
      gcongr
      have h := normalizedCentralBinom_sq_le (a + 1)
      norm_num [Nat.cast_add] at h
      rw [show (a : ℝ) + 1 + 1 = a + 2 by ring] at h
      simpa only [one_div] using h
    _ ≤ 1 / (a + 1 : ℝ) ^ 2 := by
      field_simp
      nlinarith

/-- Absolute convergence of the scalar walk-entropy series. -/
theorem summable_evenClosedWordTerm :
    Summable Boundary.evenClosedWordTerm := by
  have hp : Summable (fun a : ℕ ↦ 1 / (a + 1 : ℝ) ^ 2) := by
    have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 h
  exact hp.of_norm_bounded boundary_evenClosedWordTerm_norm_le

lemma wallisProduct_eq_normalizedCentralBinom (n : ℕ) :
    (∏ i ∈ Finset.range n, (2 * (i : ℝ) + 1) / (2 * i + 2)) =
      normalizedCentralBinom n := by
  induction n with
  | zero => simp [normalizedCentralBinom, Nat.centralBinom_zero]
  | succ n ih =>
      rw [Finset.prod_range_succ, ih, normalizedCentralBinom_succ]
      ring

lemma integral_sin_pow_even_full (n : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ (2 * n)) =
      Real.pi * normalizedCentralBinom n := by
  rw [integral_sin_pow_even,
    wallisProduct_eq_normalizedCentralBinom]

lemma integral_sin_pow_even_half (n : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi / 2, Real.sin θ ^ (2 * n)) =
      (Real.pi / 2) * normalizedCentralBinom n := by
  have hleft : IntervalIntegrable (fun θ : ℝ => Real.sin θ ^ (2 * n)) volume
      (0 : ℝ) (Real.pi / 2) :=
    (Real.continuous_sin.pow _).intervalIntegrable _ _
  have hright : IntervalIntegrable (fun θ : ℝ => Real.sin θ ^ (2 * n)) volume
      (Real.pi / 2) Real.pi :=
    (Real.continuous_sin.pow _).intervalIntegrable _ _
  have hsplit :
      (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ (2 * n)) =
        2 * (∫ θ in (0 : ℝ)..Real.pi / 2, Real.sin θ ^ (2 * n)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
    conv =>
      left
      right
      arg 1
      intro θ
      rw [← Real.sin_pi_sub]
    rw [intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => Real.sin θ ^ (2 * n)), sub_self,
      show Real.pi - Real.pi / 2 = Real.pi / 2 by ring]
    ring
  rw [integral_sin_pow_even_full] at hsplit
  linarith

/-- The sine-moment integrand whose integral is one squared
central-binomial walk term. -/
noncomputable def sineLogTerm (n : ℕ) (θ : ℝ) : ℝ :=
  centralLogTerm n * Real.sin θ ^ (2 * (n + 1))

lemma sineLogTerm_continuous (n : ℕ) : Continuous (sineLogTerm n) := by
  unfold sineLogTerm
  fun_prop

lemma integral_sineLogTerm (n : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi / 2, sineLogTerm n θ) =
      Real.pi * Boundary.evenClosedWordTerm n := by
  rw [show sineLogTerm n = fun θ : ℝ =>
      centralLogTerm n * Real.sin θ ^ (2 * (n + 1)) by rfl,
    intervalIntegral.integral_const_mul, integral_sin_pow_even_half,
    boundary_evenClosedWordTerm_eq]
  unfold centralLogTerm
  field_simp

lemma sineLogTerm_nonneg_of_mem {n : ℕ} {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    0 ≤ sineLogTerm n θ := by
  unfold sineLogTerm centralLogTerm
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
      (hθ.2.trans (by nlinarith [Real.pi_pos]))
  exact mul_nonneg
    (div_nonneg (normalizedCentralBinom_nonneg _) (by positivity))
    (pow_nonneg hsin _)

lemma sineLogTerm_integrable_restrict (n : ℕ) :
    Integrable (sineLogTerm n)
      (volume.restrict (Set.Ioc (0 : ℝ) (Real.pi / 2))) := by
  exact ((sineLogTerm_continuous n).continuousOn.integrableOn_compact
    isCompact_Icc).mono_set Set.Ioc_subset_Icc_self

lemma integral_norm_sineLogTerm_restrict (n : ℕ) :
    (∫ θ, ‖sineLogTerm n θ‖
      ∂(volume.restrict (Set.Ioc (0 : ℝ) (Real.pi / 2)))) =
      Real.pi * Boundary.evenClosedWordTerm n := by
  rw [← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  calc
    (∫ θ in (0 : ℝ)..Real.pi / 2, ‖sineLogTerm n θ‖) =
        ∫ θ in (0 : ℝ)..Real.pi / 2, sineLogTerm n θ := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      have hθ' : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
        simpa only [uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hθ
      change ‖sineLogTerm n θ‖ = sineLogTerm n θ
      rw [Real.norm_eq_abs, abs_of_nonneg (sineLogTerm_nonneg_of_mem hθ')]
    _ = Real.pi * Boundary.evenClosedWordTerm n := integral_sineLogTerm n

lemma summable_integral_norm_sineLogTerm :
    Summable (fun n : ℕ =>
      ∫ θ, ‖sineLogTerm n θ‖
        ∂(volume.restrict (Set.Ioc (0 : ℝ) (Real.pi / 2)))) := by
  simpa only [integral_norm_sineLogTerm_restrict] using
    summable_evenClosedWordTerm.mul_left Real.pi

lemma sineLogTerm_tsum_eq_centralLogGenerating (t : ℝ) :
    (∑' n : ℕ, sineLogTerm n t) =
      centralLogGenerating (Real.sin t ^ 2) := by
  rw [centralLogGenerating_eq_tsum]
  apply tsum_congr
  intro n
  unfold sineLogTerm
  rw [pow_mul]

/-- Exact reduction of the squared central-binomial series to the public
one-variable logarithmic generating function. -/
theorem integral_centralLogGenerating_sin_sq_eq_tsum :
    (∫ θ in (0 : ℝ)..Real.pi / 2,
        centralLogGenerating (Real.sin θ ^ 2)) =
      Real.pi * (∑' n : ℕ, Boundary.evenClosedWordTerm n) := by
  have hsum := MeasureTheory.hasSum_integral_of_summable_integral_norm
    sineLogTerm_integrable_restrict summable_integral_norm_sineLogTerm
  calc
    (∫ θ in (0 : ℝ)..Real.pi / 2,
        centralLogGenerating (Real.sin θ ^ 2)) =
        ∫ θ, (∑' n : ℕ, sineLogTerm n θ)
          ∂(volume.restrict (Set.Ioc (0 : ℝ) (Real.pi / 2))) := by
      rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
      apply integral_congr_ae
      filter_upwards with θ
      exact (sineLogTerm_tsum_eq_centralLogGenerating θ).symm
    _ = ∑' n : ℕ, ∫ θ, sineLogTerm n θ
          ∂(volume.restrict (Set.Ioc (0 : ℝ) (Real.pi / 2))) :=
      hsum.tsum_eq.symm
    _ = ∑' n : ℕ, Real.pi * Boundary.evenClosedWordTerm n := by
      apply tsum_congr
      intro n
      rw [← intervalIntegral.integral_of_le
        (by positivity : (0 : ℝ) ≤ Real.pi / 2), integral_sineLogTerm]
    _ = Real.pi * (∑' n : ℕ, Boundary.evenClosedWordTerm n) := by
      rw [tsum_mul_left]

lemma centralLogGenerating_eq_closedForm_one :
    centralLogGenerating 1 = centralLogClosedForm 1 := by
  rw [centralLogGenerating_eq_tsum]
  have h := tsum_boundaryCentralCoeff
  change (∑' n : ℕ, centralLogTerm n) = centralLogClosedForm 1 at h
  simpa only [one_pow, mul_one] using h

lemma centralLogGenerating_eq_closedForm_of_mem_Icc {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    centralLogGenerating t = centralLogClosedForm t := by
  rcases ht with ⟨ht0, ht1⟩
  rcases lt_or_eq_of_le ht1 with ht1 | rfl
  · apply centralLogGenerating_eq_closedForm
    rw [abs_of_nonneg ht0]
    exact ht1
  · exact centralLogGenerating_eq_closedForm_one

lemma centralLogGenerating_sin_sq_eq_closedForm (θ : ℝ) :
    centralLogGenerating (Real.sin θ ^ 2) =
      centralLogClosedForm (Real.sin θ ^ 2) := by
  apply centralLogGenerating_eq_closedForm_of_mem_Icc
  exact ⟨sq_nonneg _, Real.sin_sq_le_one θ⟩

lemma centralLogClosedForm_sin_sq {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    centralLogClosedForm (Real.sin θ ^ 2) =
      -4 * Real.log (Real.cos (θ / 2)) := by
  have hlow : -(Real.pi / 2) ≤ θ := by
    nlinarith [hθ.1, Real.pi_pos]
  have hsqrt : Real.sqrt (1 - Real.sin θ ^ 2) = Real.cos θ := by
    exact (Real.cos_eq_sqrt_one_sub_sin_sq hlow hθ.2).symm
  have hhalf : (1 + Real.cos θ) / 2 = Real.cos (θ / 2) ^ 2 := by
    rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul]
    ring_nf
  have hcospos : 0 < Real.cos (θ / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [hθ.1, hθ.2, Real.pi_pos]
  unfold centralLogClosedForm
  rw [hsqrt, hhalf, Real.log_pow]
  ring

/-- The generating-function integral is a quarter-period log-cosine
integral. -/
theorem integral_centralLogGenerating_sin_sq_eq_logCosQuarter :
    (∫ θ in (0 : ℝ)..Real.pi / 2,
        centralLogGenerating (Real.sin θ ^ 2)) =
      -8 * (∫ u in (0 : ℝ)..Real.pi / 4, Real.log (Real.cos u)) := by
  calc
    (∫ θ in (0 : ℝ)..Real.pi / 2,
        centralLogGenerating (Real.sin θ ^ 2)) =
        ∫ θ in (0 : ℝ)..Real.pi / 2,
          -4 * Real.log (Real.cos (θ / 2)) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      have hθ' : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
        simpa only [uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hθ
      change centralLogGenerating (Real.sin θ ^ 2) =
        -4 * Real.log (Real.cos (θ / 2))
      rw [centralLogGenerating_sin_sq_eq_closedForm θ,
        centralLogClosedForm_sin_sq hθ']
    _ = -4 * (∫ θ in (0 : ℝ)..Real.pi / 2,
          Real.log (Real.cos (θ / 2))) := by
      rw [intervalIntegral.integral_const_mul]
    _ = -8 * (∫ u in (0 : ℝ)..Real.pi / 4, Real.log (Real.cos u)) := by
      rw [intervalIntegral.integral_comp_div
        (fun u : ℝ => Real.log (Real.cos u)) two_ne_zero]
      norm_num
      ring_nf

/-- Catalan's constant as the removable-endpoint arctangent quotient
integral supplied by the rectangle entropy calculation. -/
theorem integral_arctan_div_eq_catalanConstant :
    (∫ u in (0 : ℝ)..1, Real.arctan u / u) = catalanConstant := by
  calc
    (∫ u in (0 : ℝ)..1, Real.arctan u / u) =
        ∫ u in (0 : ℝ)..1,
          ∫ v in (0 : ℝ)..1, Rectangle.Entropy.rationalKernel u v := by
      apply intervalIntegral.integral_congr_ae
      have hzero : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
        simp [ae_iff, measure_singleton]
      filter_upwards [hzero] with u hu
      intro _hu_mem
      exact (Rectangle.Entropy.integral_rationalKernel_eq_arctan_div hu).symm
    _ = catalanConstant :=
      Rectangle.Entropy.rationalDoubleIntegral_eq_catalanConstant

noncomputable def arctanLogProduct (u : ℝ) : ℝ :=
  Real.arctan u * Real.log u

noncomputable def arctanLogDerivative (u : ℝ) : ℝ :=
  Real.arctan u / u + Real.log u / (1 + u ^ 2)

lemma hasDerivAt_arctanLogProduct {u : ℝ} (hu : 0 < u) :
    HasDerivAt arctanLogProduct (arctanLogDerivative u) u := by
  change HasDerivAt (fun x : ℝ => Real.arctan x * Real.log x)
    (Real.arctan u / u + Real.log u / (1 + u ^ 2)) u
  apply ((Real.hasDerivAt_arctan u).mul
    (Real.hasDerivAt_log hu.ne')).congr_deriv
  field_simp [hu.ne']
  ring

lemma intervalIntegrable_arctan_div :
    IntervalIntegrable (fun u : ℝ => Real.arctan u / u) volume 0 1 := by
  have hcontinuous : Continuous (fun u : ℝ =>
      ∫ v in (0 : ℝ)..1, Rectangle.Entropy.rationalKernel u v) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      Rectangle.Entropy.rationalKernel_continuous 0 1
  have hint : IntervalIntegrable (fun u : ℝ =>
      ∫ v in (0 : ℝ)..1, Rectangle.Entropy.rationalKernel u v) volume 0 1 :=
    hcontinuous.intervalIntegrable 0 1
  apply hint.congr_uIoo
  intro u hu
  norm_num at hu
  exact Rectangle.Entropy.integral_rationalKernel_eq_arctan_div hu.1.ne'

lemma intervalIntegrable_log_div_one_add_sq :
    IntervalIntegrable (fun u : ℝ => Real.log u / (1 + u ^ 2)) volume 0 1 := by
  have hfactor : Continuous (fun u : ℝ => 1 / (1 + u ^ 2)) := by
    exact continuous_const.div (continuous_const.add (continuous_id.pow 2))
      (fun u => by positivity)
  have hlog : IntervalIntegrable Real.log volume (0 : ℝ) 1 :=
    intervalIntegral.intervalIntegrable_log'
  simpa only [div_eq_mul_inv, one_div, one_mul] using
    (hlog.mul_continuousOn hfactor.continuousOn)

lemma intervalIntegrable_arctanLogDerivative :
    IntervalIntegrable arctanLogDerivative volume 0 1 := by
  unfold arctanLogDerivative
  exact intervalIntegrable_arctan_div.add intervalIntegrable_log_div_one_add_sq

lemma tendsto_arctanLogProduct_zero_right :
    Tendsto arctanLogProduct (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have harctan : Tendsto (fun u : ℝ => Real.arctan u / u)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
    have h := (Real.hasDerivAt_arctan 0).tendsto_slope_zero_right
    norm_num at h
    simpa only [zero_add, Real.arctan_zero, sub_zero, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using h
  have hlog : Tendsto (fun u : ℝ => Real.log u * u)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa only [Real.rpow_one] using
      (tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one)
  have hprod : Tendsto
      (fun u : ℝ => (Real.arctan u / u) * (Real.log u * u))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa only [one_mul] using harctan.mul hlog
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu0 : 0 < u := hu
  unfold arctanLogProduct
  field_simp [hu0.ne']

lemma tendsto_arctanLogProduct_one_left :
    Tendsto arctanLogProduct (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  have hcontinuous : ContinuousAt arctanLogProduct 1 := by
    unfold arctanLogProduct
    fun_prop (disch := norm_num)
  have h : Tendsto arctanLogProduct
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (arctanLogProduct 1)) :=
    hcontinuous.tendsto.mono_left inf_le_left
  have hvalue : arctanLogProduct 1 = 0 := by simp [arctanLogProduct]
  rwa [hvalue] at h

/-- Integration by parts at the removable logarithmic endpoint. -/
theorem integral_arctan_div_eq_neg_log_div_one_add_sq :
    (∫ u in (0 : ℝ)..1, Real.arctan u / u) =
      -(∫ u in (0 : ℝ)..1, Real.log u / (1 + u ^ 2)) := by
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (f := arctanLogProduct) (f' := arctanLogDerivative)
    (fa := (0 : ℝ)) (fb := (0 : ℝ)) (by norm_num : (0 : ℝ) < 1)
    (fun u hu => hasDerivAt_arctanLogProduct hu.1)
    intervalIntegrable_arctanLogDerivative
    tendsto_arctanLogProduct_zero_right tendsto_arctanLogProduct_one_left
  unfold arctanLogDerivative at hfund
  rw [intervalIntegral.integral_add intervalIntegrable_arctan_div
    intervalIntegrable_log_div_one_add_sq] at hfund
  linarith

theorem integral_neg_log_div_one_add_sq_eq_catalanConstant :
    -(∫ u in (0 : ℝ)..1, Real.log u / (1 + u ^ 2)) =
      catalanConstant := by
  rw [← integral_arctan_div_eq_neg_log_div_one_add_sq,
    integral_arctan_div_eq_catalanConstant]

lemma tan_interval_continuous :
    ContinuousOn Real.tan ([[ (0 : ℝ), Real.pi / 4 ]]) := by
  apply Real.continuousOn_tan_Ioo.mono
  intro θ hθ
  rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 4)] at hθ
  exact ⟨by nlinarith [hθ.1, Real.pi_pos],
    by nlinarith [hθ.2, Real.pi_pos]⟩

lemma hasDerivAt_tan_on_quarter {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := by
  apply Real.hasDerivAt_tan_of_mem_Ioo
  exact ⟨by nlinarith [hθ.1, Real.pi_pos],
    by nlinarith [hθ.2, Real.pi_pos]⟩

lemma logTan_changeOfVariables_integrand {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4)) :
    (Real.log (Real.tan θ) / (1 + Real.tan θ ^ 2)) *
        (1 / Real.cos θ ^ 2) = Real.log (Real.tan θ) := by
  have hcospos : 0 < Real.cos θ := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by nlinarith [hθ.1, Real.pi_pos],
      by nlinarith [hθ.2, Real.pi_pos]⟩
  rw [div_eq_mul_inv, one_div, Real.inv_one_add_tan_sq hcospos.ne']
  field_simp [hcospos.ne']

/-- The tangent substitution transports the logarithmic Catalan integral
to a quarter-period log-tangent integral. -/
theorem integral_log_tan_quarter_eq_log_div_one_add_sq :
    (∫ θ in (0 : ℝ)..Real.pi / 4, Real.log (Real.tan θ)) =
      ∫ u in (0 : ℝ)..1, Real.log u / (1 + u ^ 2) := by
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.pi / 4)
    (f := Real.tan) (f' := fun θ : ℝ => 1 / Real.cos θ ^ 2)
    (g := fun u : ℝ => Real.log u / (1 + u ^ 2))
    tan_interval_continuous
    (by
      intro θ hθ
      rw [min_eq_left (by positivity : (0 : ℝ) ≤ Real.pi / 4),
        max_eq_right (by positivity : (0 : ℝ) ≤ Real.pi / 4)] at hθ
      exact hasDerivAt_tan_on_quarter hθ)
    (by
      intro θ _hθ
      exact one_div_nonneg.mpr (sq_nonneg _))
  rw [Real.tan_zero, Real.tan_pi_div_four] at hsub
  calc
    (∫ θ in (0 : ℝ)..Real.pi / 4, Real.log (Real.tan θ)) =
        ∫ θ in (0 : ℝ)..Real.pi / 4,
          ((fun u : ℝ => Real.log u / (1 + u ^ 2)) ∘ Real.tan) θ *
            (1 / Real.cos θ ^ 2) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      have hθ' : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4) := by
        simpa only [uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 4)] using hθ
      change Real.log (Real.tan θ) =
        (Real.log (Real.tan θ) / (1 + Real.tan θ ^ 2)) *
          (1 / Real.cos θ ^ 2)
      exact (logTan_changeOfVariables_integrand hθ').symm
    _ = ∫ u in (0 : ℝ)..1, Real.log u / (1 + u ^ 2) := hsub

theorem neg_integral_log_tan_quarter_eq_catalanConstant :
    -(∫ θ in (0 : ℝ)..Real.pi / 4, Real.log (Real.tan θ)) =
      catalanConstant := by
  rw [integral_log_tan_quarter_eq_log_div_one_add_sq,
    integral_neg_log_div_one_add_sq_eq_catalanConstant]

lemma log_tan_eq_log_sin_sub_log_cos {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4)) :
    Real.log (Real.tan θ) =
      Real.log (Real.sin θ) - Real.log (Real.cos θ) := by
  by_cases hzero : θ = 0
  · subst θ
    simp
  · have hpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hzero)
    have hltpi : θ < Real.pi := by nlinarith [hθ.2, Real.pi_pos]
    have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hpos hltpi
    have hcos : 0 < Real.cos θ := by
      apply Real.cos_pos_of_mem_Ioo
      exact ⟨by nlinarith [hpos, Real.pi_pos],
        by nlinarith [hθ.2, Real.pi_pos]⟩
    rw [Real.tan_eq_sin_div_cos, Real.log_div hsin.ne' hcos.ne']

theorem integral_log_tan_quarter_eq_log_sin_sub_log_cos :
    (∫ θ in (0 : ℝ)..Real.pi / 4, Real.log (Real.tan θ)) =
      (∫ θ in (0 : ℝ)..Real.pi / 4, Real.log (Real.sin θ)) -
        ∫ θ in (0 : ℝ)..Real.pi / 4, Real.log (Real.cos θ) := by
  have hsin : IntervalIntegrable (Real.log ∘ Real.sin) volume
      0 (Real.pi / 4) :=
    intervalIntegrable_log_sin
  have hcos : IntervalIntegrable (Real.log ∘ Real.cos) volume
      0 (Real.pi / 4) :=
    intervalIntegrable_log_cos
  calc
    (∫ θ in (0 : ℝ)..Real.pi / 4, Real.log (Real.tan θ)) =
        ∫ θ in (0 : ℝ)..Real.pi / 4,
          (Real.log (Real.sin θ) - Real.log (Real.cos θ)) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      have hθ' : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4) := by
        simpa only [uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 4)] using hθ
      exact log_tan_eq_log_sin_sub_log_cos hθ'
    _ = (∫ θ in (0 : ℝ)..Real.pi / 4, Real.log (Real.sin θ)) -
        ∫ θ in (0 : ℝ)..Real.pi / 4, Real.log (Real.cos θ) := by
      simpa only [Function.comp_apply] using
        (intervalIntegral.integral_sub hsin hcos)

lemma integral_log_sin_second_quarter_eq_log_cos_quarter :
    (∫ θ in Real.pi / 4..Real.pi / 2, Real.log (Real.sin θ)) =
      ∫ u in (0 : ℝ)..Real.pi / 4, Real.log (Real.cos u) := by
  calc
    (∫ θ in Real.pi / 4..Real.pi / 2, Real.log (Real.sin θ)) =
        ∫ θ in Real.pi / 4..Real.pi / 2,
          Real.log (Real.cos (Real.pi / 2 - θ)) := by
      apply intervalIntegral.integral_congr
      intro θ _hθ
      change Real.log (Real.sin θ) =
        Real.log (Real.cos (Real.pi / 2 - θ))
      rw [Real.cos_pi_div_two_sub]
    _ = ∫ u in (0 : ℝ)..Real.pi / 4, Real.log (Real.cos u) := by
      rw [intervalIntegral.integral_comp_sub_left
        (fun u : ℝ => Real.log (Real.cos u)) (Real.pi / 2)]
      congr 1 <;> ring

theorem integral_log_sin_quarter_add_log_cos_quarter :
    (∫ θ in (0 : ℝ)..Real.pi / 4, Real.log (Real.sin θ)) +
        (∫ θ in (0 : ℝ)..Real.pi / 4, Real.log (Real.cos θ)) =
      -Real.log 2 * Real.pi / 2 := by
  have hleft : IntervalIntegrable (Real.log ∘ Real.sin) volume
      0 (Real.pi / 4) := intervalIntegrable_log_sin
  have hright : IntervalIntegrable (Real.log ∘ Real.sin) volume
      (Real.pi / 4) (Real.pi / 2) := intervalIntegrable_log_sin
  calc
    (∫ θ in (0 : ℝ)..Real.pi / 4, Real.log (Real.sin θ)) +
        (∫ θ in (0 : ℝ)..Real.pi / 4, Real.log (Real.cos θ)) =
        (∫ θ in (0 : ℝ)..Real.pi / 4, Real.log (Real.sin θ)) +
          ∫ θ in Real.pi / 4..Real.pi / 2, Real.log (Real.sin θ) := by
      rw [integral_log_sin_second_quarter_eq_log_cos_quarter]
    _ = ∫ θ in (0 : ℝ)..Real.pi / 2, Real.log (Real.sin θ) := by
      simpa only [Function.comp_apply] using
        (intervalIntegral.integral_add_adjacent_intervals hleft hright)
    _ = -Real.log 2 * Real.pi / 2 := integral_log_sin_zero_pi_div_two

theorem integral_log_cos_sub_log_sin_quarter_eq_catalanConstant :
    (∫ θ in (0 : ℝ)..Real.pi / 4, Real.log (Real.cos θ)) -
        (∫ θ in (0 : ℝ)..Real.pi / 4, Real.log (Real.sin θ)) =
      catalanConstant := by
  rw [← neg_sub,
    ← integral_log_tan_quarter_eq_log_sin_sub_log_cos,
    neg_integral_log_tan_quarter_eq_catalanConstant]

/-- The classical quarter-period log-cosine evaluation, derived here from
the repository's series definition of Catalan's constant. -/
theorem integral_log_cos_quarter :
    (∫ θ in (0 : ℝ)..Real.pi / 4, Real.log (Real.cos θ)) =
      catalanConstant / 2 - Real.pi * Real.log 2 / 4 := by
  have hsum := integral_log_sin_quarter_add_log_cos_quarter
  have hdiff := integral_log_cos_sub_log_sin_quarter_eq_catalanConstant
  nlinarith

lemma log_four_eq_two_mul_log_two :
    Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- Exact evaluation of the square-lattice closed-walk entropy series. -/
theorem tsum_evenClosedWordTerm :
    (∑' n : ℕ, Boundary.evenClosedWordTerm n) =
      Real.log 4 - squareLatticeEntropy := by
  have hseries :
      Real.pi * (∑' n : ℕ, Boundary.evenClosedWordTerm n) =
        -8 * (catalanConstant / 2 - Real.pi * Real.log 2 / 4) := by
    calc
      Real.pi * (∑' n : ℕ, Boundary.evenClosedWordTerm n) =
          ∫ θ in (0 : ℝ)..Real.pi / 2,
            centralLogGenerating (Real.sin θ ^ 2) :=
        integral_centralLogGenerating_sin_sq_eq_tsum.symm
      _ = -8 * (∫ u in (0 : ℝ)..Real.pi / 4, Real.log (Real.cos u)) :=
        integral_centralLogGenerating_sin_sq_eq_logCosQuarter
      _ = -8 * (catalanConstant / 2 - Real.pi * Real.log 2 / 4) := by
        rw [integral_log_cos_quarter]
  rw [squareLatticeEntropy, log_four_eq_two_mul_log_two]
  apply mul_left_cancel₀ (a := Real.pi) Real.pi_ne_zero
  calc
    Real.pi * (∑' n : ℕ, Boundary.evenClosedWordTerm n) =
        -8 * (catalanConstant / 2 - Real.pi * Real.log 2 / 4) := hseries
    _ = Real.pi * (2 * Real.log 2 - 4 * catalanConstant / Real.pi) := by
      field_simp [Real.pi_ne_zero]
      ring

/-- `HasSum` form required by
`Boundary.BoundaryDeterminantSeriesInputs.walkEntropy`. -/
theorem hasSum_evenClosedWordTerm :
    HasSum Boundary.evenClosedWordTerm
      (Real.log 4 - squareLatticeEntropy) := by
  rw [← tsum_evenClosedWordTerm]
  exact summable_evenClosedWordTerm.hasSum

/-- Equivalent kernel-integral spelling, using the independently formalized
rectangle entropy evaluation. -/
theorem hasSum_evenClosedWordTerm_kernelIntegral :
    HasSum Boundary.evenClosedWordTerm
      (Real.log 4 - Rectangle.Trapezoid.kernelIntegral) := by
  rw [Rectangle.Entropy.kernelIntegral_eq_squareLatticeEntropy]
  exact hasSum_evenClosedWordTerm

end ClosedWalk
end SquareMaximality
