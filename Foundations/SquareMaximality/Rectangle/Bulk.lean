module

public import SquareMaximality.Rectangle.Spectral
public import SquareMaximality.Rectangle.SharpTrapezoid
public import Mathlib.Analysis.SumIntegralComparisons

@[expose] public section

set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The bulk square-rectangle limit

This file extracts the thermodynamic limit of the exact rectangular product.
The only graph-theoretic hypothesis is the rectangular Matrix--Tree input.
-/

namespace SquareMaximality.Rectangle.Bulk

open Filter Set MeasureTheory
open scoped Topology Interval
open Concrete Kernel Trapezoid Product

noncomputable section

/-- The grid points used in the right Riemann sum. -/
private noncomputable def grid (a k : ℕ) : ℝ := (k : ℝ) / (a : ℝ)

private theorem grid_zero (a : ℕ) : grid a 0 = 0 := by
  simp [grid]

private theorem grid_self {a : ℕ} (ha : 0 < a) : grid a a = 1 := by
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  simp [grid, ha0]

private theorem grid_step {a k : ℕ} (ha : 0 < a) :
    grid a (k + 1) - grid a k = (a : ℝ)⁻¹ := by
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  simp only [grid, Nat.cast_add, Nat.cast_one]
  rw [inv_eq_one_div]
  field_simp
  ring

private theorem grid_mono {a k : ℕ} (ha : 0 < a) :
    grid a k ≤ grid a (k + 1) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  simp only [grid, div_le_div_iff_of_pos_right haR]
  exact_mod_cast Nat.le_succ k

private theorem grid_mem_unit {a k : ℕ} (ha : 0 < a) (hk : k ≤ a) :
    grid a k ∈ Icc (0 : ℝ) 1 := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  constructor
  · exact div_nonneg (Nat.cast_nonneg k) haR.le
  · rw [grid, div_le_one₀ haR]
    exact_mod_cast hk

/-- A monotone function lies below its right endpoint on every grid cell. -/
private theorem kernel_cell_integral_le {a k : ℕ} (ha : 0 < a) (hk : k < a) :
    (∫ x in grid a k..grid a (k + 1), kernel x) ≤
      (a : ℝ)⁻¹ * kernel (grid a (k + 1)) := by
  have hka : k + 1 ≤ a := Nat.succ_le_iff.mpr hk
  have hleft := grid_mem_unit ha (Nat.le_of_lt hk)
  have hright := grid_mem_unit ha hka
  have hle := grid_mono (k := k) ha
  have hint : IntervalIntegrable kernel volume (grid a k) (grid a (k + 1)) :=
    kernel_intervalIntegrable.mono_set (by
      rw [uIcc_of_le hle, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc hleft.1 hright.2)
  calc
    (∫ x in grid a k..grid a (k + 1), kernel x) ≤
        ∫ _x in grid a k..grid a (k + 1), kernel (grid a (k + 1)) := by
      apply intervalIntegral.integral_mono_on hle hint
        (intervalIntegrable_const)
      intro x hx
      exact kernel_monotoneOn
        ⟨hleft.1.trans hx.1, hx.2.trans hright.2⟩ hright hx.2
    _ = (a : ℝ)⁻¹ * kernel (grid a (k + 1)) := by
      rw [intervalIntegral.integral_const, grid_step ha]
      simp [smul_eq_mul]

/-- The kernel integral is bounded by the composite right Riemann sum. -/
theorem kernelIntegral_le_rightSum {a : ℕ} (ha : 0 < a) :
    kernelIntegral ≤ (a : ℝ)⁻¹ *
      ∑ k ∈ Finset.range a, kernel (grid a (k + 1)) := by
  have hcells : ∀ k < a,
      IntervalIntegrable kernel volume (grid a k) (grid a (k + 1)) := by
    intro k hk
    have hleft := grid_mem_unit ha (Nat.le_of_lt hk)
    have hright := grid_mem_unit ha (Nat.succ_le_iff.mpr hk)
    exact kernel_intervalIntegrable.mono_set (by
      rw [uIcc_of_le (grid_mono (k := k) ha),
        uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc hleft.1 hright.2)
  rw [kernelIntegral, ← grid_zero a, ← grid_self ha,
    ← intervalIntegral.sum_integral_adjacent_intervals hcells]
  calc
    ∑ k ∈ Finset.range a, ∫ x in grid a k..grid a (k + 1), kernel x ≤
        ∑ k ∈ Finset.range a,
          (a : ℝ)⁻¹ * kernel (grid a (k + 1)) := by
      exact Finset.sum_le_sum fun k hk =>
        kernel_cell_integral_le ha (Finset.mem_range.mp hk)
    _ = (a : ℝ)⁻¹ * ∑ k ∈ Finset.range a,
        kernel (grid a (k + 1)) := by rw [Finset.mul_sum]

private theorem rightSum_eq {a : ℕ} (ha : 0 < a) :
    (∑ k ∈ Finset.range a, kernel (grid a (k + 1))) = C a + 2 * alpha := by
  calc
    (∑ k ∈ Finset.range a, kernel (grid a (k + 1))) =
        ∑ j ∈ Finset.Ico 1 (a + 1), kernel ((j : ℝ) / (a : ℝ)) := by
      rw [Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k _hk
      congr 1
      simp [grid, Nat.cast_add, add_comm]
    _ = C a + kernel ((a : ℝ) / (a : ℝ)) := by
      rw [Finset.sum_Ico_succ_top (show 1 ≤ a from ha)]
      rfl
    _ = C a + 2 * alpha := by
      have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
      rw [div_self ha0, kernel_one]

/-- The right-sum error is at most the endpoint contribution `alpha / a`. -/
theorem kernelIntegral_le_trapezoid_add {a : ℕ} (ha : 0 < a) :
    kernelIntegral ≤ trapezoid a + alpha / (a : ℝ) := by
  have h := kernelIntegral_le_rightSum ha
  rw [rightSum_eq ha] at h
  rw [trapezoid]
  calc
    kernelIntegral ≤ (a : ℝ)⁻¹ * (C a + 2 * alpha) := h
    _ = (C a + alpha) / (a : ℝ) + alpha / (a : ℝ) := by ring

/-- The composite trapezoidal approximations converge to the kernel integral. -/
theorem tendsto_trapezoid_succ :
    Tendsto (fun n : ℕ => trapezoid (n + 1)) atTop (𝓝 kernelIntegral) := by
  have hden : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have herr : Tendsto (fun n : ℕ => alpha / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hdiff : Tendsto
      (fun n : ℕ => kernelIntegral - trapezoid (n + 1)) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact sub_nonneg.mpr (trapezoid_le_kernelIntegral (by omega))
    · intro n
      have hupper := kernelIntegral_le_trapezoid_add (a := n + 1) (by omega)
      norm_num [Nat.cast_add] at hupper ⊢
      linarith
    · exact herr
  have hconst : Tendsto (fun _ : ℕ => kernelIntegral) atTop (𝓝 kernelIntegral) :=
    tendsto_const_nhds
  simpa only [sub_zero, sub_sub_cancel] using hconst.sub hdiff

/-- Equivalently, the normalized interior kernel sum converges to its integral. -/
theorem tendsto_C_div_succ :
    Tendsto (fun n : ℕ => C (n + 1) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 kernelIntegral) := by
  have hden : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have herr : Tendsto (fun n : ℕ => alpha / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have h := tendsto_trapezoid_succ.sub herr
  have heq : (fun n : ℕ => C (n + 1) / ((n + 1 : ℕ) : ℝ)) =
      fun n => trapezoid (n + 1) - alpha / ((n : ℝ) + 1) := by
    funext n
    rw [trapezoid]
    norm_num [Nat.cast_add]
    ring
  rw [heq]
  simpa only [sub_zero] using h

private noncomputable def spectralLower (a : ℕ) : ℝ :=
  Real.log (a : ℝ)⁻¹ +
    ((a - 1 : ℕ) : ℝ) * Real.log ((alpha / 2) / (a : ℝ))

/-- On the relevant compact interval, `tanh z` is bounded below by `z/2`. -/
private theorem half_le_tanh {z : ℝ} (hz0 : 0 ≤ z) (hzalpha : z ≤ alpha) :
    z / 2 ≤ Real.tanh z := by
  have habs : |z| ≤ |alpha| := by
    rw [abs_of_nonneg hz0, abs_of_pos alpha_pos]
    exact hzalpha
  have hcoshAlpha : Real.cosh alpha = Real.sqrt 2 := by
    rw [alpha, Real.cosh_arsinh]
    norm_num
  have hsqrt : Real.sqrt 2 ≤ (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hcosh : Real.cosh z ≤ 2 :=
    (Real.cosh_le_cosh.mpr habs).trans (by rw [hcoshAlpha]; exact hsqrt)
  have hsinh : z ≤ Real.sinh z := Real.self_le_sinh_iff.mpr hz0
  rw [Real.tanh_eq_sinh_div_cosh, le_div_iff₀ (Real.cosh_pos z)]
  nlinarith

private theorem tanh_kernel_lower {a j : ℕ} (ha : 0 < a)
    (hj : j ∈ Finset.Ico 1 a) :
    (alpha / 2) / (a : ℝ) ≤
      Real.tanh (kernel ((j : ℝ) / (a : ℝ)) / 2) := by
  rw [Finset.mem_Ico] at hj
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj.1
  have hratio0 : (0 : ℝ) ≤ (j : ℝ) / (a : ℝ) := by positivity
  have hratio1 : (j : ℝ) / (a : ℝ) ≤ 1 := by
    rw [div_le_one₀ haR]
    exact_mod_cast Nat.le_of_lt hj.2
  have hk0 : 0 ≤ kernel ((j : ℝ) / (a : ℝ)) := kernel_nonneg _
  have hkUpper := kernel_le_two_alpha hratio0 hratio1
  have htanh := half_le_tanh (z := kernel ((j : ℝ) / (a : ℝ)) / 2)
    (div_nonneg hk0 (by norm_num)) (by linarith)
  have hkLower := kernel_chord_lower_real hratio0 hratio1
  have hjScale : alpha / (a : ℝ) ≤
      alpha * ((j : ℝ) / (a : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hjR alpha_pos.le
    calc
      alpha / (a : ℝ) = alpha * 1 / (a : ℝ) := by ring
      _ ≤ alpha * (j : ℝ) / (a : ℝ) :=
        (div_le_div_iff_of_pos_right haR).mpr (by simpa using this)
      _ = alpha * ((j : ℝ) / (a : ℝ)) := by ring
  have hkScaled : 2 * (alpha / (a : ℝ)) ≤
      kernel ((j : ℝ) / (a : ℝ)) := by
    nlinarith [hjScale, hkLower]
  calc
    (alpha / 2) / (a : ℝ) ≤
        (kernel ((j : ℝ) / (a : ℝ)) / 2) / 2 := by
      calc
        (alpha / 2) / (a : ℝ) = (2 * (alpha / (a : ℝ))) / 4 := by ring
        _ ≤ kernel ((j : ℝ) / (a : ℝ)) / 4 := by
          exact div_le_div_of_nonneg_right hkScaled (by norm_num)
        _ = (kernel ((j : ℝ) / (a : ℝ)) / 2) / 2 := by ring
    _ ≤ Real.tanh (kernel ((j : ℝ) / (a : ℝ)) / 2) := htanh

private theorem spectralBase_lower {a : ℕ} (ha : 0 < a) :
    spectralLower a ≤ spectralBase a := by
  have hsum : ((a - 1 : ℕ) : ℝ) * Real.log ((alpha / 2) / (a : ℝ)) ≤
      ∑ j ∈ Finset.Ico 1 a,
        Real.log (Real.tanh (kernel ((j : ℝ) / (a : ℝ)) / 2)) := by
    calc
      ((a - 1 : ℕ) : ℝ) * Real.log ((alpha / 2) / (a : ℝ)) =
          ∑ _j ∈ Finset.Ico 1 a, Real.log ((alpha / 2) / (a : ℝ)) := by
        simp [Nat.card_Ico, Nat.cast_sub (show 1 ≤ a from ha)]
      _ ≤ ∑ j ∈ Finset.Ico 1 a,
          Real.log (Real.tanh (kernel ((j : ℝ) / (a : ℝ)) / 2)) := by
        apply Finset.sum_le_sum
        intro j hj
        apply Real.log_le_log
        · exact div_pos (div_pos alpha_pos (by norm_num)) (by exact_mod_cast ha)
        · exact tanh_kernel_lower ha hj
  rw [spectralLower, spectralBase]
  exact add_le_add le_rfl hsum

private theorem spectralBase_nonpos {a : ℕ} (ha : 0 < a) :
    spectralBase a ≤ 0 := by
  have haOne : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hfirst : Real.log (a : ℝ)⁻¹ ≤ 0 := by
    rw [Real.log_inv]
    linarith [Real.log_nonneg haOne]
  have hsum : (∑ j ∈ Finset.Ico 1 a,
      Real.log (Real.tanh (kernel ((j : ℝ) / (a : ℝ)) / 2))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    have hpos := Product.tanh_half_pos (Product.kernel_pos_of_mem_Ico ha hj)
    exact Real.log_nonpos hpos.le (Real.tanh_lt_one _).le
  rw [spectralBase]
  linarith

private theorem tendsto_spectralLower_div_sq :
    Tendsto (fun n : ℕ =>
      spectralLower (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2)) atTop (𝓝 0) := by
  let c : ℝ := alpha / 2
  have hc : c ≠ 0 := ne_of_gt (div_pos alpha_pos (by norm_num))
  have hden : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    hden.inv_tendsto_atTop
  have hcdiv : Tendsto (fun n : ℕ => Real.log c / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    hden.const_div_atTop _
  have hlogdiv : Tendsto
      (fun n : ℕ => Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1))
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hden
  have hlimit := hcdiv.sub (hcdiv.mul hinv) |>.sub hlogdiv
  have heq : (fun n : ℕ =>
      spectralLower (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2)) =
      fun n : ℕ => Real.log c / ((n : ℝ) + 1) -
        (Real.log c / ((n : ℝ) + 1)) * (((n : ℝ) + 1)⁻¹) -
        Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1) := by
    funext n
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp only [spectralLower, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
      Real.log_inv, c]
    rw [Real.log_div hc hn]
    field_simp
    ring
  rw [heq]
  simpa only [zero_mul, sub_zero, zero_sub, neg_zero] using hlimit

/-- The one-dimensional endpoint factor is lower order than the square area. -/
theorem tendsto_spectralBase_div_sq :
    Tendsto (fun n : ℕ =>
      spectralBase (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2)) atTop (𝓝 0) := by
  have hnegLower := tendsto_spectralLower_div_sq.neg
  have hneg : Tendsto (fun n : ℕ =>
      -(spectralBase (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2))) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      have hbase := spectralBase_nonpos (a := n + 1) (by omega)
      exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hbase (by positivity))
    · intro n
      have hlower := spectralBase_lower (a := n + 1) (by omega)
      have hsq : (0 : ℝ) < (((n + 1 : ℕ) : ℝ) ^ 2) := by positivity
      exact neg_le_neg ((div_le_div_iff_of_pos_right hsq).mpr hlower)
    · simpa only [neg_zero] using hnegLower
  have := hneg.neg
  simpa only [neg_zero, neg_neg] using this

/-- All concrete residual estimates, constructed from the exact product and
the proved quadrature formula.  The sole argument is Matrix--Tree. -/
private noncomputable def bulkInputs
    (hMatrixTree : RectangleCofactorInput) : Concrete.Inputs kernelIntegral :=
  (((ProductInputs.determinantalInputs hMatrixTree
      (Spectral.rectangularSpectralCofactor hMatrixTree)).toKernelInputs
        SharpTrapezoid.sharpTrapezoidFormula).toConcreteInputs)

/-- The exponentially decaying product correction is negligible per unit area. -/
theorem tendsto_residualPotential_div_sq
    (hMatrixTree : RectangleCofactorInput) :
    Tendsto (fun n : ℕ => residualPotential (n + 1) (n + 1) /
      (((n + 1 : ℕ) : ℝ) ^ 2)) atTop (𝓝 0) := by
  let h := bulkInputs hMatrixTree
  have hden : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    hden.inv_tendsto_atTop
  have hbound : Tendsto (fun n : ℕ => ((1 : ℝ) / 32) *
      (((n : ℝ) + 1)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      (hinv.pow 2).const_mul ((1 : ℝ) / 32)
  have hneg : Tendsto (fun n : ℕ =>
      -(residualPotential (n + 1) (n + 1) /
        (((n + 1 : ℕ) : ℝ) ^ 2))) atTop (𝓝 0) := by
    apply squeeze_zero (g := fun n : ℕ => ((1 : ℝ) / 32) *
      (((n : ℝ) + 1)⁻¹) ^ 2)
    · intro n
      have htop := h.potential_nonpos (a := n + 1) (t := n + 1) (by omega) (by omega)
      exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg htop (by positivity))
    · intro n
      have hbottom := h.negativePotential_lt_q_fraction
        (a := n + 1) (t := n + 1) (by omega) le_rfl
      rw [q_fraction] at hbottom
      have hsq : (0 : ℝ) < (((n + 1 : ℕ) : ℝ) ^ 2) := by positivity
      calc
        -(residualPotential (n + 1) (n + 1) /
            (((n + 1 : ℕ) : ℝ) ^ 2)) =
            -residualPotential (n + 1) (n + 1) /
              (((n + 1 : ℕ) : ℝ) ^ 2) := by ring
        _ ≤ ((1 : ℝ) / 32) / (((n + 1 : ℕ) : ℝ) ^ 2) :=
          (div_le_div_iff_of_pos_right hsq).mpr hbottom.le
        _ = ((1 : ℝ) / 32) * (((n : ℝ) + 1)⁻¹) ^ 2 := by
          norm_num [Nat.cast_add]
          field_simp
    · exact hbound
  have := hneg.neg
  simpa only [neg_zero, neg_neg] using this

/-- Exact per-area decomposition of the square rectangular product. -/
theorem log_tauRect_square_decomposition
    (hMatrixTree : RectangleCofactorInput) (n : ℕ) :
    Real.log (tauRect (n + 1) (n + 1) : ℝ) /
        (((n + 1 : ℕ) : ℝ) ^ 2) =
      spectralBase (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2) +
      C (n + 1) / ((n + 1 : ℕ) : ℝ) +
      residualPotential (n + 1) (n + 1) /
        (((n + 1 : ℕ) : ℝ) ^ 2) := by
  have ha : 0 < n + 1 := by omega
  have hlog : Real.log (tauRect (n + 1) (n + 1) : ℝ) =
      Concrete.logProduct spectralBase (n + 1) (n + 1) := by
    calc
      Real.log (tauRect (n + 1) (n + 1) : ℝ) =
          Real.log (rectangularSpectralProduct (n + 1) (n + 1)) :=
        ProductInputs.log_tauRect_eq_spectral hMatrixTree
          (Spectral.rectangularSpectralCofactor hMatrixTree) ha ha
      _ = Concrete.logProduct spectralBase (n + 1) (n + 1) :=
        log_rectangularSpectralProduct ha ha
  rw [hlog, Concrete.logProduct]
  have hcast : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  field_simp

/-- The logarithmic spanning-tree density of square rectangles tends to the
square-lattice entropy.  Matrix--Tree is the only hypothesis. -/
theorem tendsto_log_tauRect_square_per_area
    (hMatrixTree : RectangleCofactorInput) :
    Tendsto (fun n : ℕ =>
      Real.log (tauRect (n + 1) (n + 1) : ℝ) /
        (((n + 1 : ℕ) : ℝ) ^ 2)) atTop (𝓝 squareLatticeEntropy) := by
  have hsum := (tendsto_spectralBase_div_sq.add tendsto_C_div_succ).add
    (tendsto_residualPotential_div_sq hMatrixTree)
  have hsum' : Tendsto (fun n : ℕ =>
      spectralBase (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2) +
      C (n + 1) / ((n + 1 : ℕ) : ℝ) +
      residualPotential (n + 1) (n + 1) /
        (((n + 1 : ℕ) : ℝ) ^ 2)) atTop (𝓝 kernelIntegral) := by
    simpa only [zero_add, add_zero] using hsum
  rw [← Entropy.kernelIntegral_eq_squareLatticeEntropy]
  exact hsum'.congr' (Eventually.of_forall fun n =>
    (log_tauRect_square_decomposition hMatrixTree n).symm)

/-- An epsilon-form consequence convenient for later finite-size arguments. -/
theorem eventually_abs_log_tauRect_square_per_area_sub_entropy_lt
    (hMatrixTree : RectangleCofactorInput) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n in atTop,
      |Real.log (tauRect (n + 1) (n + 1) : ℝ) /
          (((n + 1 : ℕ) : ℝ) ^ 2) - squareLatticeEntropy| < eps := by
  rcases Metric.tendsto_atTop.1
      (tendsto_log_tauRect_square_per_area hMatrixTree) eps heps with ⟨N, hN⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  simpa only [Real.dist_eq] using hN n hn

/-- A two-sided finite-size form of the bulk limit. -/
theorem eventually_log_tauRect_square_per_area_between
    (hMatrixTree : RectangleCofactorInput) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n in atTop,
      squareLatticeEntropy - eps <
          Real.log (tauRect (n + 1) (n + 1) : ℝ) /
            (((n + 1 : ℕ) : ℝ) ^ 2) ∧
      Real.log (tauRect (n + 1) (n + 1) : ℝ) /
            (((n + 1 : ℕ) : ℝ) ^ 2) <
          squareLatticeEntropy + eps := by
  filter_upwards
      [eventually_abs_log_tauRect_square_per_area_sub_entropy_lt hMatrixTree heps]
      with n hn
  rw [abs_lt] at hn
  constructor <;> linarith

end

end SquareMaximality.Rectangle.Bulk
