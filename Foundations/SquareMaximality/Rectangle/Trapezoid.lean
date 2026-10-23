module

public import SquareMaximality.Rectangle.Kernel
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

@[expose] public section

set_option autoImplicit false

/-!
# The sharp trapezoidal error for the rectangular kernel

This file formalizes the quadrature layer behind equations `trap-identity`
and `C-trapezoidal` of the manuscript.  The elementary concavity argument is
kept separate from the special Fourier/logarithmic identity: concavity proves
that the concrete trapezoidal error is nonnegative, whereas its scaled
antitonicity uses the sharper logarithmic correction formula.
-/

namespace SquareMaximality.Rectangle.Trapezoid

open Set
open scoped Interval
open MeasureTheory
open Concrete Kernel

/-- The normalized integral of the concrete kernel. -/
noncomputable def kernelIntegral : ℝ :=
  ∫ x in (0 : ℝ)..1, kernel x

/-- The half-weighted composite trapezoidal sum from `eq:trap-identity`. -/
noncomputable def trapezoid (a : ℕ) : ℝ :=
  (C a + alpha) / (a : ℝ)

/-- `arsinh` is concave on the nonnegative unit interval. -/
theorem arsinh_concaveOn : ConcaveOn ℝ (Icc (0 : ℝ) 1) Real.arsinh := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc 0 1)
    Real.continuous_arsinh.continuousOn
    Real.differentiable_arsinh.differentiableOn
  intro x hx y hy hxy
  rw [(Real.hasDerivAt_arsinh x).deriv, (Real.hasDerivAt_arsinh y).deriv]
  have hsq : 1 + x ^ 2 ≤ 1 + y ^ 2 := by
    rw [interior_Icc, mem_Ioo] at hx hy
    nlinarith
  have hsqrt : Real.sqrt (1 + x ^ 2) ≤ Real.sqrt (1 + y ^ 2) :=
    Real.sqrt_le_sqrt hsq
  exact (inv_le_inv₀ (by positivity : 0 < Real.sqrt (1 + y ^ 2))
    (by positivity : 0 < Real.sqrt (1 + x ^ 2))).2 hsqrt

/-- The sine half-wave used to express the kernel without `arcosh`. -/
noncomputable def halfSine (x : ℝ) : ℝ :=
  Real.sin ((Real.pi / 2) * x)

theorem halfSine_mem_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    halfSine x ∈ Icc (0 : ℝ) 1 := by
  have hu0 : 0 ≤ (Real.pi / 2) * x :=
    mul_nonneg (div_nonneg Real.pi_pos.le (by norm_num)) hx.1
  have huπ : (Real.pi / 2) * x ≤ Real.pi := by
    nlinarith [Real.pi_pos, hx.2]
  exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi hu0 huπ, Real.sin_le_one _⟩

/-- Concavity of the sine half-wave on `[0,1]`. -/
theorem halfSine_concaveOn : ConcaveOn ℝ (Icc (0 : ℝ) 1) halfSine := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hux : (Real.pi / 2) * x ∈ Icc (0 : ℝ) Real.pi := by
    constructor
    · exact mul_nonneg (div_nonneg Real.pi_pos.le (by norm_num)) hx.1
    · nlinarith [Real.pi_pos, hx.2]
  have huy : (Real.pi / 2) * y ∈ Icc (0 : ℝ) Real.pi := by
    constructor
    · exact mul_nonneg (div_nonneg Real.pi_pos.le (by norm_num)) hy.1
    · nlinarith [Real.pi_pos, hy.2]
  have h := strictConcaveOn_sin_Icc.concaveOn.2 hux huy ha hb hab
  have harg : a * ((Real.pi / 2) * x) + b * ((Real.pi / 2) * y) =
      (Real.pi / 2) * (a * x + b * y) := by ring
  simpa only [halfSine, smul_eq_mul, harg] using h

/-- Concavity of `arsinh (sin (πx/2))`, obtained by composing two
increasing concave functions on their concrete ranges. -/
theorem arsinh_halfSine_concaveOn :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun x => Real.arsinh (halfSine x)) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxm := halfSine_mem_Icc hx
  have hym := halfSine_mem_Icc hy
  have hcombo : a * halfSine x + b * halfSine y ∈ Icc (0 : ℝ) 1 :=
    (convex_Icc (0 : ℝ) 1) hxm hym ha hb hab
  have harsinh := arsinh_concaveOn.2 hxm hym ha hb hab
  have hsin := halfSine_concaveOn.2 hx hy ha hb hab
  exact harsinh.trans (Real.arsinh_strictMono.monotone hsin)

/-- On `[0,1]`, the arcosh/cos kernel is exactly
`2 * arsinh (sin (πx/2))`. -/
theorem kernel_eq_two_mul_arsinh_halfSine {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    kernel x = 2 * Real.arsinh (halfSine x) := by
  have hs := halfSine_mem_Icc hx
  have hrhs : 0 ≤ 2 * Real.arsinh (halfSine x) :=
    mul_nonneg (by norm_num) (Real.arsinh_nonneg_iff.2 hs.1)
  have hcos : Real.cos (Real.pi * x) = 1 - 2 * halfSine x ^ 2 := by
    rw [show Real.pi * x = 2 * ((Real.pi / 2) * x) by ring, Real.cos_two_mul]
    simp only [halfSine]
    nlinarith [Real.sin_sq ((Real.pi / 2) * x)]
  have hcosh : Real.cosh (2 * Real.arsinh (halfSine x)) =
      1 + 2 * halfSine x ^ 2 := by
    rw [Real.cosh_two_mul, Real.sinh_arsinh]
    have hfund : Real.cosh (Real.arsinh (halfSine x)) ^ 2 - halfSine x ^ 2 = 1 := by
      simpa only [Real.sinh_arsinh] using
        Real.cosh_sq_sub_sinh_sq (Real.arsinh (halfSine x))
    linarith
  calc
    kernel x = Real.arcosh (2 - Real.cos (Real.pi * x)) := rfl
    _ = Real.arcosh (Real.cosh (2 * Real.arsinh (halfSine x))) := by
      rw [hcosh, hcos]
      congr 1
      ring
    _ = 2 * Real.arsinh (halfSine x) := Real.arcosh_cosh hrhs

/-- The actual kernel is concave on the whole quadrature interval. -/
theorem kernel_concaveOn : ConcaveOn ℝ (Icc (0 : ℝ) 1) kernel := by
  have hscaled : ConcaveOn ℝ (Icc (0 : ℝ) 1)
      (fun x => 2 * Real.arsinh (halfSine x)) := by
    simpa only [smul_eq_mul] using
      (ConcaveOn.smul (show (0 : ℝ) ≤ 2 by norm_num) arsinh_halfSine_concaveOn)
  exact hscaled.congr fun x hx => (kernel_eq_two_mul_arsinh_halfSine hx).symm

/-- Continuity, hence interval integrability, of the concrete kernel. -/
theorem kernel_intervalIntegrable : IntervalIntegrable kernel volume (0 : ℝ) 1 := by
  have hcont : Continuous (fun x : ℝ => 2 * Real.arsinh (halfSine x)) := by
    change Continuous
      ((fun _ : ℝ => (2 : ℝ)) *
        (Real.arsinh ∘ Real.sin ∘ ((fun _ : ℝ => Real.pi / 2) * id)))
    exact continuous_const.mul (Real.continuous_arsinh.comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)))
  apply (hcont.intervalIntegrable 0 1).congr
  intro x hx
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  exact (kernel_eq_two_mul_arsinh_halfSine ⟨hx.1.le, hx.2⟩).symm

/-- A single secant trapezoid lies below the integral of a concave function. -/
theorem one_trapezoid_le_integral {f : ℝ → ℝ} {u v : ℝ} (huv : u < v)
    (hconc : ConcaveOn ℝ (Icc u v) f)
    (hint : IntervalIntegrable f volume u v) :
    trapezoidal_integral f 1 u v ≤ ∫ x in u..v, f x := by
  let chord : ℝ → ℝ := fun x =>
    ((v - x) / (v - u)) * f u + ((x - u) / (v - u)) * f v
  have hchord : ∀ x ∈ Icc u v, chord x ≤ f x := by
    intro x hx
    have hden : 0 < v - u := sub_pos.mpr huv
    have hleft : 0 ≤ (v - x) / (v - u) := div_nonneg (sub_nonneg.mpr hx.2) hden.le
    have hright : 0 ≤ (x - u) / (v - u) := div_nonneg (sub_nonneg.mpr hx.1) hden.le
    have hsum : (v - x) / (v - u) + (x - u) / (v - u) = 1 := by
      field_simp
      ring
    have h := hconc.2
      (show u ∈ Icc u v by exact ⟨le_rfl, huv.le⟩)
      (show v ∈ Icc u v by exact ⟨huv.le, le_rfl⟩)
      hleft hright hsum
    have hcombo : (v - x) / (v - u) * u + (x - u) / (v - u) * v = x := by
      field_simp
      ring
    simpa only [chord, smul_eq_mul, hcombo] using h
  have hchordInt : IntervalIntegrable chord volume u v := by
    apply Continuous.intervalIntegrable
    dsimp only [chord]
    fun_prop
  have hmono := intervalIntegral.integral_mono_on huv.le hchordInt hint hchord
  have hchordIntegral :
      (∫ x in u..v, chord x) = (v - u) / 2 * (f u + f v) := by
    have hden : v - u ≠ 0 := ne_of_gt (sub_pos.mpr huv)
    have hleftInt : IntervalIntegrable (fun x : ℝ => ((v - x) / (v - u)) * f u)
        volume u v := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hrightInt : IntervalIntegrable (fun x : ℝ => ((x - u) / (v - u)) * f v)
        volume u v := by
      apply Continuous.intervalIntegrable
      fun_prop
    dsimp only [chord]
    rw [intervalIntegral.integral_add hleftInt hrightInt]
    simp only [div_eq_mul_inv, mul_assoc, intervalIntegral.integral_mul_const]
    have hvSub : (∫ x in u..v, v - x) =
        (∫ _x in u..v, v) - ∫ x in u..v, x := by
      simpa only [id_eq] using
        (intervalIntegral.integral_sub (continuous_const.intervalIntegrable u v)
          (continuous_id.intervalIntegrable u v))
    have hSubu : (∫ x in u..v, x - u) =
        (∫ x in u..v, x) - ∫ _x in u..v, u := by
      simpa only [id_eq] using
        (intervalIntegral.integral_sub (continuous_id.intervalIntegrable u v)
          (continuous_const.intervalIntegrable u v))
    rw [hvSub, hSubu]
    simp only [intervalIntegral.integral_const, integral_id,
      smul_eq_mul]
    field_simp
    ring
  rw [trapezoidal_integral_one, ← hchordIntegral]
  exact hmono

/-- The manuscript's `T_a` is literally Mathlib's composite trapezoidal
integral for the concrete kernel. -/
theorem trapezoid_eq_trapezoidal_integral {a : ℕ} (ha : 0 < a) :
    trapezoid a = trapezoidal_integral kernel a 0 1 := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have hsum : C a = ∑ k ∈ Finset.range (a - 1),
      kernel ((k + 1 : ℕ) / (a : ℝ)) := by
    rw [C, Finset.sum_Ico_eq_sum_range]
    congr 1
    funext k
    congr 2
    norm_num [Nat.cast_add]
    ring
  have hsumStd : (∑ k ∈ Finset.range (a - 1),
      kernel ((k + 1 : ℕ) / (a : ℝ))) =
      ∑ k ∈ Finset.range (a - 1),
        kernel ((0 : ℝ) + ((k : ℝ) + 1) * (1 - 0) / (a : ℝ)) := by
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    norm_num [Nat.cast_add]
  rw [trapezoid, trapezoidal_integral, Kernel.kernel_zero, Kernel.kernel_one,
    hsum, hsumStd]
  norm_num
  ring

/-- The ordinary trapezoidal error is nonnegative for the actual kernel.
This is the unconditional concavity part of `lem:trap`. -/
theorem trapezoid_le_kernelIntegral {a : ℕ} (ha : 0 < a) :
    trapezoid a ≤ kernelIntegral := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  let step : ℝ := 1 / (a : ℝ)
  have hlast : (0 : ℝ) + (a : ℝ) * step = 1 := by
    dsimp only [step]
    field_simp
    ring
  have hgridInt : IntervalIntegrable kernel volume (0 : ℝ)
      (0 + (a : ℝ) * step) := by
    simpa only [hlast] using kernel_intervalIntegrable
  have hsumEq := sum_trapezoidal_error_adjacent_intervals ha hgridInt
  have hsumNonpos :
      (∑ i ∈ Finset.range a,
        trapezoidal_error kernel 1
          ((0 : ℝ) + (i : ℝ) * step)
          (0 + ((i : ℝ) + 1) * step)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    have hia : i < a := Finset.mem_range.mp hi
    let u : ℝ := (i : ℝ) * step
    let v : ℝ := ((i : ℝ) + 1) * step
    have hstep : 0 < step := by
      dsimp only [step]
      positivity
    have huv : u < v := by
      dsimp only [u, v]
      nlinarith
    have hu0 : 0 ≤ u := by
      dsimp only [u]
      positivity
    have hv1 : v ≤ 1 := by
      have hcast : (i : ℝ) + 1 ≤ (a : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt hia)
      have hast : (a : ℝ) * step = 1 := by linarith [hlast]
      calc
        v ≤ (a : ℝ) * step := by
          dsimp only [v]
          exact mul_le_mul_of_nonneg_right hcast hstep.le
        _ = 1 := hast
    have hu1 : u ≤ 1 := huv.le.trans hv1
    have hv0 : 0 ≤ v := hu0.trans huv.le
    have hsub : Icc u v ⊆ Icc (0 : ℝ) 1 :=
      Icc_subset_Icc hu0 hv1
    have hconc : ConcaveOn ℝ (Icc u v) kernel :=
      kernel_concaveOn.subset hsub (convex_Icc u v)
    have hlocalInt : IntervalIntegrable kernel volume u v :=
      kernel_intervalIntegrable.mono
        (uIcc_subset_uIcc (mem_uIcc_of_le hu0 hu1) (mem_uIcc_of_le hv0 hv1)) le_rfl
    have hlocal := one_trapezoid_le_integral huv hconc hlocalInt
    dsimp only [trapezoidal_error]
    dsimp only [u, v] at hlocal
    simpa only [zero_add] using sub_nonpos.mpr hlocal
  rw [hsumEq, hlast] at hsumNonpos
  rw [trapezoid_eq_trapezoidal_integral ha]
  exact sub_nonpos.mp hsumNonpos

/-- The first requested concrete error property, with the integral constant. -/
theorem epsilon_nonneg {a : ℕ} (ha : 0 < a) :
    0 ≤ epsilon kernelIntegral a := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have htrap := trapezoid_le_kernelIntegral ha
  rw [epsilon]
  rw [trapezoid, div_le_iff₀ haR] at htrap
  linarith

/-- The logarithmic correction per unit mesh size in `eq:trap-identity`. -/
noncomputable def scaledCorrection (p z : ℝ) : ℝ :=
  Real.log (1 - Real.exp ((-2 * z) * p)) / p

noncomputable def scaledCorrectionDeriv (p z : ℝ) : ℝ :=
  (((0 - Real.exp ((-2 * z) * p) * (-2 * z)) /
      (1 - Real.exp ((-2 * z) * p))) * p -
    Real.log (1 - Real.exp ((-2 * z) * p)) * 1) / p ^ 2

theorem hasDerivAt_scaledCorrection {p z : ℝ} (hp : 0 < p) (hz : 0 < z) :
    HasDerivAt (fun q => scaledCorrection q z) (scaledCorrectionDeriv p z) p := by
  have hlinear : HasDerivAt (fun q : ℝ => (-2 * z) * q) (-2 * z) p := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id p).const_mul (-2 * z)
  have hexp := hlinear.exp
  have hargpos : 0 < 1 - Real.exp ((-2 * z) * p) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    nlinarith
  have hlog := ((hasDerivAt_const p 1).sub hexp).log (ne_of_gt hargpos)
  have hquot := hlog.div (hasDerivAt_id p) hp.ne'
  convert hquot using 1 <;> rfl

theorem scaledCorrectionDeriv_pos {p z : ℝ} (hp : 0 < p) (hz : 0 < z) :
    0 < scaledCorrectionDeriv p z := by
  have hexpPos : 0 < Real.exp ((-2 * z) * p) := Real.exp_pos _
  have hexpLt : Real.exp ((-2 * z) * p) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hargpos : 0 < 1 - Real.exp ((-2 * z) * p) := sub_pos.mpr hexpLt
  have harglt : 1 - Real.exp ((-2 * z) * p) < 1 := by linarith
  have hlog : Real.log (1 - Real.exp ((-2 * z) * p)) < 0 :=
    Real.log_neg hargpos harglt
  have hnumerator : 0 < 0 - Real.exp ((-2 * z) * p) * (-2 * z) := by
    nlinarith [mul_pos hexpPos hz]
  have hfirst : 0 < ((0 - Real.exp ((-2 * z) * p) * (-2 * z)) /
      (1 - Real.exp ((-2 * z) * p))) * p := by positivity
  dsimp only [scaledCorrectionDeriv]
  exact div_pos (by linarith) (sq_pos_of_pos hp)

/-- For every positive kernel value, the normalized logarithmic correction
strictly increases with the mesh parameter. -/
theorem scaledCorrection_strictMonoOn {z : ℝ} (hz : 0 < z) :
    StrictMonoOn (fun p => scaledCorrection p z) (Ioi (0 : ℝ)) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioi 0)
  · intro p hp
    exact (hasDerivAt_scaledCorrection hp hz).continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Ioi] at hp
    exact (hasDerivAt_scaledCorrection hp hz).hasDerivWithinAt
  · intro p hp
    rw [interior_Ioi] at hp
    exact scaledCorrectionDeriv_pos hp hz

/-- Endpoint integrability of the logarithmic correction.  The replacement
`kernel x = 2*arsinh(sin(πx/2))` is analytic, so the logarithm is covered by
Mathlib's integrability theorem for real meromorphic functions. -/
theorem scaledCorrection_kernel_intervalIntegrable {a : ℕ} (_ : 0 < a) :
    IntervalIntegrable
      (fun x => scaledCorrection (a : ℝ) (kernel x)) volume (0 : ℝ) 1 := by
  let analyticArg : ℝ → ℝ := fun x =>
    1 - Real.exp ((-2 * (2 * Real.arsinh (halfSine x))) * (a : ℝ))
  have hargAnalytic : AnalyticOnNhd ℝ analyticArg (uIcc (0 : ℝ) 1) := by
    intro x hx
    dsimp only [analyticArg, halfSine]
    fun_prop
  have hlog : IntervalIntegrable (Real.log ∘ analyticArg) volume (0 : ℝ) 1 :=
    hargAnalytic.meromorphicOn.intervalIntegrable_log
  have hscaled : IntervalIntegrable
      (fun x => Real.log (analyticArg x) / (a : ℝ)) volume (0 : ℝ) 1 := by
    simpa only [Function.comp_apply, div_eq_mul_inv] using
      hlog.mul_const ((a : ℝ)⁻¹)
  apply hscaled.congr
  intro x hx
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  have hxmem : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  change Real.log (analyticArg x) / (a : ℝ) =
    Real.log (1 - Real.exp ((-2 * kernel x) * (a : ℝ))) / (a : ℝ)
  dsimp only [analyticArg]
  rw [kernel_eq_two_mul_arsinh_halfSine hxmem]

/-- The only upstream analytic package still needed for the sharp scaled
error monotonicity.  It is exactly the logarithmic correction formula
`eq:trap-identity`.  Endpoint integrability is proved above. -/
structure SharpTrapezoidFormula : Prop where
  formula : ∀ {a : ℕ}, 0 < a →
    trapezoid a = kernelIntegral +
      ∫ x in (0 : ℝ)..1, scaledCorrection (a : ℝ) (kernel x)

namespace SharpTrapezoidFormula

variable (h : SharpTrapezoidFormula)
include h

theorem identity {a : ℕ} (ha : 0 < a) :
    trapezoid a = kernelIntegral +
      ∫ x in (0 : ℝ)..1, scaledCorrection (a : ℝ) (kernel x) :=
  SharpTrapezoidFormula.formula h ha

theorem trapezoid_monotone {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    trapezoid a ≤ trapezoid b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hcorr :
      (∫ x in (0 : ℝ)..1, scaledCorrection (a : ℝ) (kernel x)) ≤
        ∫ x in (0 : ℝ)..1, scaledCorrection (b : ℝ) (kernel x) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
      (scaledCorrection_kernel_intervalIntegrable ha)
      (scaledCorrection_kernel_intervalIntegrable hb)
    intro x hx
    have hxmem : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    have hk : 0 < kernel x := by
      rw [← Kernel.kernel_zero]
      exact Kernel.kernel_strictMonoOn
        (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
        hxmem hx.1
    exact (scaledCorrection_strictMonoOn hk).monotoneOn haR hbR habR
  rw [identity h ha, identity h hb]
  linarith

/-- The second requested concrete error property, derived from the sharp
quadrature formula rather than leaving an error-field interface. -/
theorem epsilon_scaled_antitone {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    (a : ℝ) * epsilon kernelIntegral b ≤
      (b : ℝ) * epsilon kernelIntegral a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have htrap := trapezoid_monotone h ha hab
  change (C a + alpha) / (a : ℝ) ≤ (C b + alpha) / (b : ℝ) at htrap
  rw [div_le_div_iff₀ haR hbR] at htrap
  simp only [epsilon]
  nlinarith

end SharpTrapezoidFormula

/-- After the quadrature theorem, this modular rectangle layer takes the two
determinantal ingredients as fields: Matrix--Tree and the explicit rectangular
product formula.  Both are constructed downstream. -/
structure DeterminantalInputs where
  logDeterminant : ℕ → ℕ → ℝ
  base : ℕ → ℝ
  matrixTreeLog : ∀ {a t : ℕ}, 0 < a → 0 < t →
    Real.log (tauRect a t : ℝ) = logDeterminant a t
  rectangularProductLog : ∀ {a t : ℕ}, 0 < a → 0 < t →
    logDeterminant a t = Concrete.logProduct base a t

namespace DeterminantalInputs

variable (d : DeterminantalInputs)
include d

/-- Constructor for all rectangular analytic inputs.  No penalty estimate,
hyperbolic increment, residual bound, or epsilon property is an argument. -/
noncomputable def toKernelInputs (htrap : SharpTrapezoidFormula) :
    Kernel.Inputs kernelIntegral where
  logDeterminant := d.logDeterminant
  base := d.base
  matrixTreeLog := d.matrixTreeLog
  rectangularProductLog := d.rectangularProductLog
  epsilon_nonneg := epsilon_nonneg
  epsilon_scaled_antitone := SharpTrapezoidFormula.epsilon_scaled_antitone htrap

theorem strictRectangularAreaPenalty (htrap : SharpTrapezoidFormula) :
    StrictRectangularAreaPenalty kernelIntegral :=
  (toKernelInputs d htrap).strictRectangularAreaPenalty

theorem rectangularAreaPenalty (htrap : SharpTrapezoidFormula) :
    RectangularAreaPenalty kernelIntegral :=
  (toKernelInputs d htrap).rectangularAreaPenalty

/-- Transport to the manuscript's named entropy constant once its independent
Catalan-integral evaluation is supplied. -/
noncomputable def toSquareLatticeEntropyInputs (hentropy :
    kernelIntegral = squareLatticeEntropy) (htrap : SharpTrapezoidFormula) :
    Kernel.Inputs squareLatticeEntropy := by
  rw [← hentropy]
  exact toKernelInputs d htrap

end DeterminantalInputs

end SquareMaximality.Rectangle.Trapezoid
