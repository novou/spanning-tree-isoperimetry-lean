import SquareMaximality.Rectangle.Entropy
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

set_option autoImplicit false

/-!
# The exact sharp trapezoidal formula

This file proves the logarithmic correction identity `eq:trap-identity` from
the concrete arcosh/cos kernel.  The proof is organized around two exact
identities: Jensen's circle-average evaluation of the logarithmic potential,
and the finite Chebyshev product which implements the half-weighted
trapezoidal filter.  Endpoint equalities are used only under interval
integrals, where the isolated logarithmic zeros form null sets.
-/

namespace SquareMaximality.Rectangle.SharpTrapezoid

open Set MeasureTheory
open scoped Interval
open Concrete Kernel Trapezoid Entropy

namespace Chebyshev

open Polynomial Polynomial.Chebyshev

/-- Factorization of the real Chebyshev polynomial of the second kind by
its `n` simple cosine roots. -/
theorem eval_U_eq_cosine_product (n : ℕ) (x : ℝ) :
    (U ℝ n).eval x =
      2 ^ n * ∏ k ∈ Finset.range n,
        (x - Real.cos (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + 1))) := by
  let root : ℕ → ℝ := fun k =>
    Real.cos (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + 1))
  have hinj : Set.InjOn root (Finset.range n) := by
    exact (Finset.range n).nodup_map_iff_injOn.mp
      (Polynomial.Chebyshev.roots_U_real_nodup n)
  have hcard : (U ℝ n).roots.card = (U ℝ n).natDegree := by
    rw [Polynomial.Chebyshev.natDegree_U_natCast,
      Polynomial.Chebyshev.roots_U_real]
    change (Finset.image root (Finset.range n)).card = n
    rw [Finset.card_image_of_injOn, Finset.card_range]
    exact hinj
  have hsplit : (U ℝ n).Splits := Polynomial.splits_iff_card_roots.mpr hcard
  have heval := hsplit.eval_eq_prod_roots x
  rw [Polynomial.Chebyshev.leadingCoeff_U_natCast,
    Polynomial.Chebyshev.roots_U_real] at heval
  change (U ℝ n).eval x = 2 ^ n * ∏ k ∈ Finset.range n, (x - root k)
  rw [heval]
  change 2 ^ n * ∏ y ∈ Finset.image root (Finset.range n), (x - y) = _
  congr 1
  rw [Finset.prod_image]
  exact hinj

end Chebyshev

theorem two_mul_exp_neg_mul_sinh (z : ℝ) :
    2 * Real.exp (-z) * Real.sinh z = 1 - Real.exp (-2 * z) := by
  rw [Real.sinh_eq]
  calc
    2 * Real.exp (-z) * ((Real.exp z - Real.exp (-z)) / 2) =
        Real.exp (-z) * Real.exp z - Real.exp (-z) * Real.exp (-z) := by ring
    _ = 1 - Real.exp (-2 * z) := by
      rw [← Real.exp_add, ← Real.exp_add]
      ring_nf
      simp

theorem two_mul_exp_neg_mul_cosh_sub_cos (z t : ℝ) :
    2 * Real.exp (-z) * (Real.cosh z - Real.cos t) =
      1 - 2 * Real.exp (-z) * Real.cos t + Real.exp (-2 * z) := by
  rw [Real.cosh_eq]
  calc
    2 * Real.exp (-z) *
        ((Real.exp z + Real.exp (-z)) / 2 - Real.cos t) =
        Real.exp (-z) * Real.exp z + Real.exp (-z) * Real.exp (-z) -
          2 * Real.exp (-z) * Real.cos t := by ring
    _ = 1 - 2 * Real.exp (-z) * Real.cos t + Real.exp (-2 * z) := by
      rw [← Real.exp_add, ← Real.exp_add]
      ring_nf
      simp

/-- Algebraic form of the half-weighted trapezoidal filter.  It is the
finite Chebyshev product, and replaces any appeal to an unformalized Fourier
filter or uniform-convergence argument. -/
theorem chebyshev_filter_product (n : ℕ) (z : ℝ) :
    (1 - Real.exp (-2 * z)) *
        ∏ k ∈ Finset.range n,
          (1 - 2 * Real.exp (-z) *
              Real.cos (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + 1)) +
            Real.exp (-2 * z)) =
      1 - Real.exp (-2 * (((n : ℝ) + 1) * z)) := by
  let q : ℝ := Real.exp (-z)
  let root : ℕ → ℝ := fun k =>
    Real.cos (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + 1))
  have hfactor (k : ℕ) :
      1 - 2 * q * root k + Real.exp (-2 * z) =
        2 * q * (Real.cosh z - root k) := by
    dsimp only [q, root]
    exact (two_mul_exp_neg_mul_cosh_sub_cos z _).symm
  have hprod :
      (∏ k ∈ Finset.range n,
          (1 - 2 * q * root k + Real.exp (-2 * z))) =
        (2 * q) ^ n * ∏ k ∈ Finset.range n, (Real.cosh z - root k) := by
    calc
      (∏ k ∈ Finset.range n,
          (1 - 2 * q * root k + Real.exp (-2 * z))) =
          ∏ k ∈ Finset.range n, (2 * q) * (Real.cosh z - root k) := by
            apply Finset.prod_congr rfl
            intro k _hk
            exact hfactor k
      _ = (2 * q) ^ n * ∏ k ∈ Finset.range n, (Real.cosh z - root k) := by
            rw [Finset.prod_mul_distrib]
            simp
  have hcheb := Chebyshev.eval_U_eq_cosine_product n (Real.cosh z)
  change (Polynomial.Chebyshev.U ℝ n).eval (Real.cosh z) =
    2 ^ n * ∏ k ∈ Finset.range n, (Real.cosh z - root k) at hcheb
  have hU := Polynomial.Chebyshev.U_real_cosh z (n : ℤ)
  have hU' :
      (Polynomial.Chebyshev.U ℝ n).eval (Real.cosh z) * Real.sinh z =
        Real.sinh (((n : ℝ) + 1) * z) := by
    simpa only [Int.cast_natCast, Int.cast_add, Int.cast_one] using hU
  have hqpow : q ^ (n + 1) = Real.exp (-(((n : ℝ) + 1) * z)) := by
    dsimp only [q]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc
    (1 - Real.exp (-2 * z)) *
        ∏ k ∈ Finset.range n,
          (1 - 2 * Real.exp (-z) *
              Real.cos (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + 1)) +
            Real.exp (-2 * z)) =
        (2 * q * Real.sinh z) *
          ((2 * q) ^ n * ∏ k ∈ Finset.range n,
            (Real.cosh z - root k)) := by
              rw [two_mul_exp_neg_mul_sinh, hprod]
    _ = 2 * q ^ (n + 1) *
        ((2 ^ n * ∏ k ∈ Finset.range n, (Real.cosh z - root k)) *
          Real.sinh z) := by
            rw [mul_pow]
            ring
    _ = 2 * q ^ (n + 1) * Real.sinh (((n : ℝ) + 1) * z) := by
          rw [← hcheb, hU']
    _ = 2 * Real.exp (-(((n : ℝ) + 1) * z)) *
        Real.sinh (((n : ℝ) + 1) * z) := by rw [hqpow]
    _ = 1 - Real.exp (-2 * (((n : ℝ) + 1) * z)) :=
      two_mul_exp_neg_mul_sinh (((n : ℝ) + 1) * z)

/-- The logarithmic half-grid sum with `n` interior Chebyshev nodes. -/
noncomputable def halfGridLogSum (n : ℕ) (z : ℝ) : ℝ :=
  (Real.log (Real.cosh z - 1) + Real.log (Real.cosh z + 1)) / 2 +
    ∑ k ∈ Finset.range n,
      Real.log (Real.cosh z -
        Real.cos (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + 1)))

theorem endpoint_halfLog_eq_log_sinh {z : ℝ} (hz : 0 < z) :
    (Real.log (Real.cosh z - 1) + Real.log (Real.cosh z + 1)) / 2 =
      Real.log (Real.sinh z) := by
  have hc : 1 < Real.cosh z := Real.one_lt_cosh.mpr (ne_of_gt hz)
  have hm : Real.cosh z - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hc)
  have hp : Real.cosh z + 1 ≠ 0 := ne_of_gt (by linarith)
  have hs : Real.sinh z ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hz)
  calc
    (Real.log (Real.cosh z - 1) + Real.log (Real.cosh z + 1)) / 2 =
        Real.log ((Real.cosh z - 1) * (Real.cosh z + 1)) / 2 := by
          rw [Real.log_mul hm hp]
    _ = Real.log (Real.sinh z ^ 2) / 2 := by
          congr 2
          nlinarith [Real.cosh_sq_sub_sinh_sq z]
    _ = Real.log (Real.sinh z) := by
          rw [pow_two, Real.log_mul hs hs]
          ring

/-- Exact logarithmic form of the Chebyshev/trapezoidal filter. -/
theorem halfGridLogSum_eq (n : ℕ) {z : ℝ} (hz : 0 < z) :
    halfGridLogSum n z =
      ((n : ℝ) + 1) * (z - Real.log 2) +
        Real.log (1 - Real.exp (-2 * (((n : ℝ) + 1) * z))) := by
  let root : ℕ → ℝ := fun k =>
    Real.cos (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + 1))
  let P : ℝ := ∏ k ∈ Finset.range n, (Real.cosh z - root k)
  have hc : 1 < Real.cosh z := Real.one_lt_cosh.mpr (ne_of_gt hz)
  have hrootPos : ∀ k ∈ Finset.range n, 0 < Real.cosh z - root k := by
    intro k _hk
    dsimp only [root]
    have hcos := Real.cos_le_one
      (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + 1))
    linarith
  have hPpos : 0 < P := by
    dsimp only [P]
    exact Finset.prod_pos fun k hk => hrootPos k hk
  have hspos : 0 < Real.sinh z := Real.sinh_pos_iff.mpr hz
  have hsumLog :
      (∑ k ∈ Finset.range n, Real.log (Real.cosh z - root k)) = Real.log P := by
    dsimp only [P]
    rw [Real.log_prod]
    intro k hk
    exact ne_of_gt (hrootPos k hk)
  have hcheb := Chebyshev.eval_U_eq_cosine_product n (Real.cosh z)
  change (Polynomial.Chebyshev.U ℝ n).eval (Real.cosh z) = 2 ^ n * P at hcheb
  have hU := Polynomial.Chebyshev.U_real_cosh z (n : ℤ)
  have hU' :
      (Polynomial.Chebyshev.U ℝ n).eval (Real.cosh z) * Real.sinh z =
        Real.sinh (((n : ℝ) + 1) * z) := by
    simpa only [Int.cast_natCast, Int.cast_add, Int.cast_one] using hU
  have hprodSinh : Real.sinh z * P =
      Real.sinh (((n : ℝ) + 1) * z) / 2 ^ n := by
    rw [hcheb] at hU'
    have htwo : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp [htwo]
    nlinarith
  let w : ℝ := ((n : ℝ) + 1) * z
  have hw : 0 < w := by dsimp only [w]; positivity
  have hcorr : 0 < 1 - Real.exp (-2 * w) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    nlinarith
  have hsinhW : Real.sinh w =
      Real.exp w * (1 - Real.exp (-2 * w)) / 2 := by
    have h := two_mul_exp_neg_mul_sinh w
    have hew : Real.exp w * Real.exp (-w) = 1 := by
      rw [← Real.exp_add]
      simp
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
    rw [← h]
    calc
      Real.sinh w * 2 =
          2 * (Real.exp w * Real.exp (-w)) * Real.sinh w := by rw [hew]; ring
      _ = Real.exp w * (2 * Real.exp (-w) * Real.sinh w) := by ring
  have hcombined : Real.sinh z * P =
      Real.exp w * (1 - Real.exp (-2 * w)) / 2 ^ (n + 1) := by
    rw [hprodSinh]
    change Real.sinh w / 2 ^ n = _
    rw [hsinhW, pow_succ]
    ring
  have hlogCombined : Real.log (Real.sinh z * P) =
      ((n : ℝ) + 1) * (z - Real.log 2) +
        Real.log (1 - Real.exp (-2 * w)) := by
    have hnum : Real.exp w * (1 - Real.exp (-2 * w)) ≠ 0 :=
      mul_ne_zero (ne_of_gt (Real.exp_pos w)) (ne_of_gt hcorr)
    have hden : (2 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [hcombined, Real.log_div hnum hden,
      Real.log_mul (ne_of_gt (Real.exp_pos w))
      (ne_of_gt hcorr), Real.log_exp, Real.log_pow]
    dsimp only [w]
    push_cast
    ring
  rw [halfGridLogSum, endpoint_halfLog_eq_log_sinh hz]
  change Real.log (Real.sinh z) +
    ∑ k ∈ Finset.range n, Real.log (Real.cosh z - root k) = _
  rw [hsumLog, ← Real.log_mul (ne_of_gt hspos) (ne_of_gt hPpos), hlogCombined]

/-- Jensen's circle-average theorem specialized to a positive real point
outside the unit circle. -/
theorem integral_logNorm_circle_sub_exp {z : ℝ} (hz : 0 < z) :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
        Real.log ‖circleMap 0 1 φ - (Real.exp z : ℂ)‖) =
      2 * Real.pi * z := by
  have hcircle :=
    circleAverage_log_norm_sub_const_eq_posLog
      (a := (Real.exp z : ℂ))
  have hnorm : ‖(Real.exp z : ℂ)‖ = Real.exp z := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos z)]
  have hone : 1 ≤ Real.exp z := Real.one_le_exp hz.le
  have habs : 1 ≤ |Real.exp z| := by
    rwa [abs_of_pos (Real.exp_pos z)]
  rw [Real.circleAverage_def, hnorm, Real.posLog_eq_log habs,
    Real.log_exp] at hcircle
  change (2 * Real.pi)⁻¹ *
    (∫ φ in (0 : ℝ)..2 * Real.pi,
      Real.log ‖circleMap 0 1 φ - (Real.exp z : ℂ)‖) = z at hcircle
  have htwoPi : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  field_simp [htwoPi] at hcircle
  nlinarith

theorem norm_circle_sub_exp_sq (z φ : ℝ) :
    ‖circleMap 0 1 φ - (Real.exp z : ℂ)‖ ^ 2 =
      2 * Real.exp z * (Real.cosh z - Real.cos φ) := by
  calc
    ‖circleMap 0 1 φ - (Real.exp z : ℂ)‖ ^ 2 =
        Complex.normSq (circleMap 0 1 φ - (Real.exp z : ℂ)) :=
      Complex.sq_norm _
    _ = (Real.cos φ - Real.exp z) ^ 2 + Real.sin φ ^ 2 := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        circleMap_zero_re, circleMap_zero_im, Complex.ofReal_re,
        Complex.ofReal_im, one_mul, sub_zero, pow_two]
    _ = 1 + Real.exp (2 * z) - 2 * Real.exp z * Real.cos φ := by
      have hexpSq : Real.exp z ^ 2 = Real.exp (2 * z) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      nlinarith [Real.sin_sq φ, hexpSq]
    _ = 2 * Real.exp z * (Real.cosh z - Real.cos φ) := by
      rw [Real.cosh_eq]
      have hcancel : Real.exp z * Real.exp (-z) = 1 := by
        rw [← Real.exp_add]
        simp
      have hsquare : Real.exp z * Real.exp z = Real.exp (2 * z) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [mul_sub]
      field_simp
      nlinarith

/-- Pointwise logarithmic-potential identity underlying the kernel
representation. -/
theorem log_cosh_sub_cos_eq {z : ℝ} (hz : 0 < z) (φ : ℝ) :
    Real.log (Real.cosh z - Real.cos φ) =
      2 * Real.log ‖circleMap 0 1 φ - (Real.exp z : ℂ)‖ -
        Real.log 2 - z := by
  let d : ℝ := ‖circleMap 0 1 φ - (Real.exp z : ℂ)‖
  let b : ℝ := Real.cosh z - Real.cos φ
  have hc : 1 < Real.cosh z := Real.one_lt_cosh.mpr (ne_of_gt hz)
  have hb : 0 < b := by
    dsimp only [b]
    linarith [Real.cos_le_one φ]
  have hdSq : d ^ 2 = 2 * Real.exp z * b := by
    simpa only [d, b] using norm_circle_sub_exp_sq z φ
  have hd : 0 < d := by
    have hrhs : 0 < 2 * Real.exp z * b := by positivity
    have hdnonneg : 0 ≤ d := by dsimp only [d]; positivity
    nlinarith
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have he : Real.exp z ≠ 0 := ne_of_gt (Real.exp_pos z)
  have hbne : b ≠ 0 := ne_of_gt hb
  have hlogs := congr_arg Real.log hdSq
  rw [Real.log_pow, Real.log_mul (mul_ne_zero htwo he) hbne,
    Real.log_mul htwo he, Real.log_exp] at hlogs
  change Real.log b = 2 * Real.log d - Real.log 2 - z
  linear_combination -hlogs

theorem integral_zero_two_pi_log_cosh_sub_cos {z : ℝ} (hz : 0 < z) :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
        Real.log (Real.cosh z - Real.cos φ)) =
      2 * Real.pi * (z - Real.log 2) := by
  have hnormInt : IntervalIntegrable
      (fun φ : ℝ => Real.log ‖circleMap 0 1 φ - (Real.exp z : ℂ)‖)
      volume 0 (2 * Real.pi) := by
    exact circleIntegrable_log_norm_sub_const
      (c := 0) (a := (Real.exp z : ℂ)) 1
  calc
    (∫ φ in (0 : ℝ)..2 * Real.pi,
        Real.log (Real.cosh z - Real.cos φ)) =
        ∫ φ in (0 : ℝ)..2 * Real.pi,
          (2 * Real.log ‖circleMap 0 1 φ - (Real.exp z : ℂ)‖ -
            Real.log 2 - z) := by
              apply intervalIntegral.integral_congr
              intro φ _hφ
              exact log_cosh_sub_cos_eq hz φ
    _ = 2 * (∫ φ in (0 : ℝ)..2 * Real.pi,
          Real.log ‖circleMap 0 1 φ - (Real.exp z : ℂ)‖) -
          (2 * Real.pi) * Real.log 2 - (2 * Real.pi) * z := by
            rw [intervalIntegral.integral_sub
              ((hnormInt.const_mul 2).sub intervalIntegrable_const)
                intervalIntegrable_const,
              intervalIntegral.integral_sub (hnormInt.const_mul 2)
                intervalIntegrable_const,
              intervalIntegral.integral_const_mul,
              intervalIntegral.integral_const,
              intervalIntegral.integral_const]
            simp only [sub_zero, smul_eq_mul]
    _ = 2 * Real.pi * (z - Real.log 2) := by
          rw [integral_logNorm_circle_sub_exp hz]
          ring

theorem integral_log_cosh_sub_cos {z : ℝ} (hz : 0 < z) :
    (∫ φ in (0 : ℝ)..Real.pi,
        Real.log (Real.cosh z - Real.cos φ)) =
      Real.pi * (z - Real.log 2) := by
  have hsecond :
      (∫ φ in Real.pi..2 * Real.pi,
          Real.log (Real.cosh z - Real.cos φ)) =
        ∫ φ in (0 : ℝ)..Real.pi,
          Real.log (Real.cosh z - Real.cos φ) := by
    let g : ℝ → ℝ := fun φ => Real.log (Real.cosh z - Real.cos φ)
    have hsubst := intervalIntegral.integral_comp_sub_left
      (f := g) (a := (0 : ℝ)) (b := Real.pi) (2 * Real.pi)
    have hlo : 2 * Real.pi - Real.pi = Real.pi := by ring
    rw [hlo, sub_zero] at hsubst
    calc
      (∫ φ in Real.pi..2 * Real.pi,
          Real.log (Real.cosh z - Real.cos φ)) =
          ∫ φ in (0 : ℝ)..Real.pi, g (2 * Real.pi - φ) := by
            exact hsubst.symm
      _ = ∫ φ in (0 : ℝ)..Real.pi,
          Real.log (Real.cosh z - Real.cos φ) := by
            apply intervalIntegral.integral_congr
            intro φ _hφ
            dsimp only [g]
            rw [Real.cos_two_pi_sub]
  have hgcont : Continuous
      (fun φ : ℝ => Real.log (Real.cosh z - Real.cos φ)) := by
    apply Continuous.log
    · fun_prop
    · intro φ
      have hc : 1 < Real.cosh z := Real.one_lt_cosh.mpr (ne_of_gt hz)
      linarith [Real.cos_le_one φ]
  have hfull := integral_zero_two_pi_log_cosh_sub_cos hz
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hgcont.intervalIntegrable (μ := volume) (0 : ℝ) Real.pi)
    (hgcont.intervalIntegrable (μ := volume) Real.pi (2 * Real.pi))
  rw [hsecond] at hadd
  rw [← hadd] at hfull
  linarith

/-- The boundary value of the logarithmic potential.  This is the
`z = 0` case omitted from the positive-radius Jensen calculation above;
the logarithmic singularity at `φ = 0` is harmless for the interval
integral. -/
theorem integral_log_one_sub_cos :
    (∫ φ in (0 : ℝ)..Real.pi, Real.log (1 - Real.cos φ)) =
      -Real.pi * Real.log 2 := by
  have hhalf : IntervalIntegrable
      (fun φ : ℝ => Real.log (Real.sin (φ / 2))) volume 0 Real.pi := by
    have h := (intervalIntegrable_log_sin
        (a := (0 : ℝ)) (b := Real.pi / 2)).comp_mul_left
          (c := (2 : ℝ)⁻¹)
    have hzero : (0 : ℝ) / (2 : ℝ)⁻¹ = 0 := by norm_num
    have hpi : (Real.pi / 2) / (2 : ℝ)⁻¹ = Real.pi := by
      field_simp
    rw [hzero, hpi] at h
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_comm] using h
  calc
    (∫ φ in (0 : ℝ)..Real.pi, Real.log (1 - Real.cos φ)) =
        ∫ φ in (0 : ℝ)..Real.pi,
          (Real.log 2 + 2 * Real.log (Real.sin (φ / 2))) := by
      apply intervalIntegral.integral_congr_codiscreteWithin
      apply Filter.codiscreteWithin_mono
        (by tauto : Ι (0 : ℝ) Real.pi ⊆ Set.univ)
      have hanalytic : AnalyticOnNhd ℝ
          (fun φ : ℝ => Real.sin (φ / 2)) Set.univ :=
        fun _ _ => by fun_prop
      have hnonzero := hanalytic.preimage_zero_mem_codiscrete
        (x := Real.pi)
      have hpi : Real.sin (Real.pi / 2) ≠ 0 := by norm_num
      specialize hnonzero hpi
      filter_upwards [hnonzero] with φ hφ
      simp only [Set.mem_compl_iff, Set.mem_preimage,
        Set.mem_singleton_iff] at hφ
      have htrig : 1 - Real.cos φ =
          2 * Real.sin (φ / 2) ^ 2 := by
        calc
          1 - Real.cos φ = 1 - Real.cos (2 * (φ / 2)) := by ring_nf
          _ = 2 * Real.sin (φ / 2) ^ 2 := by
            rw [Real.cos_two_mul]
            nlinarith [Real.sin_sq (φ / 2)]
      rw [htrig, Real.log_mul two_ne_zero (pow_ne_zero 2 hφ),
        Real.log_pow]
      norm_num
    _ = Real.pi * Real.log 2 +
        2 * (∫ φ in (0 : ℝ)..Real.pi,
          Real.log (Real.sin (φ / 2))) := by
      rw [intervalIntegral.integral_add intervalIntegrable_const
        (hhalf.const_mul 2), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
    _ = -Real.pi * Real.log 2 := by
      rw [intervalIntegral.integral_comp_div
        (fun φ : ℝ => Real.log (Real.sin φ)) two_ne_zero,
        zero_div, integral_log_sin_zero_pi_div_two]
      simp only [smul_eq_mul]
      ring

/-- The two-variable logarithmic potential in normalized coordinates. -/
noncomputable def potential (x y : ℝ) : ℝ :=
  Real.log (2 - Real.cos (Real.pi * x) - Real.cos (Real.pi * y))

/-- For fixed first coordinate, the logarithmic potential is integrable
despite the single corner singularity at `(0,0)`. -/
theorem potential_intervalIntegrable_right (x : ℝ) :
    IntervalIntegrable (potential x) volume (0 : ℝ) 1 := by
  have hanalytic : AnalyticOnNhd ℝ
      (fun y : ℝ =>
        2 - Real.cos (Real.pi * x) - Real.cos (Real.pi * y))
      (uIcc (0 : ℝ) 1) := fun _ _ => by fun_prop
  have hlog := hanalytic.meromorphicOn.intervalIntegrable_log
  change IntervalIntegrable
    (fun y : ℝ => Real.log
      (2 - Real.cos (Real.pi * x) - Real.cos (Real.pi * y)))
    volume 0 1
  simpa only [Function.comp_def] using hlog

theorem potential_comm (x y : ℝ) : potential x y = potential y x := by
  unfold potential
  congr 1
  ring

/-- The logarithmic-potential representation of the concrete kernel on
`[0,1]`, including its logarithmic endpoint case. -/
theorem kernel_eq_log_two_add_integral_potential {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    kernel x = Real.log 2 +
      ∫ y in (0 : ℝ)..1, potential x y := by
  by_cases hxzero : x = 0
  · subst x
    have hscale := intervalIntegral.integral_comp_mul_left
      (f := fun φ : ℝ => Real.log (1 - Real.cos φ))
      (a := (0 : ℝ)) (b := 1) Real.pi_ne_zero
    simp only [mul_zero, mul_one, smul_eq_mul] at hscale
    rw [Kernel.kernel_zero]
    simp only [potential, mul_zero, Real.cos_zero]
    norm_num
    rw [hscale, integral_log_one_sub_cos]
    field_simp [Real.pi_ne_zero]
    ring
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxzero)
    have hkpos : 0 < kernel x := by
      rw [← Kernel.kernel_zero]
      exact Kernel.kernel_strictMonoOn
        (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
        hx hxpos
    have hcosh : Real.cosh (kernel x) =
        2 - Real.cos (Real.pi * x) := by
      apply Real.cosh_arcosh
      linarith [Real.cos_le_one (Real.pi * x)]
    have hscale := intervalIntegral.integral_comp_mul_left
      (f := fun φ : ℝ =>
        Real.log (Real.cosh (kernel x) - Real.cos φ))
      (a := (0 : ℝ)) (b := 1) Real.pi_ne_zero
    simp only [mul_zero, mul_one, smul_eq_mul] at hscale
    have hpotential :
        (∫ y in (0 : ℝ)..1, potential x y) =
          kernel x - Real.log 2 := by
      change (∫ y in (0 : ℝ)..1,
        Real.log (2 - Real.cos (Real.pi * x) -
          Real.cos (Real.pi * y))) = _
      rw [← hcosh, hscale,
        integral_log_cosh_sub_cos hkpos]
      field_simp [Real.pi_ne_zero]
    rw [hpotential]
    ring

/-- The half-weighted potential sum over the `a`-mesh. -/
noncomputable def gridPotentialSum (a : ℕ) (y : ℝ) : ℝ :=
  (potential 0 y + potential 1 y) / 2 +
    ∑ k ∈ Finset.range (a - 1),
      potential (((k : ℝ) + 1) / (a : ℝ)) y

/-- The finite Chebyshev filter evaluated at the concrete kernel.  This is
the exact pointwise logarithmic correction, away from the null endpoint
`y = 0`. -/
theorem gridPotentialSum_eq {a : ℕ} (ha : 0 < a) {y : ℝ}
    (hy : y ∈ Ioc (0 : ℝ) 1) :
    gridPotentialSum a y =
      (a : ℝ) * (kernel y - Real.log 2) +
        Real.log (1 - Real.exp ((-2 * kernel y) * (a : ℝ))) := by
  have hymem : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
  have hkpos : 0 < kernel y := by
    rw [← Kernel.kernel_zero]
    exact Kernel.kernel_strictMonoOn
      (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
      hymem hy.1
  have hcosh : Real.cosh (kernel y) =
      2 - Real.cos (Real.pi * y) := by
    apply Real.cosh_arcosh
    linarith [Real.cos_le_one (Real.pi * y)]
  have haOne : 1 ≤ a := ha
  have hcast : (((a - 1 : ℕ) : ℝ) + 1) = (a : ℝ) := by
    rw [Nat.cast_sub haOne]
    norm_num
  have hend0 : potential 0 y =
      Real.log (Real.cosh (kernel y) - 1) := by
    unfold potential
    rw [hcosh]
    norm_num
    congr 1
    ring
  have hend1 : potential 1 y =
      Real.log (Real.cosh (kernel y) + 1) := by
    unfold potential
    rw [hcosh, mul_one, Real.cos_pi]
    congr 1
    ring
  have hinterior (k : ℕ) :
      potential (((k : ℝ) + 1) / (a : ℝ)) y =
        Real.log (Real.cosh (kernel y) -
          Real.cos (((k : ℝ) + 1) * Real.pi /
            (((a - 1 : ℕ) : ℝ) + 1))) := by
    unfold potential
    rw [hcosh, hcast]
    congr 1
    rw [show Real.pi * (((k : ℝ) + 1) / (a : ℝ)) =
      ((k : ℝ) + 1) * Real.pi / (a : ℝ) by ring]
    ring
  have hgridHalf : gridPotentialSum a y =
      halfGridLogSum (a - 1) (kernel y) := by
    rw [gridPotentialSum, halfGridLogSum, hend0, hend1]
    apply congrArg (fun t : ℝ =>
      (Real.log (Real.cosh (kernel y) - 1) +
        Real.log (Real.cosh (kernel y) + 1)) / 2 + t)
    apply Finset.sum_congr rfl
    intro k _hk
    exact hinterior k
  rw [hgridHalf, halfGridLogSum_eq (a - 1) hkpos, hcast]
  congr 3
  ring_nf

/-- Integrated form of the finite filter. -/
theorem integral_gridPotentialSum_eq {a : ℕ} (ha : 0 < a) :
    (∫ y in (0 : ℝ)..1, gridPotentialSum a y) =
      (a : ℝ) * (kernelIntegral - Real.log 2) +
        (a : ℝ) *
          ∫ y in (0 : ℝ)..1,
            scaledCorrection (a : ℝ) (kernel y) := by
  have haRne : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have hkernelSub : IntervalIntegrable
      (fun y : ℝ => kernel y - Real.log 2) volume 0 1 :=
    kernel_intervalIntegrable.sub intervalIntegrable_const
  have hscaled := scaledCorrection_kernel_intervalIntegrable ha
  calc
    (∫ y in (0 : ℝ)..1, gridPotentialSum a y) =
        ∫ y in (0 : ℝ)..1,
          ((a : ℝ) * (kernel y - Real.log 2) +
            (a : ℝ) * scaledCorrection (a : ℝ) (kernel y)) := by
      apply intervalIntegral.integral_congr_codiscreteWithin
      filter_upwards [Filter.self_mem_codiscreteWithin (Ι (0 : ℝ) 1)]
        with y hy
      have hy' : y ∈ Ioc (0 : ℝ) 1 := by
        simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
      rw [gridPotentialSum_eq ha hy']
      unfold scaledCorrection
      field_simp [haRne]
    _ = (a : ℝ) * (kernelIntegral - Real.log 2) +
        (a : ℝ) *
          ∫ y in (0 : ℝ)..1,
            scaledCorrection (a : ℝ) (kernel y) := by
      rw [intervalIntegral.integral_add (hkernelSub.const_mul (a : ℝ))
          (hscaled.const_mul (a : ℝ)),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub kernel_intervalIntegrable
          intervalIntegrable_const,
        intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul, kernelIntegral]
      ring

/-- The corresponding half-weighted mesh sum of the kernel itself. -/
noncomputable def gridKernelSum (a : ℕ) : ℝ :=
  (kernel 0 + kernel 1) / 2 +
    ∑ k ∈ Finset.range (a - 1),
      kernel (((k : ℝ) + 1) / (a : ℝ))

theorem gridKernelSum_eq_C_add_alpha (a : ℕ) :
    gridKernelSum a = C a + alpha := by
  have hsum : C a = ∑ k ∈ Finset.range (a - 1),
      kernel (((k : ℝ) + 1) / (a : ℝ)) := by
    rw [C, Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _hk
    congr 2
    norm_num [Nat.cast_add]
    ring
  rw [gridKernelSum, Kernel.kernel_zero, Kernel.kernel_one, ← hsum]
  ring

/-- Apply the logarithmic-potential representation at every mesh point and
move the finite sum through the integral. -/
theorem gridKernelSum_eq_log_two_add_integral {a : ℕ} (ha : 0 < a) :
    gridKernelSum a = (a : ℝ) * Real.log 2 +
      ∫ y in (0 : ℝ)..1, gridPotentialSum a y := by
  have haRpos : (0 : ℝ) < a := by exact_mod_cast ha
  have haOne : 1 ≤ a := ha
  have hcast : (((a - 1 : ℕ) : ℝ) + 1) = (a : ℝ) := by
    rw [Nat.cast_sub haOne]
    norm_num
  have hzero := kernel_eq_log_two_add_integral_potential
    (x := (0 : ℝ)) (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  have hone := kernel_eq_log_two_add_integral_potential
    (x := (1 : ℝ)) (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  have hnode (k : ℕ) (hk : k ∈ Finset.range (a - 1)) :
      kernel (((k : ℝ) + 1) / (a : ℝ)) = Real.log 2 +
        ∫ y in (0 : ℝ)..1,
          potential (((k : ℝ) + 1) / (a : ℝ)) y := by
    have hklt : k < a - 1 := Finset.mem_range.mp hk
    have hkLe : k + 1 ≤ a := by omega
    have hkLeR : (k : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hkLe
    apply kernel_eq_log_two_add_integral_potential
    constructor
    · positivity
    · exact (div_le_one₀ haRpos).2 hkLeR
  have hsumKernel :
      (∑ k ∈ Finset.range (a - 1),
          kernel (((k : ℝ) + 1) / (a : ℝ))) =
        ∑ k ∈ Finset.range (a - 1),
          (Real.log 2 + ∫ y in (0 : ℝ)..1,
            potential (((k : ℝ) + 1) / (a : ℝ)) y) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hnode k hk
  have hsumInt : IntervalIntegrable
      (fun y : ℝ => ∑ k ∈ Finset.range (a - 1),
        potential (((k : ℝ) + 1) / (a : ℝ)) y) volume 0 1 := by
    have h := IntervalIntegrable.sum (Finset.range (a - 1))
      (fun k _hk => potential_intervalIntegrable_right
        (((k : ℝ) + 1) / (a : ℝ)))
    apply h.congr
    intro y _hy
    simp only [Finset.sum_apply]
  have hgridIntegral :
      (∫ y in (0 : ℝ)..1, gridPotentialSum a y) =
        ((∫ y in (0 : ℝ)..1, potential 0 y) +
          (∫ y in (0 : ℝ)..1, potential 1 y)) / 2 +
        ∑ k ∈ Finset.range (a - 1),
          ∫ y in (0 : ℝ)..1,
            potential (((k : ℝ) + 1) / (a : ℝ)) y := by
    change (∫ y in (0 : ℝ)..1,
      ((potential 0 y + potential 1 y) / 2 +
        ∑ k ∈ Finset.range (a - 1),
          potential (((k : ℝ) + 1) / (a : ℝ)) y)) = _
    rw [
      intervalIntegral.integral_add
        ((potential_intervalIntegrable_right 0).add
          (potential_intervalIntegrable_right 1) |>.div_const 2)
        hsumInt,
      intervalIntegral.integral_div,
      intervalIntegral.integral_add
        (potential_intervalIntegrable_right 0)
        (potential_intervalIntegrable_right 1),
      intervalIntegral.integral_finsetSum]
    intro k _hk
    exact potential_intervalIntegrable_right _
  have hsumConst :
      (∑ _k ∈ Finset.range (a - 1), Real.log 2) =
        ((a - 1 : ℕ) : ℝ) * Real.log 2 := by simp
  calc
    gridKernelSum a =
        ((Real.log 2 + ∫ y in (0 : ℝ)..1, potential 0 y) +
          (Real.log 2 + ∫ y in (0 : ℝ)..1, potential 1 y)) / 2 +
        ∑ k ∈ Finset.range (a - 1),
          (Real.log 2 + ∫ y in (0 : ℝ)..1,
            potential (((k : ℝ) + 1) / (a : ℝ)) y) := by
      rw [gridKernelSum, hzero, hone, hsumKernel]
    _ = (a : ℝ) * Real.log 2 +
        (((∫ y in (0 : ℝ)..1, potential 0 y) +
          (∫ y in (0 : ℝ)..1, potential 1 y)) / 2 +
        ∑ k ∈ Finset.range (a - 1),
          ∫ y in (0 : ℝ)..1,
            potential (((k : ℝ) + 1) / (a : ℝ)) y) := by
      rw [Finset.sum_add_distrib, hsumConst,
        Nat.cast_sub haOne]
      norm_num
      ring
    _ = (a : ℝ) * Real.log 2 +
        ∫ y in (0 : ℝ)..1, gridPotentialSum a y := by
      rw [hgridIntegral]

/-- The unconditional sharp trapezoidal identity `eq:trap-identity`. -/
theorem sharpTrapezoidFormula : Trapezoid.SharpTrapezoidFormula where
  formula := by
    intro a ha
    have haRne : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
    rw [trapezoid, ← gridKernelSum_eq_C_add_alpha]
    rw [gridKernelSum_eq_log_two_add_integral ha,
      integral_gridPotentialSum_eq ha]
    field_simp [haRne]
    ring

end SquareMaximality.Rectangle.SharpTrapezoid
