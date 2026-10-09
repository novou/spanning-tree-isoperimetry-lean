import SquareMaximality.Rectangle.Trapezoid
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

/-!
# Evaluation of the rectangular kernel integral

This file formalizes the Catalan-integral evaluation left open by the
rectangular reduction.  The route is

`kernelIntegral = (4 / π) ∫₀^{π/2} arsinh (sin θ) dθ`,

followed by the parameter identity

`arsinh (sin θ) = ∫₀¹ sin θ / √(1 + (u sin θ)²) du`.

After Fubini, the inner trigonometric integral is evaluated by an `arcsin`
antiderivative and identified with `∫₀¹ (1 + (uv)²)⁻¹ dv`.  A final
L¹-justified termwise integration of the geometric series connects this
double integral to the repository's definition of Catalan's constant.
-/

namespace SquareMaximality.Rectangle.Entropy

open Set MeasureTheory
open scoped Interval
open Concrete Kernel Trapezoid

/-- The smooth parameter kernel obtained by differentiating
`arsinh (u * sin θ)` in `u`. -/
noncomputable def parameterKernel (u θ : ℝ) : ℝ :=
  Real.sin θ / Real.sqrt (1 + (u * Real.sin θ) ^ 2)

/-- The rational kernel whose double integral is Catalan's constant. -/
noncomputable def rationalKernel (u v : ℝ) : ℝ :=
  1 / (1 + (u * v) ^ 2)

theorem parameterKernel_continuous :
    Continuous (Function.uncurry parameterKernel) := by
  unfold parameterKernel Function.uncurry
  have hsin : Continuous (fun p : ℝ × ℝ => Real.sin p.2) :=
    Real.continuous_sin.comp continuous_snd
  have harg : Continuous (fun p : ℝ × ℝ =>
      1 + (p.1 * Real.sin p.2) ^ 2) := by fun_prop
  exact hsin.div (Real.continuous_sqrt.comp harg) fun p => by positivity

theorem rationalKernel_continuous :
    Continuous (Function.uncurry rationalKernel) := by
  unfold rationalKernel Function.uncurry
  have hden : Continuous (fun p : ℝ × ℝ => 1 + (p.1 * p.2) ^ 2) := by
    fun_prop
  exact continuous_const.div hden fun p => by positivity

/-- Fundamental-theorem form of the parameter representation of `arsinh`. -/
theorem integral_parameterKernel (s : ℝ) :
    (∫ u in (0 : ℝ)..1, s / Real.sqrt (1 + (u * s) ^ 2)) = Real.arsinh s := by
  have hderiv : ∀ u ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => Real.arsinh (t * s))
        (s / Real.sqrt (1 + (u * s) ^ 2)) u := by
    intro u _hu
    simpa only [id_eq, one_mul, mul_one, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      ((hasDerivAt_id u).mul_const s).arsinh
  have hint : IntervalIntegrable
      (fun u : ℝ => s / Real.sqrt (1 + (u * s) ^ 2)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    have harg : Continuous (fun u : ℝ => 1 + (u * s) ^ 2) := by fun_prop
    exact continuous_const.div (Real.continuous_sqrt.comp harg) fun u => by positivity
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

theorem integral_parameterKernel_sin (θ : ℝ) :
    (∫ u in (0 : ℝ)..1, parameterKernel u θ) = Real.arsinh (Real.sin θ) := by
  exact integral_parameterKernel (Real.sin θ)

/-- The first exact reduction: the arcosh/cos kernel becomes an `arsinh`
half-wave and the interval is rescaled to `[0,π/2]`. -/
theorem kernelIntegral_eq_arsinh_sin :
    kernelIntegral = (4 / Real.pi) *
      (∫ θ in (0 : ℝ)..Real.pi / 2, Real.arsinh (Real.sin θ)) := by
  have hcongr : kernelIntegral =
      ∫ x in (0 : ℝ)..1, 2 * Real.arsinh (Real.sin ((Real.pi / 2) * x)) := by
    rw [kernelIntegral]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    simpa only [halfSine] using
      kernel_eq_two_mul_arsinh_halfSine hx'
  rw [hcongr]
  have hpi : Real.pi / 2 ≠ 0 := by positivity
  have hscale := intervalIntegral.integral_comp_mul_left
    (f := fun θ : ℝ => 2 * Real.arsinh (Real.sin θ))
    (a := (0 : ℝ)) (b := 1) hpi
  simp only [smul_eq_mul] at hscale
  rw [hscale, intervalIntegral.integral_const_mul]
  field_simp [Real.pi_ne_zero]
  ring_nf

/-- The `arsinh` integral is an absolutely integrable parameter double
integral.  This is the Fubini step in the parameter argument. -/
theorem arsinhSinIntegral_eq_parameterDouble :
    (∫ θ in (0 : ℝ)..Real.pi / 2, Real.arsinh (Real.sin θ)) =
      ∫ u in (0 : ℝ)..1,
        ∫ θ in (0 : ℝ)..Real.pi / 2, parameterKernel u θ := by
  let F : ℝ → ℝ → ℝ := fun θ u => parameterKernel u θ
  have hcont : Continuous (Function.uncurry F) := by
    change Continuous (fun p : ℝ × ℝ =>
      Real.sin p.1 / Real.sqrt (1 + (p.2 * Real.sin p.1) ^ 2))
    have hsin : Continuous (fun p : ℝ × ℝ => Real.sin p.1) :=
      Real.continuous_sin.comp continuous_fst
    have harg : Continuous (fun p : ℝ × ℝ =>
        1 + (p.2 * Real.sin p.1) ^ 2) := by fun_prop
    exact hsin.div (Real.continuous_sqrt.comp harg) fun p => by positivity
  have hint : IntegrableOn (Function.uncurry F)
      (uIoc (0 : ℝ) (Real.pi / 2) ×ˢ uIoc (0 : ℝ) 1) := by
    apply IntegrableOn.mono_set
      (hcont.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc))
    rintro ⟨θ, u⟩ ⟨hθ, hu⟩
    exact ⟨uIoc_subset_uIcc hθ, uIoc_subset_uIcc hu⟩
  calc
    (∫ θ in (0 : ℝ)..Real.pi / 2, Real.arsinh (Real.sin θ)) =
        ∫ θ in (0 : ℝ)..Real.pi / 2,
          ∫ u in (0 : ℝ)..1, F θ u := by
      apply intervalIntegral.integral_congr
      intro θ _hθ
      exact (integral_parameterKernel_sin θ).symm
    _ = ∫ u in (0 : ℝ)..1,
          ∫ θ in (0 : ℝ)..Real.pi / 2, F θ u :=
      intervalIntegral_intervalIntegral_swap hint
    _ = ∫ u in (0 : ℝ)..1,
          ∫ θ in (0 : ℝ)..Real.pi / 2, parameterKernel u θ := rfl

/-- The square-root simplification in the `arcsin` antiderivative. -/
theorem sqrt_arcsin_factor (u θ : ℝ) :
    Real.sqrt (1 + u ^ 2) *
        Real.sqrt (1 - (u * Real.cos θ / Real.sqrt (1 + u ^ 2)) ^ 2) =
      Real.sqrt (1 + (u * Real.sin θ) ^ 2) := by
  let A : ℝ := Real.sqrt (1 + u ^ 2)
  have hApos : 0 < A := by dsimp only [A]; positivity
  have hAsq : A ^ 2 = 1 + u ^ 2 := by
    dsimp only [A]
    exact Real.sq_sqrt (by positivity)
  have hcos : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have hnum : (u * Real.cos θ) ^ 2 ≤ A ^ 2 := by
    have hprod := mul_le_mul_of_nonneg_left hcos (sq_nonneg u)
    rw [hAsq]
    nlinarith [hprod]
  have hinner : 0 ≤ 1 - (u * Real.cos θ / A) ^ 2 := by
    rw [sub_nonneg, div_pow]
    exact (div_le_one (sq_pos_of_pos hApos)).2 hnum
  have hsquares :
      (A * Real.sqrt (1 - (u * Real.cos θ / A) ^ 2)) ^ 2 =
        Real.sqrt (1 + (u * Real.sin θ) ^ 2) ^ 2 := by
    have htrig : 1 - Real.cos θ ^ 2 = Real.sin θ ^ 2 := by
      nlinarith [Real.sin_sq θ]
    calc
      (A * Real.sqrt (1 - (u * Real.cos θ / A) ^ 2)) ^ 2 =
          A ^ 2 * (1 - (u * Real.cos θ / A) ^ 2) := by
            rw [mul_pow, Real.sq_sqrt hinner]
      _ = A ^ 2 - (u * Real.cos θ) ^ 2 := by
            field_simp [ne_of_gt hApos]
      _ = 1 + (u * Real.sin θ) ^ 2 := by
            rw [hAsq]
            calc
              1 + u ^ 2 - (u * Real.cos θ) ^ 2 =
                  1 + u ^ 2 * (1 - Real.cos θ ^ 2) := by ring
              _ = 1 + (u * Real.sin θ) ^ 2 := by rw [htrig]; ring
      _ = Real.sqrt (1 + (u * Real.sin θ) ^ 2) ^ 2 := by
            rw [Real.sq_sqrt (by positivity)]
  have hleft : 0 ≤ A * Real.sqrt (1 - (u * Real.cos θ / A) ^ 2) :=
    mul_nonneg hApos.le (Real.sqrt_nonneg _)
  have hright : 0 ≤ Real.sqrt (1 + (u * Real.sin θ) ^ 2) := Real.sqrt_nonneg _
  change A * Real.sqrt (1 - (u * Real.cos θ / A) ^ 2) = _
  nlinarith

/-- The explicit antiderivative used to evaluate the trigonometric parameter
integral. -/
theorem hasDerivAt_arcsin_cos_antiderivative {u : ℝ} (hu : u ≠ 0) (θ : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        -Real.arcsin (u * Real.cos t / Real.sqrt (1 + u ^ 2)) / u)
      (parameterKernel u θ) θ := by
  let A : ℝ := Real.sqrt (1 + u ^ 2)
  let z : ℝ := u * Real.cos θ / A
  have hApos : 0 < A := by dsimp only [A]; positivity
  have hAsq : A ^ 2 = 1 + u ^ 2 := by
    dsimp only [A]
    exact Real.sq_sqrt (by positivity)
  have hcos : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have hnum : (u * Real.cos θ) ^ 2 ≤ u ^ 2 := by
    have hprod := mul_le_mul_of_nonneg_left hcos (sq_nonneg u)
    nlinarith [hprod]
  have hnumLt : (u * Real.cos θ) ^ 2 < A ^ 2 := by
    rw [hAsq]
    linarith
  have hzsq : z ^ 2 < 1 := by
    dsimp only [z]
    rw [div_pow]
    exact (div_lt_one (sq_pos_of_pos hApos)).2 hnumLt
  have hzne : z ≠ -1 := by
    intro hz
    rw [hz] at hzsq
    norm_num at hzsq
  have hzone : z ≠ 1 := by
    intro hz
    rw [hz] at hzsq
    norm_num at hzsq
  have hzderiv : HasDerivAt (fun t : ℝ => u * Real.cos t / A)
      (u * (-Real.sin θ) / A) θ :=
    (Real.hasDerivAt_cos θ).const_mul u |>.div_const A
  have harcsinComp := (Real.hasDerivAt_arcsin hzne hzone).comp θ hzderiv
  have harcsin : HasDerivAt (fun t : ℝ => Real.arcsin (u * Real.cos t / A))
      ((1 / Real.sqrt (1 - z ^ 2)) * (u * (-Real.sin θ) / A)) θ :=
    harcsinComp.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _t => rfl)
  have hBpos : 0 < Real.sqrt (1 - z ^ 2) := Real.sqrt_pos.2 (sub_pos.mpr hzsq)
  have hfactor :
      A * Real.sqrt (1 - z ^ 2) = Real.sqrt (1 + (u * Real.sin θ) ^ 2) := by
    simpa only [A, z] using sqrt_arcsin_factor u θ
  have hDpos : 0 < Real.sqrt (1 + (u * Real.sin θ) ^ 2) := by positivity
  have hfactor' :
      A * Real.sqrt (1 - z ^ 2) =
        Real.sqrt (1 + u ^ 2 * Real.sin θ ^ 2) := by
    convert hfactor using 1
    ring_nf
  change HasDerivAt
    (fun t : ℝ => -Real.arcsin (u * Real.cos t / A) / u)
    (Real.sin θ / Real.sqrt (1 + (u * Real.sin θ) ^ 2)) θ
  apply (harcsin.neg.div_const u).congr_deriv
  field_simp [hu, ne_of_gt hApos, ne_of_gt hBpos, ne_of_gt hDpos]
  rw [← hfactor']
  ring

theorem parameterKernel_continuous_right (u : ℝ) :
    Continuous (parameterKernel u) := by
  unfold parameterKernel
  have harg : Continuous (fun θ : ℝ => 1 + (u * Real.sin θ) ^ 2) := by
    fun_prop
  exact Real.continuous_sin.div (Real.continuous_sqrt.comp harg) fun θ => by
    positivity

theorem rationalKernel_continuous_right (u : ℝ) :
    Continuous (rationalKernel u) := by
  unfold rationalKernel
  have hden : Continuous (fun v : ℝ => 1 + (u * v) ^ 2) := by fun_prop
  exact continuous_const.div hden fun v => by positivity

/-- For nonzero parameter, the inner trigonometric integral is the usual
continuous extension of `arctan u / u`. -/
theorem integral_parameterKernel_eq_arctan_div {u : ℝ} (hu : u ≠ 0) :
    (∫ θ in (0 : ℝ)..Real.pi / 2, parameterKernel u θ) =
      Real.arctan u / u := by
  let antiderivative : ℝ → ℝ := fun θ =>
    -Real.arcsin (u * Real.cos θ / Real.sqrt (1 + u ^ 2)) / u
  have hderiv : ∀ θ ∈ uIcc (0 : ℝ) (Real.pi / 2),
      HasDerivAt antiderivative (parameterKernel u θ) θ := by
    intro θ _hθ
    exact hasDerivAt_arcsin_cos_antiderivative hu θ
  have hint : IntervalIntegrable (parameterKernel u) volume 0 (Real.pi / 2) :=
    (parameterKernel_continuous_right u).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp only [antiderivative]
  rw [Real.cos_pi_div_two, Real.cos_zero, mul_zero, zero_div, Real.arcsin_zero,
    neg_zero, zero_div, mul_one, Real.arctan_eq_arcsin]
  ring

/-- The same quotient is the elementary integral of the rational kernel. -/
theorem integral_rationalKernel_eq_arctan_div {u : ℝ} (hu : u ≠ 0) :
    (∫ v in (0 : ℝ)..1, rationalKernel u v) = Real.arctan u / u := by
  let antiderivative : ℝ → ℝ := fun v => Real.arctan (u * v) / u
  have hbase (v : ℝ) : HasDerivAt (fun t : ℝ => Real.arctan (u * t))
      (u / (1 + (u * v) ^ 2)) v := by
    have hcomp := (Real.hasDerivAt_arctan (u * v)).comp v
      ((hasDerivAt_id v).const_mul u)
    have hcomp' : HasDerivAt (fun t : ℝ => Real.arctan (u * t))
        (1 / (1 + (u * v) ^ 2) * (u * 1)) v :=
      hcomp.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _t => rfl)
    apply hcomp'.congr_deriv
    ring
  have hderiv : ∀ v ∈ uIcc (0 : ℝ) 1,
      HasDerivAt antiderivative (rationalKernel u v) v := by
    intro v _hv
    apply ((hbase v).div_const u).congr_deriv
    unfold rationalKernel
    field_simp [hu]
  have hint : IntervalIntegrable (rationalKernel u) volume 0 1 :=
    (rationalKernel_continuous_right u).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [antiderivative, mul_one, mul_zero, Real.arctan_zero, zero_div, sub_zero]

/-- Exact equality of the two inner integrals, including the removable
parameter value `u = 0`. -/
theorem integral_parameterKernel_eq_rationalKernel (u : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi / 2, parameterKernel u θ) =
      ∫ v in (0 : ℝ)..1, rationalKernel u v := by
  by_cases hu : u = 0
  · subst u
    simp only [parameterKernel, rationalKernel, zero_mul]
    norm_num
  · rw [integral_parameterKernel_eq_arctan_div hu,
      integral_rationalKernel_eq_arctan_div hu]

/-- The power-series terms obtained after dividing the arctangent series by
its parameter. -/
noncomputable def catalanIntegralTerm (n : ℕ) (u : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * u ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ)

theorem catalanIntegralTerm_continuous (n : ℕ) :
    Continuous (catalanIntegralTerm n) := by
  unfold catalanIntegralTerm
  fun_prop

theorem integral_catalanMagnitude (n : ℕ) :
    (∫ u in (0 : ℝ)..1,
        u ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ)) =
      1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2 := by
  rw [intervalIntegral.integral_div, integral_pow]
  norm_num [Nat.cast_add, Nat.cast_mul]
  field_simp

theorem integral_catalanIntegralTerm (n : ℕ) :
    (∫ u in (0 : ℝ)..1, catalanIntegralTerm n u) =
      (-1 : ℝ) ^ n / ((2 * n + 1 : ℕ) : ℝ) ^ 2 := by
  change (∫ u in (0 : ℝ)..1,
    (-1 : ℝ) ^ n * u ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ)) = _
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul, integral_pow]
  norm_num [Nat.cast_add, Nat.cast_mul]
  field_simp

theorem norm_catalanIntegralTerm_of_nonneg (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    ‖catalanIntegralTerm n u‖ =
      u ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ) := by
  have hden : 0 ≤ 2 * (n : ℝ) + 1 := by positivity
  simp [catalanIntegralTerm, Real.norm_eq_abs, abs_of_nonneg hu,
    abs_of_nonneg hden, Nat.cast_add, Nat.cast_mul]

/-- The pointwise arctangent power series after division by a positive
parameter.  The endpoint `u = 1` is deliberately excluded; it is a null set
for the subsequent L¹ argument. -/
theorem hasSum_catalanIntegralTerm {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasSum (fun n : ℕ => catalanIntegralTerm n u)
      (∫ v in (0 : ℝ)..1, rationalKernel u v) := by
  have hnorm : ‖u‖ < 1 := by
    simpa only [Real.norm_eq_abs, abs_of_pos hu0] using hu1
  have hs := (Real.hasSum_arctan hnorm).mul_left u⁻¹
  have hs' : HasSum (fun n : ℕ => catalanIntegralTerm n u)
      (u⁻¹ * Real.arctan u) := by
    have hterms :
        (fun n : ℕ =>
          u⁻¹ * ((-1 : ℝ) ^ n * u ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ))) =
        (fun n : ℕ => catalanIntegralTerm n u) := by
      funext n
      unfold catalanIntegralTerm
      rw [pow_succ]
      field_simp [ne_of_gt hu0]
    rw [← hterms]
    exact hs
  rw [integral_rationalKernel_eq_arctan_div (ne_of_gt hu0)]
  simpa only [div_eq_mul_inv, mul_comm] using hs'

theorem catalanIntegralTerm_integrable_restrict (n : ℕ) :
    Integrable (catalanIntegralTerm n) (volume.restrict (Ioc (0 : ℝ) 1)) := by
  exact ((catalanIntegralTerm_continuous n).continuousOn.integrableOn_compact
    isCompact_Icc).mono_set Ioc_subset_Icc_self

theorem integral_catalanIntegralTerm_restrict (n : ℕ) :
    (∫ u, catalanIntegralTerm n u ∂(volume.restrict (Ioc (0 : ℝ) 1))) =
      (-1 : ℝ) ^ n / ((2 * n + 1 : ℕ) : ℝ) ^ 2 := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact integral_catalanIntegralTerm n

theorem integral_norm_catalanIntegralTerm_restrict (n : ℕ) :
    (∫ u, ‖catalanIntegralTerm n u‖ ∂(volume.restrict (Ioc (0 : ℝ) 1))) =
      1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2 := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  calc
    (∫ u in (0 : ℝ)..1, ‖catalanIntegralTerm n u‖) =
        ∫ u in (0 : ℝ)..1,
          u ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc (0 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
      exact norm_catalanIntegralTerm_of_nonneg n hu'.1
    _ = 1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2 := integral_catalanMagnitude n

theorem summable_catalanMagnitudes :
    Summable (fun n : ℕ => 1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2) := by
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    exact (summable_nat_add_iff 1).2 hp
  apply hshift.of_nonneg_of_le
  · intro n
    positivity
  · intro n
    norm_num [Nat.cast_add, Nat.cast_mul]
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    gcongr
    nlinarith

/-- L¹ termwise integration of the divided arctangent series.  Absolute
integrability is supplied by the reciprocal-square majorant proved above. -/
theorem integral_tsum_catalanIntegralTerm_eq_catalanConstant :
    (∫ u, (∑' n : ℕ, catalanIntegralTerm n u)
      ∂(volume.restrict (Ioc (0 : ℝ) 1))) = catalanConstant := by
  have hnormSum : Summable (fun n : ℕ =>
      ∫ u, ‖catalanIntegralTerm n u‖ ∂(volume.restrict (Ioc (0 : ℝ) 1))) := by
    simpa only [integral_norm_catalanIntegralTerm_restrict] using
      summable_catalanMagnitudes
  have hsum := MeasureTheory.hasSum_integral_of_summable_integral_norm
    catalanIntegralTerm_integrable_restrict hnormSum
  rw [← hsum.tsum_eq, catalanConstant]
  apply tsum_congr
  intro n
  exact integral_catalanIntegralTerm_restrict n

/-- The rational double integral is exactly the repository's alternating
odd reciprocal-square definition of Catalan's constant. -/
theorem rationalDoubleIntegral_eq_catalanConstant :
    (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, rationalKernel u v) =
      catalanConstant := by
  calc
    (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, rationalKernel u v) =
        ∫ u, (∑' n : ℕ, catalanIntegralTerm n u)
          ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      apply integral_congr_ae
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
      have hone : ∀ᵐ u : ℝ ∂volume, u ≠ 1 := by
        simp [ae_iff, measure_singleton]
      filter_upwards [hone] with u hu_ne
      intro hu
      have hu1 : u < 1 := lt_of_le_of_ne hu.2 hu_ne
      exact (hasSum_catalanIntegralTerm hu.1 hu1).tsum_eq.symm
    _ = catalanConstant := integral_tsum_catalanIntegralTerm_eq_catalanConstant

/-- Completion of the parameter argument: the `arsinh(sin)` integral is
Catalan's constant. -/
theorem arsinhSinIntegral_eq_catalanConstant :
    (∫ θ in (0 : ℝ)..Real.pi / 2, Real.arsinh (Real.sin θ)) =
      catalanConstant := by
  rw [arsinhSinIntegral_eq_parameterDouble]
  calc
    (∫ u in (0 : ℝ)..1,
        ∫ θ in (0 : ℝ)..Real.pi / 2, parameterKernel u θ) =
        ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, rationalKernel u v := by
      apply intervalIntegral.integral_congr
      intro u _hu
      exact integral_parameterKernel_eq_rationalKernel u
    _ = catalanConstant := rationalDoubleIntegral_eq_catalanConstant

/-- The independent entropy evaluation required by the staged rectangular
proof: `kernelIntegral = 4 Catalan / π`. -/
theorem kernelIntegral_eq_squareLatticeEntropy :
    kernelIntegral = squareLatticeEntropy := by
  rw [kernelIntegral_eq_arsinh_sin, arsinhSinIntegral_eq_catalanConstant,
    squareLatticeEntropy]
  ring

end SquareMaximality.Rectangle.Entropy
