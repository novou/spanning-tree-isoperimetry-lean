module

public import SquareMaximality.Rectangle.Concrete
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

@[expose] public section

set_option autoImplicit false

/-!
# The hyperbolic kernel chord estimate

This file proves the one remaining elementary analytic field of
`Concrete.Inputs`: for `0 ≤ x ≤ 1`,

`2 * alpha * x ≤ arcosh (2 - cos (πx))`.

The key observation is that
`sin (πx/2) - sinh (alpha*x)` is concave on `[0,1]` and vanishes at both
endpoints.  Squaring its nonnegativity gives the equivalent cosine/cosh
inequality, after which monotonicity of `arcosh` finishes the proof.
-/

namespace SquareMaximality.Rectangle.Kernel

open Set
open Concrete

theorem kernel_zero : kernel 0 = 0 := by
  norm_num [kernel]

theorem kernel_one : kernel 1 = 2 * alpha := by
  have hcosh : Real.cosh (2 * alpha) = 3 := by
    rw [Real.cosh_two_mul]
    simp [alpha]
    norm_num
  have ha : 0 ≤ 2 * alpha := mul_nonneg (by norm_num) alpha_pos.le
  calc
    kernel 1 = Real.arcosh 3 := by norm_num [kernel]
    _ = Real.arcosh (Real.cosh (2 * alpha)) := by rw [hcosh]
    _ = 2 * alpha := Real.arcosh_cosh ha

/-- The auxiliary concave gap. -/
noncomputable def gap (x : ℝ) : ℝ :=
  Real.sin ((Real.pi / 2) * x) - Real.sinh (alpha * x)

noncomputable def gapDeriv (x : ℝ) : ℝ :=
  (Real.pi / 2) * Real.cos ((Real.pi / 2) * x) -
    alpha * Real.cosh (alpha * x)

noncomputable def gapDeriv2 (x : ℝ) : ℝ :=
  -(Real.pi / 2) ^ 2 * Real.sin ((Real.pi / 2) * x) -
    alpha ^ 2 * Real.sinh (alpha * x)

theorem hasDerivAt_gap (x : ℝ) : HasDerivAt gap (gapDeriv x) x := by
  have htrig : HasDerivAt (fun y : ℝ => (Real.pi / 2) * y) (Real.pi / 2) x :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul (Real.pi / 2)
  have hhyp : HasDerivAt (fun y : ℝ => alpha * y) alpha x :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul alpha
  unfold gap gapDeriv
  convert htrig.sin.sub hhyp.sinh using 1 <;> first | rfl | ring

theorem hasDerivAt_gapDeriv (x : ℝ) :
    HasDerivAt gapDeriv (gapDeriv2 x) x := by
  have htrig : HasDerivAt (fun y : ℝ => (Real.pi / 2) * y) (Real.pi / 2) x :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul (Real.pi / 2)
  have hhyp : HasDerivAt (fun y : ℝ => alpha * y) alpha x :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul alpha
  have hcos := (htrig.cos).const_mul (Real.pi / 2)
  have hcosh := (hhyp.cosh).const_mul alpha
  unfold gapDeriv gapDeriv2
  convert hcos.sub hcosh using 1 <;> first | rfl | ring

theorem continuous_gap : Continuous gap := by
  rw [continuous_iff_continuousAt]
  exact fun x => (hasDerivAt_gap x).continuousAt

theorem gap_concave : ConcaveOn ℝ (Icc (0 : ℝ) 1) gap := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1)
    continuous_gap.continuousOn
    (fun x _ => (hasDerivAt_gap x).hasDerivWithinAt)
    (fun x _ => (hasDerivAt_gapDeriv x).hasDerivWithinAt)
  intro x hx
  rw [interior_Icc, mem_Ioo] at hx
  have htrigArg : 0 ≤ (Real.pi / 2) * x ∧
      (Real.pi / 2) * x ≤ Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  have hsin : 0 ≤ Real.sin ((Real.pi / 2) * x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi htrigArg.1 htrigArg.2
  have hsinh : 0 ≤ Real.sinh (alpha * x) :=
    Real.sinh_nonneg_iff.2 (mul_nonneg alpha_pos.le hx.1.le)
  simp only [gapDeriv2]
  have h₁ : 0 ≤ (Real.pi / 2) ^ 2 * Real.sin ((Real.pi / 2) * x) :=
    mul_nonneg (sq_nonneg _) hsin
  have h₂ : 0 ≤ alpha ^ 2 * Real.sinh (alpha * x) :=
    mul_nonneg (sq_nonneg _) hsinh
  linarith

@[simp]
theorem gap_zero : gap 0 = 0 := by simp [gap]

@[simp]
theorem gap_one : gap 1 = 0 := by simp [gap, alpha]

theorem gap_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ gap x := by
  have h := gap_concave.ge_on_segment'
    (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (a := 1 - x) (b := x) (by linarith) hx0 (by ring)
  simpa using h

theorem sinh_le_sin {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sinh (alpha * x) ≤ Real.sin ((Real.pi / 2) * x) := by
  exact sub_nonneg.mp (gap_nonneg hx0 hx1)

/-- The scalar inequality equivalent to the desired arcosh estimate. -/
theorem cosh_add_cos_le_two {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.cosh (2 * alpha * x) + Real.cos (Real.pi * x) ≤ 2 := by
  have htrigArg : 0 ≤ (Real.pi / 2) * x ∧
      (Real.pi / 2) * x ≤ Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  have hsin : 0 ≤ Real.sin ((Real.pi / 2) * x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi htrigArg.1 htrigArg.2
  have hsinh : 0 ≤ Real.sinh (alpha * x) :=
    Real.sinh_nonneg_iff.2 (mul_nonneg alpha_pos.le hx0)
  have hsquares : Real.sinh (alpha * x) ^ 2 ≤
      Real.sin ((Real.pi / 2) * x) ^ 2 :=
    (sq_le_sq₀ hsinh hsin).2 (sinh_le_sin hx0 hx1)
  have hcosh : Real.cosh (2 * alpha * x) =
      1 + 2 * Real.sinh (alpha * x) ^ 2 := by
    rw [show 2 * alpha * x = 2 * (alpha * x) by ring, Real.cosh_two_mul]
    nlinarith [Real.cosh_sq_sub_sinh_sq (alpha * x)]
  have hcos : Real.cos (Real.pi * x) =
      1 - 2 * Real.sin ((Real.pi / 2) * x) ^ 2 := by
    rw [show Real.pi * x = 2 * ((Real.pi / 2) * x) by ring,
      Real.cos_two_mul]
    nlinarith [Real.sin_sq ((Real.pi / 2) * x)]
  rw [hcosh, hcos]
  linarith

theorem kernel_nonneg (x : ℝ) : 0 ≤ kernel x := by
  apply Real.arcosh_nonneg
  linarith [Real.cos_le_one (Real.pi * x)]

theorem kernel_strictMonoOn : StrictMonoOn kernel (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hxarg : Real.pi * x ∈ Icc (0 : ℝ) Real.pi := by
    constructor
    · exact mul_nonneg Real.pi_pos.le hx.1
    · simpa using mul_le_mul_of_nonneg_left hx.2 Real.pi_pos.le
  have hyarg : Real.pi * y ∈ Icc (0 : ℝ) Real.pi := by
    constructor
    · exact mul_nonneg Real.pi_pos.le hy.1
    · simpa using mul_le_mul_of_nonneg_left hy.2 Real.pi_pos.le
  have harglt : 2 - Real.cos (Real.pi * x) <
      2 - Real.cos (Real.pi * y) := by
    have hcos := Real.strictAntiOn_cos hxarg hyarg
      (mul_lt_mul_of_pos_left hxy Real.pi_pos)
    linarith
  have hxpos : 0 < 2 - Real.cos (Real.pi * x) := by
    linarith [Real.cos_le_one (Real.pi * x)]
  have hypos : 0 < 2 - Real.cos (Real.pi * y) := by
    linarith [Real.cos_le_one (Real.pi * y)]
  exact (Real.arcosh_lt_arcosh hxpos hypos).2 harglt

theorem kernel_monotoneOn : MonotoneOn kernel (Icc (0 : ℝ) 1) :=
  kernel_strictMonoOn.monotoneOn

theorem kernel_le_two_alpha {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    kernel x ≤ 2 * alpha := by
  rw [← kernel_one]
  exact kernel_monotoneOn ⟨hx0, hx1⟩ (by constructor <;> norm_num) hx1

/-- The unconditional chord estimate `c(x) ≥ 2αx` on `[0,1]`. -/
theorem kernel_chord_lower_real {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    2 * alpha * x ≤ kernel x := by
  have hrhs : 0 ≤ 2 * alpha * x :=
    mul_nonneg (mul_nonneg (by norm_num) alpha_pos.le) hx0
  have harg : 1 ≤ 2 - Real.cos (Real.pi * x) := by
    linarith [Real.cos_le_one (Real.pi * x)]
  have hcosh : Real.cosh (2 * alpha * x) ≤
      2 - Real.cos (Real.pi * x) := by
    linarith [cosh_add_cos_le_two hx0 hx1]
  have harcosh :=
    (Real.arcosh_le_arcosh (Real.cosh_pos _) (lt_of_lt_of_le zero_lt_one harg)).2 hcosh
  rw [Real.arcosh_cosh hrhs] at harcosh
  exact harcosh

/-- Discrete form matching `Concrete.Inputs.kernel_chord_lower`. -/
theorem kernel_chord_lower {a j : ℕ} (ha : 0 < a) (hj : 0 < j) (hja : j < a) :
    2 * alpha * ((j : ℝ) / (a : ℝ)) ≤
      kernel ((j : ℝ) / (a : ℝ)) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hj0 : (0 : ℝ) ≤ (j : ℝ) / (a : ℝ) := by positivity
  have hjaR : (j : ℝ) ≤ (a : ℝ) := by exact_mod_cast (Nat.le_of_lt hja)
  have hj1 : (j : ℝ) / (a : ℝ) ≤ 1 := (div_le_one₀ haR).2 hjaR
  exact kernel_chord_lower_real hj0 hj1

/-- The remaining rectangular inputs after discharging the kernel chord estimate. -/
structure Inputs (κ : ℝ) where
  logDeterminant : ℕ → ℕ → ℝ
  base : ℕ → ℝ
  matrixTreeLog : ∀ {a t : ℕ}, 0 < a → 0 < t →
    Real.log (tauRect a t : ℝ) = logDeterminant a t
  rectangularProductLog : ∀ {a t : ℕ}, 0 < a → 0 < t →
    logDeterminant a t = Concrete.logProduct base a t
  epsilon_nonneg : ∀ {a : ℕ}, 0 < a → 0 ≤ Concrete.epsilon κ a
  epsilon_scaled_antitone : ∀ {a b : ℕ}, 0 < a → a ≤ b →
    (a : ℝ) * Concrete.epsilon κ b ≤ (b : ℝ) * Concrete.epsilon κ a

namespace Inputs

variable {κ : ℝ} (h : Inputs κ)

noncomputable def toConcreteInputs (h : Inputs κ) : Concrete.Inputs κ where
  logDeterminant := h.logDeterminant
  base := h.base
  matrixTreeLog := h.matrixTreeLog
  rectangularProductLog := h.rectangularProductLog
  epsilon_nonneg := h.epsilon_nonneg
  epsilon_scaled_antitone := h.epsilon_scaled_antitone
  kernel_chord_lower := fun ha hj hja => kernel_chord_lower ha hj hja

theorem strictRectangularAreaPenalty (h : Inputs κ) : StrictRectangularAreaPenalty κ :=
  h.toConcreteInputs.strictRectangularAreaPenalty

theorem rectangularAreaPenalty (h : Inputs κ) : RectangularAreaPenalty κ :=
  h.toConcreteInputs.rectangularAreaPenalty

end Inputs

end SquareMaximality.Rectangle.Kernel
