module

public import SquareMaximality.Rectangle.Reduction
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Algebra.Order.Field.GeomSum

@[expose] public section

set_option autoImplicit false

/-!
# Concrete constants and kernels for the rectangular penalty

This module pushes `Rectangle.AnalyticInputs` down to the actual quantities in
`general.tex`.  Matrix--Tree remains an explicit interface.  The hyperbolic
increment, the `C_a` identity, the numerical `α` margins, residual positivity,
and the residual bounds are derived here rather than left as interface fields.
-/

namespace SquareMaximality.Rectangle.Concrete

/-- The manuscript's `α = log (1 + √2) = arsinh 1`. -/
noncomputable def alpha : ℝ := Real.arsinh 1

/-- The hyperbolic kernel `c(x) = arcosh (2 - cos (πx))`. -/
noncomputable def kernel (x : ℝ) : ℝ :=
  Real.arcosh (2 - Real.cos (Real.pi * x))

/-- The finite sum `C_a`.  `Ico 1 a` implements `j=1,...,a-1`. -/
noncomputable def C (a : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico 1 a, kernel ((j : ℝ) / (a : ℝ))

/-- The error term, now a definition rather than an independent input. -/
noncomputable def epsilon (κ : ℝ) (a : ℕ) : ℝ :=
  (a : ℝ) * κ - alpha - C a

/-- The logarithmic residual potential whose forward difference is `R_a(t)`. -/
noncomputable def residualPotential (a t : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico 1 a,
    Real.log (1 - Real.exp
      (-2 * (t : ℝ) * kernel ((j : ℝ) / (a : ℝ))))

/-- The manuscript's residual, in telescoping-potential form. -/
noncomputable def residual (a t : ℕ) : ℝ :=
  residualPotential a (t + 1) - residualPotential a t

/-- The concrete logarithm of the rectangular hyperbolic product.  The factor
depending only on `a` is named `base`; it cancels from every increment. -/
noncomputable def logProduct (base : ℕ → ℝ) (a t : ℕ) : ℝ :=
  base a + (t : ℝ) * C a + residualPotential a t

theorem sqrt_two_ge_one : (1 : ℝ) ≤ Real.sqrt 2 := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]
  norm_num

theorem half_le_alpha : (1 : ℝ) / 2 ≤ alpha := by
  have hsqrt : (2 : ℝ) ≤ 1 + Real.sqrt 2 := by
    linarith [sqrt_two_ge_one]
  have hpos : (0 : ℝ) < 1 + Real.sqrt 2 := by positivity
  have hinv : (1 + Real.sqrt 2)⁻¹ ≤ (2 : ℝ)⁻¹ :=
    (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 2)).2 hsqrt
  have halpha : alpha = Real.log (1 + Real.sqrt 2) := by
    norm_num [alpha, Real.arsinh]
  rw [halpha]
  calc
    (1 : ℝ) / 2 ≤ 1 - (1 + Real.sqrt 2)⁻¹ := by norm_num at hinv ⊢; linarith
    _ ≤ Real.log (1 + Real.sqrt 2) := Real.one_sub_inv_le_log_of_pos hpos

theorem one_thirtysecond_lt_alpha : (1 : ℝ) / 32 < alpha := by
  linarith [half_le_alpha]

theorem diagonalMargin : (1 : ℝ) / 32 + (1 : ℝ) / 4 < 2 * alpha := by
  linarith [half_le_alpha]

theorem cError {κ : ℝ} {a : ℕ} :
    C a = (a : ℝ) * κ - alpha - epsilon κ a := by
  simp [epsilon]

/-- `q=e^{-4α}` from equation `residual-bound`. -/
noncomputable def q : ℝ := Real.exp (-4 * alpha)

/-- `q₀=e^{-2α}` used for the exceptional diagonal residual. -/
noncomputable def q₀ : ℝ := Real.exp (-2 * alpha)

theorem alpha_pos : 0 < alpha := lt_of_lt_of_le (by norm_num) half_le_alpha

theorem q_pos : 0 < q := Real.exp_pos _

theorem q_lt_one : q < 1 := by
  rw [q, Real.exp_lt_one_iff]
  nlinarith [alpha_pos]

theorem q₀_pos : 0 < q₀ := Real.exp_pos _

theorem q₀_lt_one : q₀ < 1 := by
  rw [q₀, Real.exp_lt_one_iff]
  nlinarith [alpha_pos]

theorem exp_alpha : Real.exp alpha = 1 + Real.sqrt 2 := by
  rw [alpha, Real.exp_arsinh]
  norm_num

theorem q₀_eq : q₀ = 3 - 2 * Real.sqrt 2 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hne : 1 + Real.sqrt 2 ≠ 0 := by positivity
  rw [q₀, show -2 * alpha = -alpha + -alpha by ring, Real.exp_add,
    Real.exp_neg, exp_alpha]
  field_simp
  nlinarith

theorem q_eq_q₀_sq : q = q₀ ^ 2 := by
  rw [q, q₀, show -4 * alpha = (-2 * alpha) + (-2 * alpha) by ring,
    Real.exp_add, pow_two]

theorem q₀_fraction : q₀ / (1 - q₀) ^ 2 = (1 : ℝ) / 4 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hden : 1 - (3 - 2 * Real.sqrt 2) ≠ 0 := by
    rw [← q₀_eq]
    exact ne_of_gt (sub_pos.mpr q₀_lt_one)
  rw [q₀_eq]
  rw [div_eq_iff (pow_ne_zero 2 hden)]
  ring_nf
  nlinarith

theorem q_fraction : q / (1 - q) ^ 2 = (1 : ℝ) / 32 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsqrt3 : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
    calc
      (Real.sqrt 2) ^ 3 = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [hsqrt]
  have hsqrt4 : (Real.sqrt 2) ^ 4 = (4 : ℝ) := by
    calc
      (Real.sqrt 2) ^ 4 = ((Real.sqrt 2) ^ 2) ^ 2 := by ring
      _ = 4 := by rw [hsqrt]; norm_num
  have hden : 1 - (3 - 2 * Real.sqrt 2) ^ 2 ≠ 0 := by
    rw [← q₀_eq, ← q_eq_q₀_sq]
    exact ne_of_gt (sub_pos.mpr q_lt_one)
  rw [q_eq_q₀_sq, q₀_eq]
  rw [div_eq_iff (pow_ne_zero 2 hden)]
  ring_nf
  rw [hsqrt, hsqrt3, hsqrt4]
  ring

/-- Genuinely deeper inputs that remain after making all elementary parts concrete.

The last field is precisely the concavity/chord estimate
`c(j/a) ≥ 2αj/a`; it is upstream of, rather than identical to, either residual
target bound. -/
structure Inputs (κ : ℝ) where
  logDeterminant : ℕ → ℕ → ℝ
  base : ℕ → ℝ
  matrixTreeLog : ∀ {a t : ℕ}, 0 < a → 0 < t →
    Real.log (tauRect a t : ℝ) = logDeterminant a t
  rectangularProductLog : ∀ {a t : ℕ}, 0 < a → 0 < t →
    logDeterminant a t = logProduct base a t
  epsilon_nonneg : ∀ {a : ℕ}, 0 < a → 0 ≤ epsilon κ a
  epsilon_scaled_antitone : ∀ {a b : ℕ}, 0 < a → a ≤ b →
    (a : ℝ) * epsilon κ b ≤ (b : ℝ) * epsilon κ a
  kernel_chord_lower : ∀ {a j : ℕ}, 0 < a → 0 < j → j < a →
    2 * alpha * ((j : ℝ) / (a : ℝ)) ≤
      kernel ((j : ℝ) / (a : ℝ))

namespace Inputs

variable {κ : ℝ} (h : Inputs κ)

theorem kernel_pos (h : Inputs κ) {a j : ℕ}
    (ha : 0 < a) (hj : 0 < j) (hja : j < a) :
    0 < kernel ((j : ℝ) / (a : ℝ)) := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hratio : (0 : ℝ) < (j : ℝ) / (a : ℝ) := div_pos hjR haR
  exact lt_of_lt_of_le (mul_pos (mul_pos (by norm_num) alpha_pos) hratio)
    (h.kernel_chord_lower ha hj hja)

/-- The hyperbolic increment follows algebraically from the concrete product. -/
theorem hyperbolicIncrement {a t : ℕ} :
    logProduct h.base a (t + 1) - logProduct h.base a t =
      C a + residual a t := by
  simp only [logProduct, residual]
  push_cast
  ring

theorem residual_nonneg (h : Inputs κ) {a t : ℕ} (ha : 0 < a) (ht : 0 < t) :
    0 ≤ residual a t := by
  have hpotential : residualPotential a t ≤ residualPotential a (t + 1) := by
    apply Finset.sum_le_sum
    intro j hjmem
    rw [Finset.mem_Ico] at hjmem
    have hk := h.kernel_pos ha hjmem.1 hjmem.2
    have htR : (0 : ℝ) < t := by exact_mod_cast ht
    have hargpos : 0 < 1 - Real.exp
        (-2 * (t : ℝ) * kernel ((j : ℝ) / (a : ℝ))) := by
      rw [sub_pos, Real.exp_lt_one_iff]
      nlinarith
    apply Real.log_le_log hargpos
    have hexp : Real.exp
        (-2 * ((t + 1 : ℕ) : ℝ) * kernel ((j : ℝ) / (a : ℝ))) ≤
        Real.exp (-2 * (t : ℝ) * kernel ((j : ℝ) / (a : ℝ))) := by
      rw [Real.exp_le_exp]
      push_cast
      nlinarith
    linarith
  exact sub_nonneg.mpr hpotential

/-- The residuals telescope because they were defined as forward differences. -/
theorem residualSum_eq_potential_sub {a t u : ℕ} (htu : t ≤ u) :
    residualSum residual a t u = residualPotential a u - residualPotential a t := by
  induction u, htu using Nat.le_induction with
  | base => simp [residualSum]
  | succ u htu ih =>
      simp only [residualSum]
      rw [Finset.sum_Ico_succ_top htu]
      rw [← residualSum, ih]
      simp only [residual]
      ring

theorem potential_nonpos (h : Inputs κ) {a t : ℕ} (ha : 0 < a) (ht : 0 < t) :
    residualPotential a t ≤ 0 := by
  apply Finset.sum_nonpos
  intro j hjmem
  rw [Finset.mem_Ico] at hjmem
  have hk := h.kernel_pos ha hjmem.1 hjmem.2
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hargpos : 0 < 1 - Real.exp
      (-2 * (t : ℝ) * kernel ((j : ℝ) / (a : ℝ))) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    nlinarith
  apply Real.log_nonpos (le_of_lt hargpos)
  linarith [Real.exp_pos
    (-2 * (t : ℝ) * kernel ((j : ℝ) / (a : ℝ)))]

/-- The elementary logarithmic estimate
`-log(1-x) ≤ x/(1-x)`. -/
theorem neg_log_one_sub_le {x : ℝ} (_hx : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x) ≤ x / (1 - x) := by
  have hpos : 0 < 1 - x := sub_pos.mpr hx1
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hid : 1 - (1 - x)⁻¹ = -(x / (1 - x)) := by
    field_simp [ne_of_gt hpos]
    ring
  rw [hid] at hlog
  linarith

theorem geom_Ico_lt_fraction {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    {a : ℕ} (ha : 0 < a) :
    (∑ j ∈ Finset.Ico 1 a, x ^ j) < x / (1 - x) := by
  have h1a : 1 ≤ a := ha
  rw [geom_sum_Ico' (ne_of_lt hx1) h1a]
  apply (div_lt_div_iff_of_pos_right (sub_pos.mpr hx1)).2
  have hpow : 0 < x ^ a := pow_pos hx a
  nlinarith

theorem uniform_exponent_lower (h : Inputs κ) {a j t : ℕ}
    (ha : 0 < a) (hj : 0 < j) (hja : j < a) (hat : a ≤ t) :
    4 * alpha * (j : ℝ) ≤
      2 * (t : ℝ) * kernel ((j : ℝ) / (a : ℝ)) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hatR : (a : ℝ) ≤ (t : ℝ) := by exact_mod_cast hat
  have hratio : (1 : ℝ) ≤ (t : ℝ) / (a : ℝ) :=
    (le_div_iff₀ haR).2 (by simpa using hatR)
  have hcoef : 0 ≤ 4 * alpha * (j : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) alpha_pos.le) (Nat.cast_nonneg j)
  have hscale := mul_le_mul_of_nonneg_left hratio hcoef
  have ht_nonneg : (0 : ℝ) ≤ 2 * (t : ℝ) := by positivity
  have hkernel := mul_le_mul_of_nonneg_left
    (h.kernel_chord_lower ha hj hja) ht_nonneg
  calc
    4 * alpha * (j : ℝ) ≤
        (4 * alpha * (j : ℝ)) * ((t : ℝ) / (a : ℝ)) := by simpa using hscale
    _ = 2 * (t : ℝ) *
        (2 * alpha * ((j : ℝ) / (a : ℝ))) := by
          field_simp [ne_of_gt haR]
          ring
    _ ≤ 2 * (t : ℝ) * kernel ((j : ℝ) / (a : ℝ)) := hkernel

theorem diagonal_exponent_lower (h : Inputs κ) {a j : ℕ}
    (ha : 0 < a) (hj : 0 < j) (hja : j < a + 1) :
    2 * alpha * (j : ℝ) ≤
      2 * (a : ℝ) * kernel ((j : ℝ) / ((a + 1 : ℕ) : ℝ)) := by
  have ha1 : 0 < a + 1 := by omega
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have ha1R : (0 : ℝ) < (a + 1 : ℕ) := by positivity
  have haNat : a + 1 ≤ 2 * a := by omega
  have hratio : (1 : ℝ) ≤ 2 * (a : ℝ) / ((a + 1 : ℕ) : ℝ) := by
    rw [le_div_iff₀ ha1R]
    norm_num
    exact_mod_cast haNat
  have hcoef : 0 ≤ 2 * alpha * (j : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) alpha_pos.le) (Nat.cast_nonneg j)
  have hscale := mul_le_mul_of_nonneg_left hratio hcoef
  have ha_nonneg : (0 : ℝ) ≤ 2 * (a : ℝ) := by positivity
  have hkernel := mul_le_mul_of_nonneg_left
    (h.kernel_chord_lower ha1 hj hja) ha_nonneg
  calc
    2 * alpha * (j : ℝ) ≤
        (2 * alpha * (j : ℝ)) *
          (2 * (a : ℝ) / ((a + 1 : ℕ) : ℝ)) := by simpa using hscale
    _ = 2 * (a : ℝ) *
        (2 * alpha * ((j : ℝ) / ((a + 1 : ℕ) : ℝ))) := by
          field_simp [ne_of_gt ha1R]
    _ ≤ 2 * (a : ℝ) *
        kernel ((j : ℝ) / ((a + 1 : ℕ) : ℝ)) := hkernel

theorem exp_term_le_q_pow (h : Inputs κ) {a j t : ℕ}
    (ha : 0 < a) (hj : 0 < j) (hja : j < a) (hat : a ≤ t) :
    Real.exp (-2 * (t : ℝ) * kernel ((j : ℝ) / (a : ℝ))) ≤ q ^ j := by
  rw [q, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  change -2 * (t : ℝ) * kernel ((j : ℝ) / (a : ℝ)) ≤
    (j : ℝ) * (-4 * alpha)
  nlinarith [h.uniform_exponent_lower ha hj hja hat]

theorem exp_diagonal_term_le_q₀_pow (h : Inputs κ) {a j : ℕ}
    (ha : 0 < a) (hj : 0 < j) (hja : j < a + 1) :
    Real.exp (-2 * (a : ℝ) *
      kernel ((j : ℝ) / ((a + 1 : ℕ) : ℝ))) ≤ q₀ ^ j := by
  rw [q₀, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  change -2 * (a : ℝ) * kernel ((j : ℝ) / ((a + 1 : ℕ) : ℝ)) ≤
    (j : ℝ) * (-2 * alpha)
  nlinarith [h.diagonal_exponent_lower ha hj hja]

theorem negativePotential_lt_q_fraction (h : Inputs κ) {a t : ℕ}
    (ha : 0 < a) (hat : a ≤ t) :
    -residualPotential a t < q / (1 - q) ^ 2 := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  have hterm : ∀ j ∈ Finset.Ico 1 a,
      -Real.log (1 - Real.exp
        (-2 * (t : ℝ) * kernel ((j : ℝ) / (a : ℝ)))) ≤
        q ^ j / (1 - q) := by
    intro j hjmem
    rw [Finset.mem_Ico] at hjmem
    let x := Real.exp (-2 * (t : ℝ) * kernel ((j : ℝ) / (a : ℝ)))
    have hx : 0 ≤ x := (Real.exp_pos _).le
    have hxq : x ≤ q ^ j := h.exp_term_le_q_pow ha hjmem.1 hjmem.2 hat
    have hqj : q ^ j ≤ q := by
      simpa using pow_le_pow_of_le_one q_pos.le q_lt_one.le hjmem.1
    have hx1 : x < 1 := lt_of_le_of_lt (hxq.trans hqj) q_lt_one
    exact (neg_log_one_sub_le hx hx1).trans
      (div_le_div₀ (pow_nonneg q_pos.le j) hxq (sub_pos.mpr q_lt_one)
        (by linarith))
  have hsum : -residualPotential a t ≤
      ∑ j ∈ Finset.Ico 1 a, q ^ j / (1 - q) := by
    rw [residualPotential, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum hterm
  have hgeom := geom_Ico_lt_fraction q_pos q_lt_one ha
  have hscaled : (∑ j ∈ Finset.Ico 1 a, q ^ j / (1 - q)) <
      q / (1 - q) ^ 2 := by
    have := (div_lt_div_iff_of_pos_right (sub_pos.mpr q_lt_one)).2 hgeom
    simpa [div_eq_mul_inv, Finset.sum_mul, pow_two, mul_assoc] using this
  exact lt_of_le_of_lt hsum hscaled

theorem negativeDiagonalPotential_lt_q₀_fraction (h : Inputs κ)
    {a : ℕ} (ha : 0 < a) :
    -residualPotential (a + 1) a < q₀ / (1 - q₀) ^ 2 := by
  have hterm : ∀ j ∈ Finset.Ico 1 (a + 1),
      -Real.log (1 - Real.exp
        (-2 * (a : ℝ) * kernel ((j : ℝ) / ((a + 1 : ℕ) : ℝ)))) ≤
        q₀ ^ j / (1 - q₀) := by
    intro j hjmem
    rw [Finset.mem_Ico] at hjmem
    let x := Real.exp
      (-2 * (a : ℝ) * kernel ((j : ℝ) / ((a + 1 : ℕ) : ℝ)))
    have hx : 0 ≤ x := (Real.exp_pos _).le
    have hxq : x ≤ q₀ ^ j :=
      h.exp_diagonal_term_le_q₀_pow ha hjmem.1 hjmem.2
    have hqj : q₀ ^ j ≤ q₀ := by
      simpa using pow_le_pow_of_le_one q₀_pos.le q₀_lt_one.le hjmem.1
    have hx1 : x < 1 := lt_of_le_of_lt (hxq.trans hqj) q₀_lt_one
    exact (neg_log_one_sub_le hx hx1).trans
      (div_le_div₀ (pow_nonneg q₀_pos.le j) hxq (sub_pos.mpr q₀_lt_one)
        (by linarith))
  have hsum : -residualPotential (a + 1) a ≤
      ∑ j ∈ Finset.Ico 1 (a + 1), q₀ ^ j / (1 - q₀) := by
    rw [residualPotential, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum hterm
  have hgeom := geom_Ico_lt_fraction q₀_pos q₀_lt_one (by omega : 0 < a + 1)
  have hscaled : (∑ j ∈ Finset.Ico 1 (a + 1), q₀ ^ j / (1 - q₀)) <
      q₀ / (1 - q₀) ^ 2 := by
    have := (div_lt_div_iff_of_pos_right (sub_pos.mpr q₀_lt_one)).2 hgeom
    simpa [div_eq_mul_inv, Finset.sum_mul, pow_two, mul_assoc] using this
  exact lt_of_le_of_lt hsum hscaled

/-- Equation `residual-bound`, derived from the chord estimate and the geometric
series calculation rather than assumed. -/
theorem residualInterval_lt_one_thirtysecond (h : Inputs κ) {a t u : ℕ}
    (ha : 0 < a) (hat : a ≤ t) (htu : t < u) :
    residualSum residual a t u < (1 : ℝ) / 32 := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  have hu : 0 < u := lt_trans ht htu
  have htel := residualSum_eq_potential_sub (a := a) (Nat.le_of_lt htu)
  have htop := h.potential_nonpos ha hu
  have hbottom := h.negativePotential_lt_q_fraction ha hat
  rw [q_fraction] at hbottom
  rw [htel]
  linarith

/-- The special `R_{a+1}(a)<1/4` estimate used in the diagonal step. -/
theorem secondDiagonalResidual_lt_quarter (h : Inputs κ) {a : ℕ} (ha : 0 < a) :
    residual (a + 1) a < (1 : ℝ) / 4 := by
  have ha1 : 0 < a + 1 := by omega
  have htop := h.potential_nonpos ha1 ha1
  have hbottom := h.negativeDiagonalPotential_lt_q₀_fraction ha
  rw [q₀_fraction] at hbottom
  simp only [residual]
  linarith

/-- The potential difference agrees with the quotient formula for
`R_a(t)` displayed in the manuscript. -/
theorem residual_eq_sum_log_ratio (h : Inputs κ) {a t : ℕ}
    (ha : 0 < a) (ht : 0 < t) :
    residual a t =
      ∑ j ∈ Finset.Ico 1 a,
        Real.log
          ((1 - Real.exp (-2 * ((t + 1 : ℕ) : ℝ) *
              kernel ((j : ℝ) / (a : ℝ)))) /
            (1 - Real.exp (-2 * (t : ℝ) *
              kernel ((j : ℝ) / (a : ℝ))))) := by
  simp only [residual, residualPotential, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hjmem
  rw [Finset.mem_Ico] at hjmem
  have hk := h.kernel_pos ha hjmem.1 hjmem.2
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hden : 1 - Real.exp
      (-2 * (t : ℝ) * kernel ((j : ℝ) / (a : ℝ))) ≠ 0 := by
    apply ne_of_gt
    rw [sub_pos, Real.exp_lt_one_iff]
    nlinarith
  have hnum : 1 - Real.exp
      (-2 * ((t + 1 : ℕ) : ℝ) * kernel ((j : ℝ) / (a : ℝ))) ≠ 0 := by
    apply ne_of_gt
    rw [sub_pos, Real.exp_lt_one_iff]
    push_cast
    nlinarith
  exact (Real.log_div hnum hden).symm

/-- Assemble the old interface from only the concrete, deeper inputs. -/
noncomputable def toAnalyticInputs (h : Inputs κ) : AnalyticInputs κ where
  C := C
  epsilon := epsilon κ
  residual := residual
  alpha := alpha
  logDeterminant := h.logDeterminant
  logProduct := logProduct h.base
  matrixTreeLog := h.matrixTreeLog
  rectangularProductLog := h.rectangularProductLog
  hyperbolicIncrement := fun _ _ => h.hyperbolicIncrement
  cError := fun _ => cError
  epsilon_nonneg := h.epsilon_nonneg
  epsilon_scaled_antitone := h.epsilon_scaled_antitone
  residual_nonneg := fun ha ht => h.residual_nonneg ha ht
  residualInterval_lt_one_thirtysecond := fun ha hat htu =>
    h.residualInterval_lt_one_thirtysecond ha hat htu
  one_thirtysecond_lt_alpha := one_thirtysecond_lt_alpha
  secondDiagonalResidual_lt_quarter := fun ha =>
    h.secondDiagonalResidual_lt_quarter ha
  diagonalMargin := diagonalMargin

/-- Strict rectangular penalty from the concrete lower-level inputs. -/
theorem strictRectangularAreaPenalty (h : Inputs κ) : StrictRectangularAreaPenalty κ :=
  h.toAnalyticInputs.strictRectangularAreaPenalty_of_analyticInputs

/-- Non-strict rectangular penalty from the concrete lower-level inputs. -/
theorem rectangularAreaPenalty (h : Inputs κ) : RectangularAreaPenalty κ :=
  h.toAnalyticInputs.rectangularAreaPenalty_of_analyticInputs

end Inputs

end SquareMaximality.Rectangle.Concrete
