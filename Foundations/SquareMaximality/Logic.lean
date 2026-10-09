import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace SquareMaximality

/-!
# Arithmetic and order glue for square maximality

This file contains only the elementary real and natural-number reasoning used
when the two analytic estimates are assembled.  In particular, it has no
dependency on the geometric encoding of lattice sets.
-/

section Cancellation

variable {a b c κ d : ℝ}

/-- Two bounds with matching penalty terms imply the desired comparison. -/
theorem le_of_matching_penalties
    (hab : a - b ≤ -κ * d) (hbc : b - c ≤ κ * d) :
    a ≤ c := by
  linarith

/-- Difference form of `le_of_matching_penalties`. -/
theorem sub_nonpos_of_matching_penalties
    (hab : a - b ≤ -κ * d) (hbc : b - c ≤ κ * d) :
    a - c ≤ 0 := by
  linarith

/-- If the second of two matching bounds is strict, so is their conclusion. -/
theorem lt_of_matching_penalties
    (hab : a - b ≤ -κ * d) (hbc : b - c < κ * d) :
    a < c := by
  linarith

/-- Difference form of `lt_of_matching_penalties`. -/
theorem sub_neg_of_matching_penalties
    (hab : a - b ≤ -κ * d) (hbc : b - c < κ * d) :
    a - c < 0 := by
  linarith

/-- The symmetric strict variant, useful if strictness comes from the first bound. -/
theorem lt_of_matching_penalties_left
    (hab : a - b < -κ * d) (hbc : b - c ≤ κ * d) :
    a < c := by
  linarith

/-- Equality is impossible when one of the matching estimates is strict. -/
theorem ne_of_matching_penalties
    (hab : a - b ≤ -κ * d) (hbc : b - c < κ * d) :
    a ≠ c :=
  ne_of_lt (lt_of_matching_penalties hab hbc)

end Cancellation

section Logarithms

/-- A logarithmic comparison of positive natural numbers reflects `≤`. -/
theorem nat_le_of_log_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hlog : Real.log (m : ℝ) ≤ Real.log (n : ℝ)) :
    m ≤ n := by
  have hmℝ : (0 : ℝ) < m := by exact_mod_cast hm
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hn
  have hexp : Real.exp (Real.log (m : ℝ)) ≤ Real.exp (Real.log (n : ℝ)) :=
    Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hmℝ, Real.exp_log hnℝ] at hexp
  exact_mod_cast hexp

/-- A strict logarithmic comparison of positive natural numbers reflects `<`. -/
theorem nat_lt_of_log_lt {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hlog : Real.log (m : ℝ) < Real.log (n : ℝ)) :
    m < n := by
  have hmℝ : (0 : ℝ) < m := by exact_mod_cast hm
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hn
  have hexp : Real.exp (Real.log (m : ℝ)) < Real.exp (Real.log (n : ℝ)) :=
    Real.exp_lt_exp.mpr hlog
  rw [Real.exp_log hmℝ, Real.exp_log hnℝ] at hexp
  exact_mod_cast hexp

/-- Consequently a strict logarithmic comparison rules out equality. -/
theorem nat_ne_of_log_lt {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hlog : Real.log (m : ℝ) < Real.log (n : ℝ)) :
    m ≠ n :=
  ne_of_lt (nat_lt_of_log_lt hm hn hlog)

end Logarithms

end SquareMaximality
