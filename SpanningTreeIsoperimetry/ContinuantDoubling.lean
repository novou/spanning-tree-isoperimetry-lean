module

public import SpanningTreeIsoperimetry.SmallCases

@[expose] public section

/-! Division-free binary continuant construction over any commutative ring. -/
namespace SpanningTreeIsoperimetry.ContinuantDoubling

open SmallCases
variable {K : Type*} [CommRing K]

def previous (x : K) : ℕ → K
  | 0 => 0
  | n + 1 => continuant x n

theorem continuant_add (x : K) (m n : ℕ) :
    continuant x (m + n + 2) =
      continuant x (m + 1) * continuant x (n + 1) - continuant x m * continuant x n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [continuant_recurrence, mul_comm]
  | one =>
    rw [show m + 1 + 2 = (m + 1) + 2 by omega, continuant_recurrence,
      continuant_recurrence]
    simp [continuant]
    ring
  | more n ih ih1 =>
    have he : m + (n + 2) + 2 = (m + n + 2) + 2 := by omega
    rw [he, continuant_recurrence]
    rw [show m + n + 2 + 1 = m + (n + 1) + 2 by omega, ih1, ih,
      show n + 2 + 1 = (n + 1) + 2 by omega, continuant_recurrence, continuant_recurrence]
    simp only [continuant_recurrence]
    ring

theorem double_even (x : K) (m : ℕ) :
    continuant x (2 * m) = continuant x m ^ 2 - previous x m ^ 2 := by
  cases m with
  | zero => simp [continuant, previous]
  | succ m =>
    have h := continuant_add x m m
    rw [show m + m + 2 = 2 * (m + 1) by omega] at h
    simpa only [previous, pow_two] using h

theorem double_odd (x : K) (m : ℕ) :
    continuant x (2 * m + 1) = continuant x m * (x * continuant x m - 2 * previous x m) := by
  cases m with
  | zero => simp [continuant, previous]
  | succ m =>
    have h := continuant_add x (m + 1) m
    rw [show m + 1 + m + 2 = 2 * (m + 1) + 1 by omega, continuant_recurrence] at h
    rw [h]
    simp only [previous]
    ring

theorem previous_even (x : K) (m : ℕ) :
    previous x (2 * m) = previous x m * (2 * continuant x m - x * previous x m) := by
  cases m with
  | zero => simp [previous]
  | succ m =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, previous, double_odd]
    simp only [previous]
    cases m with
    | zero => simp [continuant, previous]; ring
    | succ m =>
      rw [continuant_recurrence]
      simp only [previous]
      ring

theorem previous_odd (x : K) (m : ℕ) :
    previous x (2 * m + 1) = continuant x m ^ 2 - previous x m ^ 2 := by
  rw [previous, double_even]

/-- Binary recursion uses only addition, subtraction, multiplication, and
natural-index halving. It therefore works in every characteristic. -/
def binaryContinuants (x : K) (n : ℕ) : K × K :=
  if hn : n = 0 then (1, 0) else
    let p := binaryContinuants x (n / 2)
    if n % 2 = 0 then
      (p.1 ^ 2 - p.2 ^ 2, p.2 * (2 * p.1 - x * p.2))
    else (p.1 * (x * p.1 - 2 * p.2), p.1 ^ 2 - p.2 ^ 2)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by norm_num)

/-- The executable binary recursion constructs both consecutive continuants. -/
theorem binaryContinuants_eq (x : K) (n : ℕ) :
    binaryContinuants x n = (continuant x n, previous x n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [binaryContinuants]
    split_ifs with hn he
    · subst n
      simp [continuant, previous]
    · rw [ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by norm_num))]
      have hn' : n = 2 * (n / 2) := by omega
      conv_rhs => rw [hn', double_even, previous_even]
    · rw [ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by norm_num))]
      have hn' : n = 2 * (n / 2) + 1 := by omega
      conv_rhs => rw [hn', double_odd, previous_odd]

end SpanningTreeIsoperimetry.ContinuantDoubling
