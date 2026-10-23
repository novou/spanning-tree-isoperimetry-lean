module

public import SpanningTreeIsoperimetry.HankelDegreeJump

@[expose] public section

/-! Finite convolution identities underlying the generalized Hankel step.
The Toeplitz congruence and repeated Euclidean normalization are developed
from these sums, not assumed as an external factorization theorem. -/
namespace SpanningTreeIsoperimetry.HankelDeflation

open scoped BigOperators Matrix Classical
open Matrix HankelDegreeJump
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type*} [CommRing K]

def convolution (D m : ℕ → K) (n : ℕ) : K :=
  ∑ a ∈ Finset.range (n + 1), D (n - a) * m a

def transformedEntry (D m : ℕ → K) (i j : ℕ) : K :=
  ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
    D (i - a) * m (a + b) * D (j - b)

def shiftedCore (D m : ℕ → K) (i j : ℕ) : K :=
  ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
    D (i - a) * m (a + b + 1) * D (j - b)

theorem transformedEntry_symm (D m : ℕ → K) (i j : ℕ) :
    transformedEntry D m i j = transformedEntry D m j i := by
  unfold transformedEntry
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Nat.add_comm]
  ring

theorem shiftedCore_symm (D m : ℕ → K) (i j : ℕ) :
    shiftedCore D m i j = shiftedCore D m j i := by
  unfold shiftedCore
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Nat.add_comm a b]
  ring

theorem transformedEntry_zero (D m : ℕ → K) (j : ℕ) :
    transformedEntry D m 0 j = D 0 * convolution D m j := by
  simp only [transformedEntry, Finset.sum_range_one, Nat.sub_zero, Nat.zero_add,
    convolution, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem transformedEntry_succ_left (D m : ℕ → K) (i j : ℕ) :
    transformedEntry D m (i + 1) j = shiftedCore D m i j + D (i + 1) * convolution D m j := by
  unfold transformedEntry
  rw [Finset.sum_range_succ']
  congr 1
  · unfold shiftedCore
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [Nat.add_sub_add_right, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  · simp only [Nat.sub_zero, Nat.zero_add, convolution, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring

theorem transformedEntry_succ_right (D m : ℕ → K) (i j : ℕ) :
    transformedEntry D m i (j + 1) = shiftedCore D m i j + D (j + 1) * convolution D m i := by
  rw [transformedEntry_symm, transformedEntry_succ_left, shiftedCore_symm]

/-- Displacement identity for the Toeplitz-conjugated Hankel kernel. -/
theorem transformedEntry_step (D m : ℕ → K) (i j : ℕ) :
    transformedEntry D m (i + 1) j = transformedEntry D m i (j + 1) +
      D (i + 1) * convolution D m j - D (j + 1) * convolution D m i := by
  rw [transformedEntry_succ_left, transformedEntry_succ_right]
  ring

end SpanningTreeIsoperimetry.HankelDeflation
