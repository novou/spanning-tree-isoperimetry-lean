module

public import SquareMaximality.ClosedWalk.OneDim
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

set_option autoImplicit false

/-!
# First-hit reflection for one-dimensional walks

This file implements the finite reflection used in the manuscript.  Reflection
at time `σ` keeps the first `σ` signs and flips every later sign.  In particular,
if a bridge first reaches level `k` at `σ`, its reflection ends at `2k`.
-/

namespace SquareMaximality
namespace ClosedWalk

@[simp] theorem signValue_not (b : Bool) : signValue (!b) = -signValue b := by
  cases b <;> rfl

/-- Reflect all steps at and after time `σ`. -/
def reflectAt {n : ℕ} (σ : ℕ) (γ : OneWord n) : OneWord n :=
  fun i => if i.1 < σ then γ i else !γ i

@[simp] theorem reflectAt_apply_of_lt {n σ : ℕ} (γ : OneWord n) (i : Fin n)
    (hi : i.1 < σ) : reflectAt σ γ i = γ i := by
  simp [reflectAt, hi]

@[simp] theorem reflectAt_apply_of_le {n σ : ℕ} (γ : OneWord n) (i : Fin n)
    (hi : σ ≤ i.1) : reflectAt σ γ i = !γ i := by
  simp [reflectAt, show ¬ i.1 < σ by omega]

@[simp] theorem reflectAt_involutive {n σ : ℕ} :
    Function.Involutive (reflectAt σ : OneWord n → OneWord n) := by
  intro γ
  funext i
  by_cases hi : i.1 < σ <;> simp [reflectAt, hi]

theorem oneStepAt_reflectAt {n σ j : ℕ} (γ : OneWord n) :
    oneStepAt (reflectAt σ γ) j =
      if j < σ then oneStepAt γ j else -oneStepAt γ j := by
  by_cases hjn : j < n
  · by_cases hjσ : j < σ
    · simp [oneStepAt, hjn, hjσ, reflectAt]
    · simp [oneStepAt, hjn, hjσ, reflectAt]
  · simp [oneStepAt, hjn]

/-- Reflection leaves every position through the reflection time unchanged. -/
theorem onePosition_reflectAt_of_le {n σ t : ℕ} (γ : OneWord n) (ht : t ≤ σ) :
    onePosition (reflectAt σ γ) t = onePosition γ t := by
  simp only [onePosition]
  apply Finset.sum_congr rfl
  intro j hj
  have hjt : j < t := Finset.mem_range.mp hj
  rw [oneStepAt_reflectAt, if_pos (by omega)]

/-- The endpoint after reflection is `2 * position(σ) - endpoint`. -/
theorem oneEndpoint_reflectAt {n σ : ℕ} (γ : OneWord n) (hσ : σ ≤ n) :
    oneEndpoint (reflectAt σ γ) = 2 * onePosition γ σ - oneEndpoint γ := by
  have hsplit := Finset.sum_range_add_sum_Ico (oneStepAt γ) hσ
  rw [oneEndpoint, onePosition]
  calc
    (∑ j ∈ Finset.range n, oneStepAt (reflectAt σ γ) j) =
        (∑ j ∈ Finset.range σ, oneStepAt γ j) +
          ∑ j ∈ Finset.Ico σ n, -oneStepAt γ j := by
      rw [← Finset.sum_range_add_sum_Ico
        (fun j => oneStepAt (reflectAt σ γ) j) hσ]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        rw [oneStepAt_reflectAt, if_pos (Finset.mem_range.mp hj)]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [oneStepAt_reflectAt, if_neg]
        exact Nat.not_lt_of_ge (Finset.mem_Ico.mp hj).1
    _ = 2 * (∑ j ∈ Finset.range σ, oneStepAt γ j) -
        ((∑ j ∈ Finset.range σ, oneStepAt γ j) +
          ∑ j ∈ Finset.Ico σ n, oneStepAt γ j) := by
      rw [Finset.sum_neg_distrib]
      ring
    _ = 2 * onePosition γ σ - oneEndpoint γ := by
      rw [onePosition, oneEndpoint, onePosition, ← hsplit]

/-- Reflecting a bridge at a visit to `k` produces endpoint `2k`. -/
theorem oneEndpoint_reflectAt_of_bridge_of_hit {n σ : ℕ} {γ : OneWord n} {k : ℤ}
    (hσ : σ ≤ n) (hbridge : IsBridge γ) (hhit : onePosition γ σ = k) :
    oneEndpoint (reflectAt σ γ) = 2 * k := by
  rw [oneEndpoint_reflectAt γ hσ, hhit, hbridge]
  ring

end ClosedWalk
end SquareMaximality
