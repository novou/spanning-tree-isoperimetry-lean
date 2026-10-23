module

public import SquareMaximality.Boundary.WalkCharging
public import SquareMaximality.ClosedWalk.Symmetry

@[expose] public section

set_option backward.privateInPublic true

/-!
# Summing the walk-charging inequality

This module performs the finite summation step used before Tonelli and the
log-determinant series in the manuscript.  It combines the constructed
sliding-window injection with the exact horizontal and vertical span masses.
No determinant or infinite-series input is used here.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Boundary

open ClosedWalk

/-- Total number of normalized placements of closed words of length `n`
which meet a marked face. -/
def closedPlacementCount (R S : ℕ) (V : Finset LatticePoint) (n : ℕ) : ℕ :=
  ∑ ω ∈ closedWords n, (walkMeetingStarts R S V ω).card

private theorem sum_charge {α : Type*} (s : Finset α)
    (a b c : ℕ) (f g : α → ℕ) :
    (∑ x ∈ s, (a + f x * b + g x * c)) =
      a * s.card + b * (∑ x ∈ s, f x) + c * (∑ x ∈ s, g x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      simp only [Finset.sum_insert hx, Finset.card_insert_of_notMem hx]
      rw [ih]
      ring

/-- Sum the pointwise charging inequality over all closed words of a fixed
length. -/
theorem closedPlacementCount_le
    (R S : ℕ) (V : Finset LatticePoint) (n : ℕ)
    (hV : V ⊆ grid R S)
    (hinj : ∀ ω ∈ closedWords n,
      SlidingWindowInjection R S (spanX ω + 1) V) :
    closedPlacementCount R S V n ≤
      V.card * closedWordCount n +
        horizontalInternalRunCount R S V *
          (∑ ω ∈ closedWords n, (spanX ω + 1)) +
        verticalInternalRunCount R S V *
          (∑ ω ∈ closedWords n, (spanY ω + 1)) := by
  classical
  rw [closedPlacementCount]
  calc
    (∑ ω ∈ closedWords n, (walkMeetingStarts R S V ω).card) ≤
        ∑ ω ∈ closedWords n,
          (V.card + (spanX ω + 1) * horizontalInternalRunCount R S V +
            (spanY ω + 1) * verticalInternalRunCount R S V) := by
      apply Finset.sum_le_sum
      intro ω hω
      exact walk_charging R S V ω hV (hinj ω hω)
    _ = V.card * closedWordCount n +
        horizontalInternalRunCount R S V *
          (∑ ω ∈ closedWords n, (spanX ω + 1)) +
        verticalInternalRunCount R S V *
          (∑ ω ∈ closedWords n, (spanY ω + 1)) := by
      rw [sum_charge, closedWordCount]

/-- The fixed-length charging bound for the canonical boundary-attached
vacancy set.  The sliding injection is already constructed, so this theorem
has no geometric hypothesis. -/
theorem closedPlacementCount_encodedBoundaryVacancies_le
    (R S : ℕ) (A : Finset Point) (n : ℕ) :
    closedPlacementCount R S
      (boundaryVacancies R S (encodedVacancies R S A)) n ≤
      (boundaryVacancies R S (encodedVacancies R S A)).card *
          closedWordCount n +
        horizontalInternalRunCount R S
            (boundaryVacancies R S (encodedVacancies R S A)) *
          (∑ ω ∈ closedWords n, (spanX ω + 1)) +
        verticalInternalRunCount R S
            (boundaryVacancies R S (encodedVacancies R S A)) *
          (∑ ω ∈ closedWords n, (spanY ω + 1)) := by
  apply closedPlacementCount_le
  · exact (boundaryVacancies_subset R S _).trans
      (encodedVacancies_subset_grid R S A)
  · intro ω hω
    exact slidingWindowInjection_encodedBoundaryVacancies R S (spanX ω + 1) A

/-- After inserting the exact even closed-word coefficients, both span
directions contribute the same central binomial coefficient. -/
theorem closedPlacementCount_encodedBoundaryVacancies_even_le
    (R S : ℕ) (A : Finset Point) (a : ℕ) :
    closedPlacementCount R S
      (boundaryVacancies R S (encodedVacancies R S A)) (2 * a) ≤
      (boundaryVacancies R S (encodedVacancies R S A)).card *
          (Nat.choose (2 * a) a) ^ 2 +
        (horizontalInternalRunCount R S
            (boundaryVacancies R S (encodedVacancies R S A)) +
          verticalInternalRunCount R S
            (boundaryVacancies R S (encodedVacancies R S A))) *
          Nat.choose (2 * (2 * a)) (2 * a) := by
  have h := closedPlacementCount_encodedBoundaryVacancies_le R S A (2 * a)
  rw [closedWordCount_even, closedWords_spanX_add_one_sum_even,
    closedWords_spanY_add_one_sum_even] at h
  simpa only [Nat.add_mul, Nat.add_assoc] using h

/-- Odd-length closed words, and hence their placement count, vanish. -/
@[simp] theorem closedPlacementCount_odd
    (R S : ℕ) (V : Finset LatticePoint) (a : ℕ) :
    closedPlacementCount R S V (2 * a + 1) = 0 := by
  simp [closedPlacementCount, closedWords_odd_eq_empty]

/-- Infinite-series form of the horizontal span identity used in the boundary
determinant estimate.  Odd lengths vanish, so the index `a` enumerates the
positive even lengths `2(a+1)`. -/
theorem horizontalSpanEvenSeries :
    (∑' a : ℕ,
      ((∑ ω ∈ closedWords (2 * (a + 1)), (spanX ω + 1) : ℕ) : ℝ) /
        ((2 * (a + 1) : ℕ) * (4 : ℝ) ^ (2 * (a + 1)))) =
      Real.log (4 / (1 + Real.sqrt 2)) := by
  calc
    (∑' a : ℕ,
        ((∑ ω ∈ closedWords (2 * (a + 1)), (spanX ω + 1) : ℕ) : ℝ) /
          ((2 * (a + 1) : ℕ) * (4 : ℝ) ^ (2 * (a + 1)))) =
        ∑' a : ℕ,
          (Nat.choose (4 * (a + 1)) (2 * (a + 1)) : ℝ) /
            ((2 * (a + 1) : ℕ) * (4 : ℝ) ^ (2 * (a + 1))) := by
      apply tsum_congr
      intro a
      rw [closedWords_spanX_add_one_sum_even]
      congr 3
      omega
    _ = Real.log (4 / (1 + Real.sqrt 2)) := centralBinomialEvenSeries

theorem hasSum_horizontalSpanEven :
    HasSum
      (fun a : ℕ =>
        ((∑ ω ∈ closedWords (2 * (a + 1)), (spanX ω + 1) : ℕ) : ℝ) /
          ((2 * (a + 1) : ℕ) * (4 : ℝ) ^ (2 * (a + 1))))
      (Real.log (4 / (1 + Real.sqrt 2))) := by
  refine HasSum.congr_fun ClosedWalk.hasSum_evenCentralLogTerm ?_
  intro a
  rw [closedWords_spanX_add_one_sum_even]
  simp only [ClosedWalk.evenCentralLogTerm]
  congr 3
  omega

/-- Vertical counterpart, obtained from the proved coordinate-swap
involution. -/
theorem verticalSpanEvenSeries :
    (∑' a : ℕ,
      ((∑ ω ∈ closedWords (2 * (a + 1)), (spanY ω + 1) : ℕ) : ℝ) /
        ((2 * (a + 1) : ℕ) * (4 : ℝ) ^ (2 * (a + 1)))) =
      Real.log (4 / (1 + Real.sqrt 2)) := by
  calc
    (∑' a : ℕ,
        ((∑ ω ∈ closedWords (2 * (a + 1)), (spanY ω + 1) : ℕ) : ℝ) /
          ((2 * (a + 1) : ℕ) * (4 : ℝ) ^ (2 * (a + 1)))) =
        ∑' a : ℕ,
          ((∑ ω ∈ closedWords (2 * (a + 1)), (spanX ω + 1) : ℕ) : ℝ) /
            ((2 * (a + 1) : ℕ) * (4 : ℝ) ^ (2 * (a + 1))) := by
      apply tsum_congr
      intro a
      rw [closedWords_spanY_add_one_sum_eq_spanX]
    _ = Real.log (4 / (1 + Real.sqrt 2)) := horizontalSpanEvenSeries

theorem hasSum_verticalSpanEven :
    HasSum
      (fun a : ℕ =>
        ((∑ ω ∈ closedWords (2 * (a + 1)), (spanY ω + 1) : ℕ) : ℝ) /
          ((2 * (a + 1) : ℕ) * (4 : ℝ) ^ (2 * (a + 1))))
      (Real.log (4 / (1 + Real.sqrt 2))) := by
  refine HasSum.congr_fun hasSum_horizontalSpanEven ?_
  intro a
  rw [closedWords_spanY_add_one_sum_eq_spanX]

end Boundary
end SquareMaximality
