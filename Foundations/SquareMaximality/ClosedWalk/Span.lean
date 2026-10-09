import SquareMaximality.ClosedWalk.Marked
import Mathlib.Data.Int.Interval

set_option autoImplicit false

/-!
# Visited intervals and the exact bridge-span sum

Nearest-neighbour paths visit every integer between their minimum and maximum.
Combining that fact with the marked-bridge reflection equivalence proves the
finite identity

`sum_{γ bridge of length 2a} (span(γ)+1) = 2^(2a)`.
-/

namespace SquareMaximality
namespace ClosedWalk

/-- Restrict a word to its first `t` letters. -/
def takeOne {n t : ℕ} (γ : OneWord n) (ht : t ≤ n) : OneWord t :=
  fun i => γ ⟨i.1, lt_of_lt_of_le i.2 ht⟩

theorem oneStepAt_takeOne {n t j : ℕ} (γ : OneWord n) (ht : t ≤ n) (hj : j < t) :
    oneStepAt (takeOne γ ht) j = oneStepAt γ j := by
  simp [oneStepAt, takeOne, hj, lt_of_lt_of_le hj ht]

theorem onePosition_takeOne {n t u : ℕ} (γ : OneWord n) (ht : t ≤ n) (hu : u ≤ t) :
    onePosition (takeOne γ ht) u = onePosition γ u := by
  simp only [onePosition]
  apply Finset.sum_congr rfl
  intro j hj
  exact oneStepAt_takeOne γ ht (by have := Finset.mem_range.mp hj; omega)

theorem oneEndpoint_takeOne {n t : ℕ} (γ : OneWord n) (ht : t ≤ n) :
    oneEndpoint (takeOne γ ht) = onePosition γ t := by
  rw [oneEndpoint, onePosition_takeOne γ ht le_rfl]

private theorem min_oneVisited_nonpos {n : ℕ} (γ : OneWord n) :
    (oneVisited γ).min' (oneVisited_nonempty γ) ≤ 0 :=
  Finset.min'_le _ 0 (zero_mem_oneVisited γ)

private theorem max_oneVisited_nonneg {n : ℕ} (γ : OneWord n) :
    0 ≤ (oneVisited γ).max' (oneVisited_nonempty γ) :=
  Finset.le_max' _ 0 (zero_mem_oneVisited γ)

/-- Every integer between the attained minimum and maximum is attained. -/
theorem between_min_max_mem_oneVisited {n : ℕ} (γ : OneWord n) (k : ℤ)
    (hlo : (oneVisited γ).min' (oneVisited_nonempty γ) ≤ k)
    (hhi : k ≤ (oneVisited γ).max' (oneVisited_nonempty γ)) :
    k ∈ oneVisited γ := by
  by_cases hk : 0 ≤ k
  · have hmaxmem := Finset.max'_mem (oneVisited γ) (oneVisited_nonempty γ)
    rcases mem_oneVisited.mp hmaxmem with ⟨t, ht, hpos⟩
    have hend : oneEndpoint (takeOne γ ht) =
        (oneVisited γ).max' (oneVisited_nonempty γ) := by
      rw [oneEndpoint_takeOne, hpos]
    have hle : k ≤ oneEndpoint (takeOne γ ht) := by rwa [hend]
    rcases exists_hit_of_nonneg_of_le_endpoint (takeOne γ ht) k hk hle with
      ⟨u, hu, huhit⟩
    apply mem_oneVisited.mpr
    refine ⟨u, hu.trans ht, ?_⟩
    rw [← huhit, onePosition_takeOne γ ht hu]
  · have hmink : 0 ≤ -k := by omega
    have hminmem := Finset.min'_mem (oneVisited γ) (oneVisited_nonempty γ)
    rcases mem_oneVisited.mp hminmem with ⟨t, ht, hpos⟩
    have hend : oneEndpoint (takeOne (negateOne γ) ht) =
        -(oneVisited γ).min' (oneVisited_nonempty γ) := by
      rw [oneEndpoint_takeOne, onePosition_negateOne, hpos]
    have hle : -k ≤ oneEndpoint (takeOne (negateOne γ) ht) := by
      rw [hend]
      omega
    rcases exists_hit_of_nonneg_of_le_endpoint (takeOne (negateOne γ) ht) (-k) hmink hle with
      ⟨u, hu, huhit⟩
    apply mem_oneVisited.mpr
    refine ⟨u, hu.trans ht, ?_⟩
    rw [onePosition_takeOne (negateOne γ) ht hu, onePosition_negateOne] at huhit
    omega

/-- The set of visited levels is exactly the integer interval from minimum to maximum. -/
theorem oneVisited_eq_Icc {n : ℕ} (γ : OneWord n) :
    oneVisited γ = Finset.Icc
      ((oneVisited γ).min' (oneVisited_nonempty γ))
      ((oneVisited γ).max' (oneVisited_nonempty γ)) := by
  ext k
  simp only [Finset.mem_Icc]
  constructor
  · intro hk
    exact ⟨Finset.min'_le _ k hk, Finset.le_max' _ k hk⟩
  · rintro ⟨hlo, hhi⟩
    exact between_min_max_mem_oneVisited γ k hlo hhi

/-- The number of visited levels is `span+1`. -/
theorem card_oneVisited_eq_oneSpan_add_one {n : ℕ} (γ : OneWord n) :
    (oneVisited γ).card = oneSpan γ + 1 := by
  rw [oneVisited_eq_Icc, Int.card_Icc]
  simp only [oneSpan]
  have hle : (oneVisited γ).min' (oneVisited_nonempty γ) ≤
      (oneVisited γ).max' (oneVisited_nonempty γ) :=
    (min_oneVisited_nonpos γ).trans (max_oneVisited_nonneg γ)
  omega

private theorem card_markedBridge_eq_sum (a : ℕ) :
    Fintype.card (MarkedBridge a) =
      ∑ γ : { γ : OneWord (2 * a) // IsBridge γ }, (oneVisited γ.1).card := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro γ _
  exact Fintype.subtype_card (oneVisited γ.1) (fun _ => Iff.rfl)

/-- Sum over the bridge subtype of the number of visited levels. -/
theorem bridgeSubtype_visited_sum (a : ℕ) :
    (∑ γ : { γ : OneWord (2 * a) // IsBridge γ }, (oneVisited γ.1).card) =
      2 ^ (2 * a) := by
  rw [← card_markedBridge_eq_sum, card_markedBridge]

/-- Bridge subtypes and membership in the finite bridge set are equivalent. -/
def bridgeSubtypeEquivMem (n : ℕ) :
    { γ : OneWord n // IsBridge γ } ≃ { γ : OneWord n // γ ∈ bridges n } where
  toFun γ := ⟨γ.1, mem_bridges.mpr γ.2⟩
  invFun γ := ⟨γ.1, mem_bridges.mp γ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Finset form of the exact reflection/visited-level identity. -/
theorem bridges_visited_sum (a : ℕ) :
    ∑ γ ∈ bridges (2 * a), (oneVisited γ).card = 2 ^ (2 * a) := by
  calc
    (∑ γ ∈ bridges (2 * a), (oneVisited γ).card) =
        ∑ γ : { γ : OneWord (2 * a) // γ ∈ bridges (2 * a) },
          (oneVisited γ.1).card := (Finset.sum_coe_sort _ _).symm
    _ = ∑ γ : { γ : OneWord (2 * a) // IsBridge γ },
          (oneVisited γ.1).card := by
      symm
      apply Fintype.sum_equiv (bridgeSubtypeEquivMem (2 * a))
      intro γ
      rfl
    _ = 2 ^ (2 * a) := bridgeSubtype_visited_sum a

/-- The manuscript's exact one-dimensional bridge-span identity. -/
theorem bridges_span_add_one_sum (a : ℕ) :
    ∑ γ ∈ bridges (2 * a), (oneSpan γ + 1) = 2 ^ (2 * a) := by
  calc
    (∑ γ ∈ bridges (2 * a), (oneSpan γ + 1)) =
        ∑ γ ∈ bridges (2 * a), (oneVisited γ).card := by
      apply Finset.sum_congr rfl
      intro γ _
      exact (card_oneVisited_eq_oneSpan_add_one γ).symm
    _ = 2 ^ (2 * a) := bridges_visited_sum a

end ClosedWalk
end SquareMaximality
