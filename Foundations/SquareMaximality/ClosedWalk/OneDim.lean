module

public import SquareMaximality.ClosedWalk.Counts

@[expose] public section

set_option autoImplicit false

/-!
# One-dimensional sign walks and bridges

The walks in this file are finite Boolean words, with `true` interpreted as
`+1` and `false` as `-1`.  Positions are defined for natural times; all the
objects used below restrict time to `0,…,n`.
-/

namespace SquareMaximality
namespace ClosedWalk

/-- A one-dimensional nearest-neighbour word of length `n`. -/
abbrev OneWord (n : ℕ) := Fin n → Bool

/-- The signed contribution at a natural index, extended by zero past the word. -/
def oneStepAt {n : ℕ} (γ : OneWord n) (j : ℕ) : ℤ :=
  if h : j < n then signValue (γ ⟨j, h⟩) else 0

/-- Position after `t` steps.  Terms beyond the word length contribute zero. -/
def onePosition {n : ℕ} (γ : OneWord n) (t : ℕ) : ℤ :=
  ∑ j ∈ Finset.range t, oneStepAt γ j

@[simp] theorem onePosition_zero {n : ℕ} (γ : OneWord n) : onePosition γ 0 = 0 := by
  simp [onePosition]

theorem onePosition_succ {n t : ℕ} (γ : OneWord n) (ht : t < n) :
    onePosition γ (t + 1) = onePosition γ t + signValue (γ ⟨t, ht⟩) := by
  simp [onePosition, oneStepAt, Finset.sum_range_succ, ht]

/-- Endpoint of a one-dimensional word. -/
def oneEndpoint {n : ℕ} (γ : OneWord n) : ℤ := onePosition γ n

theorem oneEndpoint_eq_sum {n : ℕ} (γ : OneWord n) :
    oneEndpoint γ = ∑ i, signValue (γ i) := by
  rw [oneEndpoint, onePosition]
  calc
    (∑ j ∈ Finset.range n, oneStepAt γ j) =
        ∑ i : Fin n,
          if h : i.1 < n then signValue (γ ⟨i.1, h⟩) else 0 :=
      (Fin.sum_univ_eq_sum_range
        (fun j => if h : j < n then signValue (γ ⟨j, h⟩) else 0) n).symm
    _ = ∑ i, signValue (γ i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [i.2, dite_true]

/-- The finite set of levels visited at the times `0,…,n`. -/
def oneVisited {n : ℕ} (γ : OneWord n) : Finset ℤ :=
  (Finset.range (n + 1)).image (onePosition γ)

theorem oneVisited_nonempty {n : ℕ} (γ : OneWord n) : (oneVisited γ).Nonempty := by
  exact ⟨onePosition γ 0, Finset.mem_image.mpr ⟨0, by simp, rfl⟩⟩

@[simp] theorem zero_mem_oneVisited {n : ℕ} (γ : OneWord n) : 0 ∈ oneVisited γ := by
  rw [← onePosition_zero γ]
  exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩

@[simp] theorem mem_oneVisited {n : ℕ} {γ : OneWord n} {k : ℤ} :
    k ∈ oneVisited γ ↔ ∃ t ≤ n, onePosition γ t = k := by
  simp only [oneVisited, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, by omega, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, by omega, rfl⟩

/-- A bridge starts and ends at zero. -/
def IsBridge {n : ℕ} (γ : OneWord n) : Prop := oneEndpoint γ = 0

instance {n : ℕ} (γ : OneWord n) : Decidable (IsBridge γ) :=
  inferInstanceAs (Decidable (oneEndpoint γ = 0))

/-- The finite set of bridges of length `n`. -/
def bridges (n : ℕ) : Finset (OneWord n) := Finset.univ.filter IsBridge

@[simp] theorem mem_bridges {n : ℕ} {γ : OneWord n} : γ ∈ bridges n ↔ IsBridge γ := by
  simp [bridges]

/-- The subset of positions carrying `+1`. -/
def positiveSet {n : ℕ} (γ : OneWord n) : Finset (Fin n) :=
  Finset.univ.filter fun i => γ i = true

@[simp] theorem mem_positiveSet {n : ℕ} {γ : OneWord n} {i : Fin n} :
    i ∈ positiveSet γ ↔ γ i = true := by
  simp [positiveSet]

/-- Boolean words are equivalent to subsets of their positions. -/
def oneWordEquivFinset (n : ℕ) : OneWord n ≃ Finset (Fin n) where
  toFun := positiveSet
  invFun s i := decide (i ∈ s)
  left_inv γ := by funext i; simp [positiveSet]
  right_inv s := by ext i; simp [positiveSet]

theorem oneEndpoint_eq_card {n : ℕ} (γ : OneWord n) :
    oneEndpoint γ = 2 * ((positiveSet γ).card : ℤ) - n := by
  rw [oneEndpoint_eq_sum]
  simpa only [positiveSet] using sum_signValue_eq_card γ

theorem isBridge_iff_card {a : ℕ} (γ : OneWord (2 * a)) :
    IsBridge γ ↔ (positiveSet γ).card = a := by
  rw [IsBridge, oneEndpoint_eq_card]
  constructor
  · intro h
    have hz : 2 * ((positiveSet γ).card : ℤ) = 2 * a := by
      push_cast at h ⊢
      omega
    exact_mod_cast (show (positiveSet γ).card = a by omega)
  · intro h
    rw [h]
    push_cast
    omega

/-- Bridges of length `2a` are equivalent to `a`-subsets. -/
def bridgeEvenEquiv (a : ℕ) :
    { γ : OneWord (2 * a) // IsBridge γ } ≃
      { s : Finset (Fin (2 * a)) // s.card = a } :=
  (oneWordEquivFinset (2 * a)).subtypeEquiv fun γ => isBridge_iff_card γ

/-- The standard bridge count. -/
theorem card_bridges_even (a : ℕ) :
    (bridges (2 * a)).card = Nat.choose (2 * a) a := by
  calc
    (bridges (2 * a)).card = Fintype.card { γ : OneWord (2 * a) // IsBridge γ } :=
      (Fintype.subtype_card (bridges (2 * a)) (fun γ => mem_bridges)).symm
    _ = Fintype.card { s : Finset (Fin (2 * a)) // s.card = a } :=
      Fintype.card_congr (bridgeEvenEquiv a)
    _ = Nat.choose (2 * a) a := by simp

/-- Span of a one-dimensional path. -/
def oneSpan {n : ℕ} (γ : OneWord n) : ℕ :=
  Int.toNat ((oneVisited γ).max' (oneVisited_nonempty γ) -
    (oneVisited γ).min' (oneVisited_nonempty γ))

end ClosedWalk
end SquareMaximality
