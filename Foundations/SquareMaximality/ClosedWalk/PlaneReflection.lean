module

public import SquareMaximality.ClosedWalk.Span

@[expose] public section

set_option autoImplicit false

/-!
# Horizontal reflection of square-lattice words
-/

namespace SquareMaximality
namespace ClosedWalk

/-- Reflect a step in a vertical line. -/
def reflectXStep : Step → Step
  | .east => .west
  | .west => .east
  | .north => .north
  | .south => .south

@[simp] theorem reflectXStep_involutive : Function.Involutive reflectXStep := by
  intro d
  cases d <;> rfl

@[simp] theorem reflectXStep_vector_fst (d : Step) :
    (reflectXStep d).vector.1 = -d.vector.1 := by
  cases d <;> rfl

@[simp] theorem reflectXStep_vector_snd (d : Step) :
    (reflectXStep d).vector.2 = d.vector.2 := by
  cases d <;> rfl

/-- Reflect horizontal increments at and after time `σ`. -/
def reflectXAt {n : ℕ} (σ : ℕ) (ω : Word n) : Word n :=
  fun i => if i.1 < σ then ω i else reflectXStep (ω i)

@[simp] theorem reflectXAt_involutive {n σ : ℕ} :
    Function.Involutive (reflectXAt σ : Word n → Word n) := by
  intro ω
  funext i
  by_cases hi : i.1 < σ
  · simp [reflectXAt, hi]
  · simp only [reflectXAt, hi, ↓reduceIte]
    exact reflectXStep_involutive (ω i)

theorem stepAt_reflectXAt_fst {n σ j : ℕ} (ω : Word n) :
    (stepAt (reflectXAt σ ω) j).1 =
      if j < σ then (stepAt ω j).1 else -(stepAt ω j).1 := by
  by_cases hjn : j < n
  · by_cases hjσ : j < σ
    · simp [stepAt, reflectXAt, hjn, hjσ]
    · simp [stepAt, reflectXAt, hjn, hjσ]
  · simp [stepAt, hjn]

theorem stepAt_reflectXAt_snd {n σ j : ℕ} (ω : Word n) :
    (stepAt (reflectXAt σ ω) j).2 = (stepAt ω j).2 := by
  by_cases hjn : j < n
  · by_cases hjσ : j < σ
    · simp [stepAt, reflectXAt, hjn, hjσ]
    · simp [stepAt, reflectXAt, hjn, hjσ]
  · simp [stepAt, hjn]

theorem position_fst_eq_sum {n t : ℕ} (ω : Word n) :
    (position ω t).1 = ∑ j ∈ Finset.range t, (stepAt ω j).1 := by
  rw [position, Prod.fst_sum]

theorem position_snd_eq_sum {n t : ℕ} (ω : Word n) :
    (position ω t).2 = ∑ j ∈ Finset.range t, (stepAt ω j).2 := by
  rw [position, Prod.snd_sum]

theorem position_succ {n t : ℕ} (ω : Word n) (ht : t < n) :
    position ω (t + 1) = position ω t + (ω ⟨t, ht⟩).vector := by
  simp only [position, Finset.sum_range_succ]
  simp [stepAt, ht]

/-- Reflection leaves positions through the reflection time unchanged. -/
theorem position_reflectXAt_of_le {n σ t : ℕ} (ω : Word n) (ht : t ≤ σ) :
    position (reflectXAt σ ω) t = position ω t := by
  simp only [position]
  apply Finset.sum_congr rfl
  intro j hj
  have hjσ : j < σ := by have := Finset.mem_range.mp hj; omega
  by_cases hjn : j < n
  · simp [stepAt, reflectXAt, hjn, hjσ]
  · simp [stepAt, hjn]

/-- Horizontal endpoint after reflection. -/
theorem total_reflectXAt_fst {n σ : ℕ} (ω : Word n) (hσ : σ ≤ n) :
    (total (reflectXAt σ ω)).1 = 2 * (position ω σ).1 - (total ω).1 := by
  have hsplit := Finset.sum_range_add_sum_Ico (fun j => (stepAt ω j).1) hσ
  calc
    (total (reflectXAt σ ω)).1 =
        ∑ j ∈ Finset.range n, (stepAt (reflectXAt σ ω) j).1 := by
      rw [← position_fst_eq_sum, position_length]
    _ = (∑ j ∈ Finset.range σ, (stepAt ω j).1) +
          ∑ j ∈ Finset.Ico σ n, -(stepAt ω j).1 := by
      rw [← Finset.sum_range_add_sum_Ico
        (fun j => (stepAt (reflectXAt σ ω) j).1) hσ]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        rw [stepAt_reflectXAt_fst, if_pos (Finset.mem_range.mp hj)]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [stepAt_reflectXAt_fst, if_neg (Nat.not_lt_of_ge (Finset.mem_Ico.mp hj).1)]
    _ = 2 * (∑ j ∈ Finset.range σ, (stepAt ω j).1) -
        ((∑ j ∈ Finset.range σ, (stepAt ω j).1) +
          ∑ j ∈ Finset.Ico σ n, (stepAt ω j).1) := by
      rw [Finset.sum_neg_distrib]
      ring
    _ = 2 * (position ω σ).1 - (total ω).1 := by
      rw [position_fst_eq_sum, ← position_length, position_fst_eq_sum, ← hsplit]

/-- Vertical endpoint is unchanged by horizontal reflection. -/
theorem total_reflectXAt_snd {n σ : ℕ} (ω : Word n) :
    (total (reflectXAt σ ω)).2 = (total ω).2 := by
  calc
    (total (reflectXAt σ ω)).2 =
        ∑ j ∈ Finset.range n, (stepAt (reflectXAt σ ω) j).2 := by
      rw [← position_snd_eq_sum, position_length]
    _ = ∑ j ∈ Finset.range n, (stepAt ω j).2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact stepAt_reflectXAt_snd ω
    _ = (total ω).2 := by rw [← position_snd_eq_sum, position_length]

/-- Times at which the horizontal coordinate has reached at least `k`. -/
private def xUpperTimes {n : ℕ} (ω : Word n) (k : ℤ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun t => k ≤ (position ω t).1

/-- A lazy nearest-neighbour horizontal path ending at or beyond `k ≥ 0`
visits `k`; vertical steps merely give zero horizontal increments. -/
theorem exists_x_hit_of_nonneg_of_le_total {n : ℕ} (ω : Word n) (k : ℤ)
    (hk : 0 ≤ k) (hle : k ≤ (total ω).1) :
    ∃ t ≤ n, (position ω t).1 = k := by
  have hnmem : n ∈ xUpperTimes ω k := by
    simp [xUpperTimes, hle]
  have hne : (xUpperTimes ω k).Nonempty := ⟨n, hnmem⟩
  let σ := (xUpperTimes ω k).min' hne
  have hσmem : σ ∈ xUpperTimes ω k := Finset.min'_mem _ _
  have hσle : σ ≤ n := by
    have h := (show σ ≤ n ∧ k ≤ (position ω σ).1 by
      simpa [xUpperTimes] using hσmem)
    exact h.1
  have hkσ : k ≤ (position ω σ).1 := by
    have h := (show σ ≤ n ∧ k ≤ (position ω σ).1 by
      simpa [xUpperTimes] using hσmem)
    exact h.2
  by_cases hσzero : σ = 0
  · refine ⟨0, Nat.zero_le _, ?_⟩
    rw [hσzero, position_zero] at hkσ
    rw [position_zero]
    omega
  · obtain ⟨t, htσ⟩ := Nat.exists_eq_succ_of_ne_zero hσzero
    have htlt : t < n := by omega
    have htNot : ¬ k ≤ (position ω t).1 := by
      intro ht
      have htmem : t ∈ xUpperTimes ω k := by
        simp [xUpperTimes, ht, show t ≤ n by omega]
      have hmin := Finset.min'_le _ t htmem
      omega
    have hstep := congrArg Prod.fst (position_succ ω htlt)
    have hinc : (ω ⟨t, htlt⟩).vector.1 ≤ 1 := by
      cases ω ⟨t, htlt⟩ <;> norm_num
    refine ⟨t + 1, by omega, ?_⟩
    simp only [Prod.fst_add] at hstep
    rw [htσ] at hkσ
    have hkfinal : k ≤ (position ω (t + 1)).1 := by
      simpa only [Nat.succ_eq_add_one] using hkσ
    omega

end ClosedWalk
end SquareMaximality
