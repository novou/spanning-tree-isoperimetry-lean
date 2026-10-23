module

public import SquareMaximality.ClosedWalk.PlaneReflection

@[expose] public section

set_option autoImplicit false

/-!
# Horizontal first visits and spans of square-lattice words
-/

namespace SquareMaximality
namespace ClosedWalk

@[simp] theorem mem_visitedX {n : ℕ} {ω : Word n} {k : ℤ} :
    k ∈ visitedX ω ↔ ∃ t ≤ n, (position ω t).1 = k := by
  constructor
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨p, hp, rfl⟩
    rcases Finset.mem_image.mp hp with ⟨t, ht, rfl⟩
    exact ⟨t, by simpa using ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨position ω t, ?_, rfl⟩
    exact Finset.mem_image.mpr ⟨t, by simp; omega, rfl⟩

/-- Times at which the horizontal coordinate equals `k`. -/
def xHitTimes {n : ℕ} (ω : Word n) (k : ℤ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun t => (position ω t).1 = k

@[simp] theorem mem_xHitTimes {n : ℕ} {ω : Word n} {k : ℤ} {t : ℕ} :
    t ∈ xHitTimes ω k ↔ t ≤ n ∧ (position ω t).1 = k := by
  simp [xHitTimes]

theorem xHitTimes_nonempty {n : ℕ} {ω : Word n} {k : ℤ}
    (hk : k ∈ visitedX ω) : (xHitTimes ω k).Nonempty := by
  rcases mem_visitedX.mp hk with ⟨t, ht, hpos⟩
  exact ⟨t, mem_xHitTimes.mpr ⟨ht, hpos⟩⟩

/-- First visit to a horizontal level. -/
def firstHitX {n : ℕ} (ω : Word n) (k : ℤ) (hk : k ∈ visitedX ω) : ℕ :=
  (xHitTimes ω k).min' (xHitTimes_nonempty hk)

theorem firstHitX_mem {n : ℕ} (ω : Word n) (k : ℤ) (hk : k ∈ visitedX ω) :
    firstHitX ω k hk ∈ xHitTimes ω k := Finset.min'_mem _ _

theorem firstHitX_le_length {n : ℕ} (ω : Word n) (k : ℤ) (hk : k ∈ visitedX ω) :
    firstHitX ω k hk ≤ n := (mem_xHitTimes.mp (firstHitX_mem ω k hk)).1

theorem position_firstHitX {n : ℕ} (ω : Word n) (k : ℤ) (hk : k ∈ visitedX ω) :
    (position ω (firstHitX ω k hk)).1 = k :=
  (mem_xHitTimes.mp (firstHitX_mem ω k hk)).2

theorem firstHitX_minimal {n : ℕ} (ω : Word n) (k : ℤ) (hk : k ∈ visitedX ω)
    {t : ℕ} (ht : t ≤ n) (hpos : (position ω t).1 = k) : firstHitX ω k hk ≤ t :=
  Finset.min'_le _ t (mem_xHitTimes.mpr ⟨ht, hpos⟩)

theorem firstHitX_strict_minimal {n : ℕ} (ω : Word n) (k : ℤ)
    (hk : k ∈ visitedX ω) {t : ℕ} (ht : t < firstHitX ω k hk) :
    (position ω t).1 ≠ k := by
  intro hpos
  exact (Nat.not_le_of_lt ht) (firstHitX_minimal ω k hk
    (le_trans (Nat.le_of_lt ht) (firstHitX_le_length ω k hk)) hpos)

theorem firstHitX_eq_of_hit_of_minimal {n σ : ℕ} (ω : Word n) (k : ℤ)
    (hk : k ∈ visitedX ω) (hσ : σ ≤ n) (hhit : (position ω σ).1 = k)
    (hmin : ∀ t < σ, (position ω t).1 ≠ k) : firstHitX ω k hk = σ := by
  apply Nat.le_antisymm
  · exact firstHitX_minimal ω k hk hσ hhit
  · by_contra hnot
    have hlt : firstHitX ω k hk < σ := by omega
    exact hmin _ hlt (position_firstHitX ω k hk)

theorem firstHitX_reflectXAt {n : ℕ} (ω : Word n) (k : ℤ) (hk : k ∈ visitedX ω) :
    let σ := firstHitX ω k hk
    let ω' := reflectXAt σ ω
    ∀ hk' : k ∈ visitedX ω', firstHitX ω' k hk' = σ := by
  dsimp only
  intro hk'
  apply firstHitX_eq_of_hit_of_minimal
  · exact firstHitX_le_length ω k hk
  · rw [position_reflectXAt_of_le ω le_rfl, position_firstHitX]
  · intro t ht hpos
    rw [position_reflectXAt_of_le ω (Nat.le_of_lt ht)] at hpos
    exact firstHitX_strict_minimal ω k hk ht hpos

/-- Prefix of a square-lattice word. -/
def takeWord {n t : ℕ} (ω : Word n) (ht : t ≤ n) : Word t :=
  fun i => ω ⟨i.1, lt_of_lt_of_le i.2 ht⟩

theorem stepAt_takeWord {n t j : ℕ} (ω : Word n) (ht : t ≤ n) (hj : j < t) :
    stepAt (takeWord ω ht) j = stepAt ω j := by
  simp [stepAt, takeWord, hj, lt_of_lt_of_le hj ht]

theorem position_takeWord {n t u : ℕ} (ω : Word n) (ht : t ≤ n) (hu : u ≤ t) :
    position (takeWord ω ht) u = position ω u := by
  simp only [position]
  apply Finset.sum_congr rfl
  intro j hj
  exact stepAt_takeWord ω ht (by have := Finset.mem_range.mp hj; omega)

theorem total_takeWord {n t : ℕ} (ω : Word n) (ht : t ≤ n) :
    total (takeWord ω ht) = position ω t := by
  rw [← position_length, position_takeWord ω ht le_rfl]

/-- Full horizontal reflection negates every horizontal position. -/
theorem position_reflectXAt_zero_fst {n t : ℕ} (ω : Word n) :
    (position (reflectXAt 0 ω) t).1 = -(position ω t).1 := by
  rw [position_fst_eq_sum, position_fst_eq_sum]
  simp only [stepAt_reflectXAt_fst, Nat.not_lt_zero, ↓reduceIte, Finset.sum_neg_distrib]

private theorem min_visitedX_nonpos {n : ℕ} (ω : Word n) :
    (visitedX ω).min' (visitedX_nonempty ω) ≤ 0 :=
  Finset.min'_le _ 0 (zero_mem_visitedX ω)

private theorem max_visitedX_nonneg {n : ℕ} (ω : Word n) :
    0 ≤ (visitedX ω).max' (visitedX_nonempty ω) :=
  Finset.le_max' _ 0 (zero_mem_visitedX ω)

/-- Every level between the minimum and maximum horizontal coordinates is visited. -/
theorem between_min_max_mem_visitedX {n : ℕ} (ω : Word n) (k : ℤ)
    (hlo : (visitedX ω).min' (visitedX_nonempty ω) ≤ k)
    (hhi : k ≤ (visitedX ω).max' (visitedX_nonempty ω)) : k ∈ visitedX ω := by
  by_cases hk : 0 ≤ k
  · rcases mem_visitedX.mp (Finset.max'_mem (visitedX ω) (visitedX_nonempty ω)) with
      ⟨t, ht, hpos⟩
    have hle : k ≤ (total (takeWord ω ht)).1 := by rw [total_takeWord, hpos]; exact hhi
    rcases exists_x_hit_of_nonneg_of_le_total (takeWord ω ht) k hk hle with ⟨u, hu, huhit⟩
    exact mem_visitedX.mpr ⟨u, hu.trans ht, (congrArg Prod.fst (position_takeWord ω ht hu)).symm.trans huhit⟩
  · rcases mem_visitedX.mp (Finset.min'_mem (visitedX ω) (visitedX_nonempty ω)) with
      ⟨t, ht, hpos⟩
    have hk' : 0 ≤ -k := by omega
    have hle : -k ≤ (total (takeWord (reflectXAt 0 ω) ht)).1 := by
      rw [total_takeWord, position_reflectXAt_zero_fst, hpos]
      omega
    rcases exists_x_hit_of_nonneg_of_le_total (takeWord (reflectXAt 0 ω) ht) (-k) hk' hle with
      ⟨u, hu, huhit⟩
    apply mem_visitedX.mpr
    refine ⟨u, hu.trans ht, ?_⟩
    have htake := congrArg Prod.fst (position_takeWord (reflectXAt 0 ω) ht hu)
    rw [position_reflectXAt_zero_fst] at htake
    omega

theorem visitedX_eq_Icc {n : ℕ} (ω : Word n) :
    visitedX ω = Finset.Icc ((visitedX ω).min' (visitedX_nonempty ω))
      ((visitedX ω).max' (visitedX_nonempty ω)) := by
  ext k
  simp only [Finset.mem_Icc]
  constructor
  · intro hk
    exact ⟨Finset.min'_le _ k hk, Finset.le_max' _ k hk⟩
  · rintro ⟨hlo, hhi⟩
    exact between_min_max_mem_visitedX ω k hlo hhi

theorem card_visitedX_eq_spanX_add_one {n : ℕ} (ω : Word n) :
    (visitedX ω).card = spanX ω + 1 := by
  rw [visitedX_eq_Icc, Int.card_Icc]
  simp only [spanX]
  have hle : (visitedX ω).min' (visitedX_nonempty ω) ≤
      (visitedX ω).max' (visitedX_nonempty ω) :=
    (min_visitedX_nonpos ω).trans (max_visitedX_nonneg ω)
  omega

end ClosedWalk
end SquareMaximality
