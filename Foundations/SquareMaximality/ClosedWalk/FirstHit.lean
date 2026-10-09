import SquareMaximality.ClosedWalk.Reflection

set_option autoImplicit false

/-!
# First visits and the finite intermediate-value property
-/

namespace SquareMaximality
namespace ClosedWalk

/-- Delete the final letter of a nonempty one-dimensional word. -/
def dropLast {n : ℕ} (γ : OneWord (n + 1)) : OneWord n := fun i => γ i.castSucc

theorem oneStepAt_dropLast {n j : ℕ} (γ : OneWord (n + 1)) (hj : j < n) :
    oneStepAt (dropLast γ) j = oneStepAt γ j := by
  simp [oneStepAt, dropLast, hj, show j < n + 1 by omega]

theorem onePosition_dropLast {n t : ℕ} (γ : OneWord (n + 1)) (ht : t ≤ n) :
    onePosition (dropLast γ) t = onePosition γ t := by
  simp only [onePosition]
  apply Finset.sum_congr rfl
  intro j hj
  exact oneStepAt_dropLast γ (by have := Finset.mem_range.mp hj; omega)

theorem oneEndpoint_dropLast {n : ℕ} (γ : OneWord (n + 1)) :
    oneEndpoint (dropLast γ) = onePosition γ n := by
  rw [oneEndpoint, onePosition_dropLast γ le_rfl]

/-- A nearest-neighbour path from zero to a level at least `k ≥ 0` visits `k`. -/
theorem exists_hit_of_nonneg_of_le_endpoint {n : ℕ} (γ : OneWord n) (k : ℤ)
    (hk : 0 ≤ k) (hle : k ≤ oneEndpoint γ) :
    ∃ t ≤ n, onePosition γ t = k := by
  induction n with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      have hend : oneEndpoint γ = 0 := by
        rw [oneEndpoint, onePosition_zero]
      rw [onePosition_zero]
      omega
  | succ n ih =>
      by_cases hprefix : k ≤ onePosition γ n
      · have hle' : k ≤ oneEndpoint (dropLast γ) := by
          rwa [oneEndpoint_dropLast]
        rcases ih (dropLast γ) hle' with ⟨t, ht, hhit⟩
        exact ⟨t, by omega, (onePosition_dropLast γ ht).symm.trans hhit⟩
      · have hstep := onePosition_succ γ (Nat.lt_succ_self n)
        have hsign : signValue (γ ⟨n, Nat.lt_succ_self n⟩) = 1 ∨
            signValue (γ ⟨n, Nat.lt_succ_self n⟩) = -1 := by
          cases γ ⟨n, Nat.lt_succ_self n⟩ <;> simp
        have hend : oneEndpoint γ = onePosition γ (n + 1) := rfl
        refine ⟨n + 1, le_rfl, ?_⟩
        rcases hsign with hsign | hsign <;> rw [hstep, hsign]
        · omega
        · omega

/-- Times at which a walk visits `k`. -/
def hitTimes {n : ℕ} (γ : OneWord n) (k : ℤ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun t => onePosition γ t = k

@[simp] theorem mem_hitTimes {n : ℕ} {γ : OneWord n} {k : ℤ} {t : ℕ} :
    t ∈ hitTimes γ k ↔ t ≤ n ∧ onePosition γ t = k := by
  simp [hitTimes]

theorem hitTimes_nonempty {n : ℕ} {γ : OneWord n} {k : ℤ}
    (hk : k ∈ oneVisited γ) : (hitTimes γ k).Nonempty := by
  rcases mem_oneVisited.mp hk with ⟨t, ht, hpos⟩
  exact ⟨t, mem_hitTimes.mpr ⟨ht, hpos⟩⟩

/-- The first time at which a walk visits a specified visited level. -/
def firstHit {n : ℕ} (γ : OneWord n) (k : ℤ) (hk : k ∈ oneVisited γ) : ℕ :=
  (hitTimes γ k).min' (hitTimes_nonempty hk)

theorem firstHit_mem {n : ℕ} (γ : OneWord n) (k : ℤ) (hk : k ∈ oneVisited γ) :
    firstHit γ k hk ∈ hitTimes γ k := by
  exact Finset.min'_mem _ _

theorem firstHit_le_length {n : ℕ} (γ : OneWord n) (k : ℤ)
    (hk : k ∈ oneVisited γ) : firstHit γ k hk ≤ n :=
  (mem_hitTimes.mp (firstHit_mem γ k hk)).1

theorem onePosition_firstHit {n : ℕ} (γ : OneWord n) (k : ℤ)
    (hk : k ∈ oneVisited γ) : onePosition γ (firstHit γ k hk) = k :=
  (mem_hitTimes.mp (firstHit_mem γ k hk)).2

theorem firstHit_minimal {n : ℕ} (γ : OneWord n) (k : ℤ)
    (hk : k ∈ oneVisited γ) {t : ℕ} (ht : t ≤ n)
    (hpos : onePosition γ t = k) : firstHit γ k hk ≤ t := by
  exact Finset.min'_le _ t (mem_hitTimes.mpr ⟨ht, hpos⟩)

theorem firstHit_eq_of_hit_of_minimal {n σ : ℕ} (γ : OneWord n) (k : ℤ)
    (hk : k ∈ oneVisited γ) (hσ : σ ≤ n) (hhit : onePosition γ σ = k)
    (hmin : ∀ t < σ, onePosition γ t ≠ k) : firstHit γ k hk = σ := by
  apply Nat.le_antisymm
  · exact firstHit_minimal γ k hk hσ hhit
  · by_contra hnot
    have hlt : firstHit γ k hk < σ := by omega
    exact hmin _ hlt (onePosition_firstHit γ k hk)

theorem firstHit_strict_minimal {n : ℕ} (γ : OneWord n) (k : ℤ)
    (hk : k ∈ oneVisited γ) {t : ℕ} (ht : t < firstHit γ k hk) :
    onePosition γ t ≠ k := by
  intro hpos
  exact (Nat.not_le_of_lt ht) (firstHit_minimal γ k hk
    (le_trans (Nat.le_of_lt ht) (firstHit_le_length γ k hk)) hpos)

/-- The first-hit time is unchanged by reflection at that time. -/
theorem firstHit_reflectAt {n : ℕ} (γ : OneWord n) (k : ℤ)
    (hk : k ∈ oneVisited γ) :
    let σ := firstHit γ k hk
    let γ' := reflectAt σ γ
    ∀ hk' : k ∈ oneVisited γ', firstHit γ' k hk' = σ := by
  dsimp only
  intro hk'
  apply firstHit_eq_of_hit_of_minimal
  · exact firstHit_le_length γ k hk
  · rw [onePosition_reflectAt_of_le γ le_rfl, onePosition_firstHit]
  · intro t ht hpos
    rw [onePosition_reflectAt_of_le γ (Nat.le_of_lt ht)] at hpos
    exact firstHit_strict_minimal γ k hk ht hpos

end ClosedWalk
end SquareMaximality
