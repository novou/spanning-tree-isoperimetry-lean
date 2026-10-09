import SquareMaximality.ClosedWalk.FirstHit

set_option autoImplicit false

/-!
# Marked bridges and unrestricted words

The reflection principle is most economical as one global finite equivalence:
a bridge together with one of its visited levels is equivalent to an arbitrary
sign word of the same even length.  This avoids any appeal to an infinite
series.
-/

namespace SquareMaximality
namespace ClosedWalk

/-- Negate every step of a one-dimensional word. -/
def negateOne {n : ℕ} (γ : OneWord n) : OneWord n := fun i => !γ i

@[simp] theorem negateOne_involutive {n : ℕ} :
    Function.Involutive (negateOne : OneWord n → OneWord n) := by
  intro γ
  funext i
  simp [negateOne]

theorem oneStepAt_negateOne {n j : ℕ} (γ : OneWord n) :
    oneStepAt (negateOne γ) j = -oneStepAt γ j := by
  by_cases hj : j < n <;> simp [oneStepAt, negateOne, hj]

theorem onePosition_negateOne {n t : ℕ} (γ : OneWord n) :
    onePosition (negateOne γ) t = -onePosition γ t := by
  simp only [onePosition, oneStepAt_negateOne, Finset.sum_neg_distrib]

theorem oneEndpoint_negateOne {n : ℕ} (γ : OneWord n) :
    oneEndpoint (negateOne γ) = -oneEndpoint γ := by
  simp [oneEndpoint, onePosition_negateOne]

/-- Half the endpoint of an even-length sign word. -/
def midLevel (a : ℕ) (γ : OneWord (2 * a)) : ℤ :=
  ((positiveSet γ).card : ℤ) - a

theorem oneEndpoint_eq_two_mul_midLevel (a : ℕ) (γ : OneWord (2 * a)) :
    oneEndpoint γ = 2 * midLevel a γ := by
  rw [oneEndpoint_eq_card]
  simp only [midLevel]
  push_cast
  ring

/-- Every even-length word visits half of its endpoint. -/
theorem midLevel_mem_oneVisited (a : ℕ) (γ : OneWord (2 * a)) :
    midLevel a γ ∈ oneVisited γ := by
  let k := midLevel a γ
  by_cases hk : 0 ≤ k
  · apply mem_oneVisited.mpr
    apply exists_hit_of_nonneg_of_le_endpoint γ k hk
    rw [oneEndpoint_eq_two_mul_midLevel]
    dsimp only [k]
    omega
  · have hkneg : 0 ≤ -k := by omega
    have hle : -k ≤ oneEndpoint (negateOne γ) := by
      rw [oneEndpoint_negateOne, oneEndpoint_eq_two_mul_midLevel]
      dsimp only [k]
      omega
    rcases exists_hit_of_nonneg_of_le_endpoint (negateOne γ) (-k) hkneg hle with
      ⟨t, ht, hpos⟩
    apply mem_oneVisited.mpr
    refine ⟨t, ht, ?_⟩
    rw [onePosition_negateOne] at hpos
    omega

/-- A bridge with a distinguished visited level. -/
abbrev MarkedBridge (a : ℕ) :=
  Σ γ : { γ : OneWord (2 * a) // IsBridge γ },
    { k : ℤ // k ∈ oneVisited γ.1 }

/-- Reflect a marked bridge after its first visit to the marked level. -/
def markedBridgeToWord (a : ℕ) : MarkedBridge a → OneWord (2 * a)
  | ⟨γ, k⟩ => reflectAt (firstHit γ.1 k.1 k.2) γ.1

/-- Turn an arbitrary even-length word into a marked bridge by reflecting it
after its first visit to half of its endpoint. -/
def wordToMarkedBridge (a : ℕ) (δ : OneWord (2 * a)) : MarkedBridge a := by
  let k := midLevel a δ
  have hk : k ∈ oneVisited δ := midLevel_mem_oneVisited a δ
  let σ := firstHit δ k hk
  let γ := reflectAt σ δ
  have hbridge : IsBridge γ := by
    rw [IsBridge, oneEndpoint_reflectAt δ (firstHit_le_length δ k hk),
      onePosition_firstHit δ k hk, oneEndpoint_eq_two_mul_midLevel a δ]
    dsimp only [k]
    ring
  have hvisit : k ∈ oneVisited γ := by
    apply mem_oneVisited.mpr
    refine ⟨σ, firstHit_le_length δ k hk, ?_⟩
    rw [onePosition_reflectAt_of_le δ le_rfl, onePosition_firstHit]
  exact ⟨⟨γ, hbridge⟩, ⟨k, hvisit⟩⟩

private theorem midLevel_eq_of_endpoint {a : ℕ} {δ : OneWord (2 * a)} {k : ℤ}
    (h : oneEndpoint δ = 2 * k) : midLevel a δ = k := by
  rw [oneEndpoint_eq_two_mul_midLevel] at h
  omega

theorem markedBridgeToWord_wordToMarkedBridge (a : ℕ) (δ : OneWord (2 * a)) :
    markedBridgeToWord a (wordToMarkedBridge a δ) = δ := by
  let k := midLevel a δ
  have hk : k ∈ oneVisited δ := midLevel_mem_oneVisited a δ
  let σ := firstHit δ k hk
  let γ := reflectAt σ δ
  have hvisit : k ∈ oneVisited γ := by
    apply mem_oneVisited.mpr
    refine ⟨σ, firstHit_le_length δ k hk, ?_⟩
    rw [onePosition_reflectAt_of_le δ le_rfl, onePosition_firstHit]
  have hfirst : firstHit γ k hvisit = σ := firstHit_reflectAt δ k hk hvisit
  change reflectAt (firstHit γ k hvisit) γ = δ
  rw [hfirst]
  exact reflectAt_involutive δ

theorem wordToMarkedBridge_markedBridgeToWord (a : ℕ) (x : MarkedBridge a) :
    wordToMarkedBridge a (markedBridgeToWord a x) = x := by
  rcases x with ⟨⟨γ, hbridge⟩, ⟨k, hk⟩⟩
  let σ := firstHit γ k hk
  let δ := reflectAt σ γ
  have hend : oneEndpoint δ = 2 * k := by
    exact oneEndpoint_reflectAt_of_bridge_of_hit (firstHit_le_length γ k hk)
      hbridge (onePosition_firstHit γ k hk)
  have hmid : midLevel a δ = k := midLevel_eq_of_endpoint hend
  have hkδ : k ∈ oneVisited δ := by
    apply mem_oneVisited.mpr
    refine ⟨σ, firstHit_le_length γ k hk, ?_⟩
    rw [onePosition_reflectAt_of_le γ le_rfl, onePosition_firstHit]
  have hfirst : firstHit δ k hkδ = σ := firstHit_reflectAt γ k hk hkδ
  have hword : reflectAt (firstHit δ k hkδ) δ = γ := by
    rw [hfirst]
    exact reflectAt_involutive γ
  have hkmid : midLevel a δ ∈ oneVisited δ := midLevel_mem_oneVisited a δ
  have hfirstmid : firstHit δ (midLevel a δ) hkmid = σ := by
    apply firstHit_eq_of_hit_of_minimal
    · exact firstHit_le_length γ k hk
    · calc
        onePosition δ σ = onePosition γ σ := onePosition_reflectAt_of_le γ le_rfl
        _ = k := onePosition_firstHit γ k hk
        _ = midLevel a δ := hmid.symm
    · intro t ht hpos
      have hpos' : onePosition γ t = k := by
        rw [← hmid, ← hpos]
        exact (onePosition_reflectAt_of_le γ (Nat.le_of_lt ht)).symm
      exact firstHit_strict_minimal γ k hk ht hpos'
  have hwordmid : reflectAt (firstHit δ (midLevel a δ) hkmid) δ = γ := by
    rw [hfirstmid]
    exact reflectAt_involutive γ
  change wordToMarkedBridge a δ = ⟨⟨γ, hbridge⟩, ⟨k, hk⟩⟩
  have hfst : (wordToMarkedBridge a δ).fst = ⟨γ, hbridge⟩ := by
    apply Subtype.ext
    change reflectAt (firstHit δ (midLevel a δ) _) δ = γ
    exact hwordmid
  apply Sigma.ext hfst
  · apply (Subtype.heq_iff_coe_eq (fun z => by
      have hw := congrArg Subtype.val hfst
      change (z ∈ oneVisited (wordToMarkedBridge a δ).fst.1) ↔ z ∈ oneVisited γ
      rw [hw])).2
    exact hmid

/-- First-hit reflection as an exact finite equivalence. -/
def markedBridgeEquivWord (a : ℕ) : MarkedBridge a ≃ OneWord (2 * a) where
  toFun := markedBridgeToWord a
  invFun := wordToMarkedBridge a
  left_inv := wordToMarkedBridge_markedBridgeToWord a
  right_inv := markedBridgeToWord_wordToMarkedBridge a

/-- Cardinality form of the reflection/visited-level identity. -/
theorem card_markedBridge (a : ℕ) : Fintype.card (MarkedBridge a) = 2 ^ (2 * a) := by
  rw [Fintype.card_congr (markedBridgeEquivWord a), Fintype.card_fun]
  simp

end ClosedWalk
end SquareMaximality
