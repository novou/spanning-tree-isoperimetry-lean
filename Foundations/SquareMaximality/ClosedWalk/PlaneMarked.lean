import SquareMaximality.ClosedWalk.VerticalCount

set_option autoImplicit false

/-!
# Marked closed square-lattice words

First-hit horizontal reflection gives an exact finite equivalence between a
closed word with a marked visited horizontal level and a word with zero
vertical displacement.  Its cardinality is the central binomial coefficient.
-/

namespace SquareMaximality
namespace ClosedWalk

/-- Half of the horizontal endpoint of an even word with zero vertical endpoint. -/
def midX (a : ℕ) (ω : Word (2 * a)) : ℤ := ((firstSignSet ω).card : ℤ) - a

theorem total_fst_eq_two_mul_midX_of_verticalZero {a : ℕ} {ω : Word (2 * a)}
    (hy : VerticalZero ω) : (total ω).1 = 2 * midX a ω := by
  calc
    (total ω).1 = (total ω).1 + (total ω).2 := by rw [hy]; simp
    _ = ∑ i, signValue (stepSignEquiv (ω i)).1 := (first_sign_sum_eq ω).symm
    _ = 2 * ((firstSignSet ω).card : ℤ) - (2 * a : ℕ) := first_sign_sum_card ω
    _ = 2 * midX a ω := by simp only [midX]; push_cast; ring

/-- A zero-vertical even word visits half of its horizontal endpoint. -/
theorem midX_mem_visitedX {a : ℕ} {ω : Word (2 * a)} (hy : VerticalZero ω) :
    midX a ω ∈ visitedX ω := by
  let k := midX a ω
  by_cases hk : 0 ≤ k
  · apply mem_visitedX.mpr
    apply exists_x_hit_of_nonneg_of_le_total ω k hk
    rw [total_fst_eq_two_mul_midX_of_verticalZero hy]
    dsimp only [k]
    omega
  · have hk' : 0 ≤ -k := by omega
    have hle : -k ≤ (total (reflectXAt 0 ω)).1 := by
      rw [total_reflectXAt_fst ω (Nat.zero_le _), position_zero,
        total_fst_eq_two_mul_midX_of_verticalZero hy]
      dsimp only [k]
      omega
    rcases exists_x_hit_of_nonneg_of_le_total (reflectXAt 0 ω) (-k) hk' hle with
      ⟨t, ht, hpos⟩
    apply mem_visitedX.mpr
    refine ⟨t, ht, ?_⟩
    rw [position_reflectXAt_zero_fst] at hpos
    omega

/-- A closed word with one distinguished visited horizontal level. -/
abbrev MarkedClosedX (a : ℕ) :=
  Σ ω : { ω : Word (2 * a) // IsClosed ω }, { k : ℤ // k ∈ visitedX ω.1 }

/-- Reflect a marked closed word after its first visit to the marked level. -/
def markedClosedXToVerticalZero (a : ℕ) :
    MarkedClosedX a → { ω : Word (2 * a) // VerticalZero ω }
  | ⟨ω, k⟩ => ⟨reflectXAt (firstHitX ω.1 k.1 k.2) ω.1, by
      rw [VerticalZero, total_reflectXAt_snd]
      have h := ω.2
      exact congrArg Prod.snd h⟩

/-- Inverse construction: reflect a zero-vertical word at the first visit to
half of its horizontal endpoint. -/
def verticalZeroToMarkedClosedX (a : ℕ)
    (δ : { δ : Word (2 * a) // VerticalZero δ }) : MarkedClosedX a := by
  let k := midX a δ.1
  have hk : k ∈ visitedX δ.1 := midX_mem_visitedX δ.2
  let σ := firstHitX δ.1 k hk
  let ω := reflectXAt σ δ.1
  have hclosed : IsClosed ω := by
    apply Prod.ext
    · change (total ω).1 = 0
      rw [total_reflectXAt_fst δ.1 (firstHitX_le_length δ.1 k hk),
        position_firstHitX δ.1 k hk, total_fst_eq_two_mul_midX_of_verticalZero δ.2]
      dsimp only [k]
      ring
    · change (total ω).2 = 0
      rw [total_reflectXAt_snd]
      exact δ.2
  have hvisit : k ∈ visitedX ω := by
    apply mem_visitedX.mpr
    refine ⟨σ, firstHitX_le_length δ.1 k hk, ?_⟩
    rw [position_reflectXAt_of_le δ.1 le_rfl, position_firstHitX]
  exact ⟨⟨ω, hclosed⟩, ⟨k, hvisit⟩⟩

theorem markedClosedXToVerticalZero_verticalZeroToMarkedClosedX (a : ℕ)
    (δ : { δ : Word (2 * a) // VerticalZero δ }) :
    markedClosedXToVerticalZero a (verticalZeroToMarkedClosedX a δ) = δ := by
  apply Subtype.ext
  let k := midX a δ.1
  have hk : k ∈ visitedX δ.1 := midX_mem_visitedX δ.2
  let σ := firstHitX δ.1 k hk
  let ω := reflectXAt σ δ.1
  have hvisit : k ∈ visitedX ω := by
    apply mem_visitedX.mpr
    refine ⟨σ, firstHitX_le_length δ.1 k hk, ?_⟩
    rw [position_reflectXAt_of_le δ.1 le_rfl, position_firstHitX]
  have hfirst : firstHitX ω k hvisit = σ := firstHitX_reflectXAt δ.1 k hk hvisit
  change reflectXAt (firstHitX ω k hvisit) ω = δ.1
  rw [hfirst]
  exact reflectXAt_involutive δ.1

private theorem midX_eq_of_total {a : ℕ} {δ : Word (2 * a)} {k : ℤ}
    (hy : VerticalZero δ) (hx : (total δ).1 = 2 * k) : midX a δ = k := by
  rw [total_fst_eq_two_mul_midX_of_verticalZero hy] at hx
  omega

theorem verticalZeroToMarkedClosedX_markedClosedXToVerticalZero (a : ℕ)
    (x : MarkedClosedX a) :
    verticalZeroToMarkedClosedX a (markedClosedXToVerticalZero a x) = x := by
  rcases x with ⟨⟨ω, hclosed⟩, ⟨k, hk⟩⟩
  let σ := firstHitX ω k hk
  let δ := reflectXAt σ ω
  have hy : VerticalZero δ := by
    rw [VerticalZero, total_reflectXAt_snd]
    exact congrArg Prod.snd hclosed
  have hx : (total δ).1 = 2 * k := by
    rw [total_reflectXAt_fst ω (firstHitX_le_length ω k hk),
      position_firstHitX ω k hk]
    have hx0 : (total ω).1 = 0 := congrArg Prod.fst hclosed
    rw [hx0]
    ring
  have hmid : midX a δ = k := midX_eq_of_total hy hx
  have hkδ : k ∈ visitedX δ := by
    apply mem_visitedX.mpr
    refine ⟨σ, firstHitX_le_length ω k hk, ?_⟩
    rw [position_reflectXAt_of_le ω le_rfl, position_firstHitX]
  have hkmid : midX a δ ∈ visitedX δ := midX_mem_visitedX hy
  have hfirstmid : firstHitX δ (midX a δ) hkmid = σ := by
    apply firstHitX_eq_of_hit_of_minimal
    · exact firstHitX_le_length ω k hk
    · calc
        (position δ σ).1 = (position ω σ).1 :=
          congrArg Prod.fst (position_reflectXAt_of_le ω le_rfl)
        _ = k := position_firstHitX ω k hk
        _ = midX a δ := hmid.symm
    · intro t ht hpos
      have hpos' : (position ω t).1 = k := by
        rw [← hmid, ← hpos]
        exact congrArg Prod.fst (position_reflectXAt_of_le ω (Nat.le_of_lt ht)).symm
      exact firstHitX_strict_minimal ω k hk ht hpos'
  have hwordmid : reflectXAt (firstHitX δ (midX a δ) hkmid) δ = ω := by
    rw [hfirstmid]
    exact reflectXAt_involutive ω
  change verticalZeroToMarkedClosedX a ⟨δ, hy⟩ = ⟨⟨ω, hclosed⟩, ⟨k, hk⟩⟩
  have hfst : (verticalZeroToMarkedClosedX a ⟨δ, hy⟩).fst = ⟨ω, hclosed⟩ := by
    apply Subtype.ext
    change reflectXAt (firstHitX δ (midX a δ) _) δ = ω
    exact hwordmid
  apply Sigma.ext hfst
  · apply (Subtype.heq_iff_coe_eq (fun z => by
      have hw := congrArg Subtype.val hfst
      change (z ∈ visitedX (verticalZeroToMarkedClosedX a ⟨δ, hy⟩).fst.1) ↔
        z ∈ visitedX ω
      rw [hw])).2
    exact hmid

/-- Exact finite marked-word reflection equivalence. -/
def markedClosedXEquivVerticalZero (a : ℕ) :
    MarkedClosedX a ≃ { ω : Word (2 * a) // VerticalZero ω } where
  toFun := markedClosedXToVerticalZero a
  invFun := verticalZeroToMarkedClosedX a
  left_inv := verticalZeroToMarkedClosedX_markedClosedXToVerticalZero a
  right_inv := markedClosedXToVerticalZero_verticalZeroToMarkedClosedX a

theorem card_markedClosedX (a : ℕ) :
    Fintype.card (MarkedClosedX a) = Nat.choose (2 * (2 * a)) (2 * a) := by
  rw [Fintype.card_congr (markedClosedXEquivVerticalZero a), card_verticalZero]

private theorem card_markedClosedX_eq_sum (a : ℕ) :
    Fintype.card (MarkedClosedX a) =
      ∑ ω : { ω : Word (2 * a) // IsClosed ω }, (visitedX ω.1).card := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro ω _
  exact Fintype.subtype_card (visitedX ω.1) (fun _ => Iff.rfl)

theorem closedSubtype_visitedX_sum (a : ℕ) :
    (∑ ω : { ω : Word (2 * a) // IsClosed ω }, (visitedX ω.1).card) =
      Nat.choose (2 * (2 * a)) (2 * a) := by
  rw [← card_markedClosedX_eq_sum, card_markedClosedX]

def closedSubtypeEquivMem (n : ℕ) :
    { ω : Word n // IsClosed ω } ≃ { ω : Word n // ω ∈ closedWords n } where
  toFun ω := ⟨ω.1, mem_closedWords.mpr ω.2⟩
  invFun ω := ⟨ω.1, mem_closedWords.mp ω.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact finite closed-word horizontal-span coefficient identity. -/
theorem closedWords_spanX_add_one_sum_even (a : ℕ) :
    ∑ ω ∈ closedWords (2 * a), (spanX ω + 1) =
      Nat.choose (2 * (2 * a)) (2 * a) := by
  calc
    (∑ ω ∈ closedWords (2 * a), (spanX ω + 1)) =
        ∑ ω ∈ closedWords (2 * a), (visitedX ω).card := by
      apply Finset.sum_congr rfl
      intro ω _
      exact (card_visitedX_eq_spanX_add_one ω).symm
    _ = ∑ ω : { ω : Word (2 * a) // ω ∈ closedWords (2 * a) },
          (visitedX ω.1).card := (Finset.sum_coe_sort _ _).symm
    _ = ∑ ω : { ω : Word (2 * a) // IsClosed ω }, (visitedX ω.1).card := by
      symm
      apply Fintype.sum_equiv (closedSubtypeEquivMem (2 * a))
      intro ω
      rfl
    _ = Nat.choose (2 * (2 * a)) (2 * a) := closedSubtype_visitedX_sum a

/-- Odd-length closed-word span sum vanishes because there are no closed words. -/
theorem closedWords_spanX_add_one_sum_odd (a : ℕ) :
    ∑ ω ∈ closedWords (2 * a + 1), (spanX ω + 1) = 0 := by
  rw [closedWords_odd_eq_empty]
  simp

end ClosedWalk
end SquareMaximality
