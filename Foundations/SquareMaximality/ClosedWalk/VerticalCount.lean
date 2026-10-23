module

public import SquareMaximality.ClosedWalk.PlaneFirstHit
public import Mathlib.Data.Nat.Choose.Vandermonde

@[expose] public section

set_option autoImplicit false

/-!
# Words with zero vertical displacement

The two-sign encoding identifies zero vertical displacement with equality of
the two positive-sign counts.  Vandermonde's finite identity then gives
`choose (2n) n` words.
-/

namespace SquareMaximality
namespace ClosedWalk

/-- A word has zero vertical displacement. -/
def VerticalZero {n : ℕ} (ω : Word n) : Prop := (total ω).2 = 0

instance {n : ℕ} (ω : Word n) : Decidable (VerticalZero ω) :=
  inferInstanceAs (Decidable ((total ω).2 = 0))

theorem verticalZero_iff_sign_card_eq {n : ℕ} (ω : Word n) :
    VerticalZero ω ↔ (firstSignSet ω).card = (secondSignSet ω).card := by
  have hfirst := first_sign_sum_eq ω
  have hsecond := second_sign_sum_eq ω
  have hfirstCard := first_sign_sum_card ω
  have hsecondCard := second_sign_sum_card ω
  constructor
  · intro hy
    have hy' : (total ω).2 = 0 := hy
    have hc : ((firstSignSet ω).card : ℤ) = (secondSignSet ω).card := by omega
    exact_mod_cast hc
  · intro hc
    have hc' : ((firstSignSet ω).card : ℤ) = (secondSignSet ω).card := by
      exact_mod_cast hc
    change (total ω).2 = 0
    omega

/-- Pairs of subsets having the same cardinality. -/
abbrev EqualCardPairs (n : ℕ) :=
  { p : Finset (Fin n) × Finset (Fin n) // p.1.card = p.2.card }

/-- Equal-cardinality pairs, grouped by their common cardinality. -/
abbrev CardPairSigma (n : ℕ) :=
  Σ k : Fin (n + 1),
    { s : Finset (Fin n) // s.card = k.1 } × { s : Finset (Fin n) // s.card = k.1 }

def equalCardPairsEquivSigma (n : ℕ) : EqualCardPairs n ≃ CardPairSigma n where
  toFun p := by
    let k : Fin (n + 1) := ⟨p.1.1.card, by
      exact Nat.lt_succ_of_le (by simpa using Finset.card_le_univ p.1.1)⟩
    exact ⟨k, ⟨⟨p.1.1, rfl⟩, ⟨p.1.2, p.2.symm⟩⟩⟩
  invFun p := ⟨(p.2.1.1, p.2.2.1), p.2.1.2.trans p.2.2.2.symm⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv p := by
    rcases p with ⟨⟨k, hk⟩, ⟨⟨s, hs⟩, ⟨t, ht⟩⟩⟩
    dsimp
    have hsk : s.card = k := hs
    subst k
    rfl

/-- Zero-vertical words are equivalent to equal-cardinality sign-set pairs. -/
def verticalZeroEquivEqualCardPairs (n : ℕ) :
    { ω : Word n // VerticalZero ω } ≃ EqualCardPairs n :=
  (wordEquivSignSets n).subtypeEquiv fun ω => verticalZero_iff_sign_card_eq ω

/-- The exact count of words with zero vertical displacement. -/
theorem card_verticalZero (n : ℕ) :
    Fintype.card { ω : Word n // VerticalZero ω } = Nat.choose (2 * n) n := by
  rw [Fintype.card_congr ((verticalZeroEquivEqualCardPairs n).trans
    (equalCardPairsEquivSigma n))]
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_finset_len, Fintype.card_fin]
  calc
    (∑ k : Fin (n + 1), n.choose k.1 * n.choose k.1) =
        ∑ k ∈ Finset.range (n + 1), n.choose k * n.choose k :=
      Fin.sum_univ_eq_sum_range (fun k => n.choose k * n.choose k) (n + 1)
    _ = Nat.choose (2 * n) n := by simpa [pow_two] using Nat.sum_range_choose_sq n

end ClosedWalk
end SquareMaximality
