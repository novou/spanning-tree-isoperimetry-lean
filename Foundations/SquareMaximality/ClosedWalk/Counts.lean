import SquareMaximality.ClosedWalk.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
# Counting finite closed square-lattice words

The two-sign encoding turns one square-lattice word into two Boolean words.
The original word is closed exactly when both Boolean words have equally many
positive and negative signs.  This gives a literal finite equivalence and the
coefficient identity `w_(2a) = choose (2a) a ^ 2`; it also proves that the odd
coefficients vanish.
-/

namespace SquareMaximality
namespace ClosedWalk

/-- A sign, regarded as `+1` or `-1`. -/
def signValue : Bool → ℤ
  | true => 1
  | false => -1

@[simp] theorem signValue_true : signValue true = 1 := rfl
@[simp] theorem signValue_false : signValue false = -1 := rfl

theorem sum_signValue_eq_card {n : ℕ} (f : Fin n → Bool) :
    (∑ i, signValue (f i)) =
      2 * ((Finset.univ.filter fun i => f i).card : ℤ) - n := by
  classical
  rw [show (∑ i, signValue (f i)) =
      ∑ i, if f i then (1 : ℤ) else -1 by
        apply Finset.sum_congr rfl
        intro i _
        cases f i <;> rfl]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg, mul_one]
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun i => f i)
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- The first transformed sign sum is `x+y` of the total displacement. -/
theorem first_sign_sum_eq {n : ℕ} (ω : Word n) :
    (∑ i, signValue (stepSignEquiv (ω i)).1) = (total ω).1 + (total ω).2 := by
  calc
    (∑ i, signValue (stepSignEquiv (ω i)).1) =
        ∑ i, ((ω i).vector.1 + (ω i).vector.2) := by
          apply Finset.sum_congr rfl
          intro i _
          cases ω i <;> rfl
    _ = (∑ i, (ω i).vector.1) + ∑ i, (ω i).vector.2 :=
      Finset.sum_add_distrib
    _ = (total ω).1 + (total ω).2 := by
      rw [total, Prod.fst_sum, Prod.snd_sum]

/-- The second transformed sign sum is `x-y` of the total displacement. -/
theorem second_sign_sum_eq {n : ℕ} (ω : Word n) :
    (∑ i, signValue (stepSignEquiv (ω i)).2) = (total ω).1 - (total ω).2 := by
  calc
    (∑ i, signValue (stepSignEquiv (ω i)).2) =
        ∑ i, ((ω i).vector.1 - (ω i).vector.2) := by
          apply Finset.sum_congr rfl
          intro i _
          cases ω i <;> rfl
    _ = (∑ i, (ω i).vector.1) - ∑ i, (ω i).vector.2 := by
      simp only [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = (total ω).1 - (total ω).2 := by
      rw [total, Prod.fst_sum, Prod.snd_sum]

theorem first_sign_sum_card {n : ℕ} (ω : Word n) :
    (∑ i, signValue (stepSignEquiv (ω i)).1) =
      2 * ((firstSignSet ω).card : ℤ) - n := by
  simpa only [firstSignSet] using
    (sum_signValue_eq_card (fun i => (stepSignEquiv (ω i)).1))

theorem second_sign_sum_card {n : ℕ} (ω : Word n) :
    (∑ i, signValue (stepSignEquiv (ω i)).2) =
      2 * ((secondSignSet ω).card : ℤ) - n := by
  simpa only [secondSignSet] using
    (sum_signValue_eq_card (fun i => (stepSignEquiv (ω i)).2))

/-- A subset of `n` positions is balanced when positives and negatives agree. -/
def IsBalanced {n : ℕ} (s : Finset (Fin n)) : Prop := 2 * s.card = n

theorem isClosed_iff_sign_sets_balanced {n : ℕ} (ω : Word n) :
    IsClosed ω ↔ IsBalanced (firstSignSet ω) ∧ IsBalanced (secondSignSet ω) := by
  constructor
  · intro h
    have hxy : (total ω).1 = 0 ∧ (total ω).2 = 0 := by
      constructor
      · simpa using congrArg Prod.fst h
      · simpa using congrArg Prod.snd h
    constructor
    · have hz : 2 * ((firstSignSet ω).card : ℤ) - n = 0 := by
        rw [← first_sign_sum_card, first_sign_sum_eq, hxy.1, hxy.2]
        simp
      exact_mod_cast (show 2 * (firstSignSet ω).card = n by omega)
    · have hz : 2 * ((secondSignSet ω).card : ℤ) - n = 0 := by
        rw [← second_sign_sum_card, second_sign_sum_eq, hxy.1, hxy.2]
        simp
      exact_mod_cast (show 2 * (secondSignSet ω).card = n by omega)
  · rintro ⟨hfirst, hsecond⟩
    have hfirstZ : 2 * ((firstSignSet ω).card : ℤ) - n = 0 := by
      rw [sub_eq_zero]
      exact_mod_cast hfirst
    have hsecondZ : 2 * ((secondSignSet ω).card : ℤ) - n = 0 := by
      rw [sub_eq_zero]
      exact_mod_cast hsecond
    have hsum : (total ω).1 + (total ω).2 = 0 := by
      rw [← first_sign_sum_eq, first_sign_sum_card]
      exact hfirstZ
    have hdiff : (total ω).1 - (total ω).2 = 0 := by
      rw [← second_sign_sum_eq, second_sign_sum_card]
      exact hsecondZ
    apply Prod.ext
    · change (total ω).1 = 0
      omega
    · change (total ω).2 = 0
      omega

private theorem balanced_even_iff_card {a : ℕ} (s : Finset (Fin (2 * a))) :
    IsBalanced s ↔ s.card = a := by
  simp only [IsBalanced]
  omega

/-- A concrete finite equivalence underlying the central-binomial-square count. -/
def closedEvenEquiv (a : ℕ) :
    { ω : Word (2 * a) // IsClosed ω } ≃
      { s : Finset (Fin (2 * a)) // s.card = a } ×
        { s : Finset (Fin (2 * a)) // s.card = a } :=
  ((wordEquivSignSets (2 * a)).subtypeEquiv fun ω => by
      rw [isClosed_iff_sign_sets_balanced]
      exact and_congr (balanced_even_iff_card _) (balanced_even_iff_card _)).trans
    Equiv.subtypeProdEquivProd

private theorem closedWordCount_eq_subtype_card (n : ℕ) :
    closedWordCount n = Fintype.card { ω : Word n // IsClosed ω } := by
  symm
  exact Fintype.subtype_card (closedWords n) (fun ω => mem_closedWords)

/-- The exact even coefficient formula `w_(2a) = choose(2a,a)^2`. -/
theorem closedWordCount_even (a : ℕ) :
    closedWordCount (2 * a) = (Nat.choose (2 * a) a) ^ 2 := by
  rw [closedWordCount_eq_subtype_card]
  rw [Fintype.card_congr (closedEvenEquiv a), Fintype.card_prod]
  simp only [Fintype.card_finset_len, Fintype.card_fin]
  exact (pow_two _).symm

/-- There is no closed nearest-neighbour word of odd length. -/
theorem closedWords_odd_eq_empty (a : ℕ) : closedWords (2 * a + 1) = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨ω, hω⟩
  have hbalanced := (isClosed_iff_sign_sets_balanced ω).mp (mem_closedWords.mp hω)
  simp only [IsBalanced] at hbalanced
  omega

/-- Equivalently, every odd coefficient `w_(2a+1)` vanishes. -/
theorem closedWordCount_odd (a : ℕ) : closedWordCount (2 * a + 1) = 0 := by
  simp [closedWordCount, closedWords_odd_eq_empty]

end ClosedWalk
end SquareMaximality
