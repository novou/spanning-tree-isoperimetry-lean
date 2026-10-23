module

public import SpanningTreeIsoperimetry.SmallMaximumValue

@[expose] public section

/-! Every maximizing opposite pair at a small cardinality is one of the five
actual exceptional domains, up to lattice congruence. -/
namespace SpanningTreeIsoperimetry.SmallPairClassification
open Ferrers CornerEnergy CornerPrimalDomains CornerProfileNormalization SmallMaximumValue
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def oppositeDomain (N : ℕ) : Domain :=
  if N=7 then ConcreteCounts.winner7Domain
  else if N=10 then cornerPrimal 2 3 SmallTenComparison.singletonPair
  else if N=13 then cornerPrimal 3 3 SmallPrimalComparisons.oppositeFamily
  else if N=14 then ConcreteCounts.winner14Domain
  else SmallCases.winner17Domain

def ExceptionalSize (N : ℕ) : Prop := N=7 ∨ N=10 ∨ N=13 ∨ N=14 ∨ N=17

theorem square_pair_congruent (v : Bool) :
    Congruent (cornerPrimal 3 3 (SeventeenPrimalComparisons.pairFamily v))
      (cornerPrimal 3 3 SmallPrimalComparisons.oppositeFamily) := by
  cases v
  · have he : SeventeenPrimalComparisons.pairFamily false=SmallPrimalComparisons.oppositeFamily := by decide +kernel
    rw [he]
    exact congruent_refl _
  · have hf := pair_family_fit (R := 3) (S := 3)
      (by decide : (true,true)≠(false,false)) (stripDiagram_ferrers 2 true)
      (horizontalStrip_isFerrers 1) (by decide) (by decide)
    have hc := cornerPrimal_transpose_congruent hf
    change Congruent (cornerPrimal 3 3 (SeventeenPrimalComparisons.pairFamily true))
      (cornerPrimal 3 3 (transposedFamily (SeventeenPrimalComparisons.pairFamily true))) at hc
    have he : transposedFamily (SeventeenPrimalComparisons.pairFamily true)=
      SmallPrimalComparisons.oppositeFamily := by decide +kernel
    rwa [he] at hc

theorem singleton_pair_form {N R S : ℕ} (hN : 0<N) (hsmall : N≤17) (hRS : R≤S)
    (harea : N+2=(R+1)*(S+1)) (hk : 2≤R)
    (hsum : (R+1)+(S+1)=minimumSideSum N)
    (hm : IsMaximizer (cornerPrimal R S SmallTenComparison.singletonPair)) :
    ExceptionalSize N ∧ Congruent (cornerPrimal R S SmallTenComparison.singletonPair) (oppositeDomain N) := by
  have hh := small_hulls hN hsmall hRS harea hk le_rfl hsum
  have hc : (R=2 ∧ S=2) ∨ (R=2 ∧ S=3) ∨ (R=2 ∧ S=4) ∨ (R=3 ∧ S=3) := by omega
  rcases hc with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · have hn : N=7 := by omega
    subst N
    constructor
    · exact Or.inl rfl
    · simp only [oppositeDomain,ite_true,SingletonPairComparisons.singleton_pair_seven]
      exact congruent_refl _
  · have hn : N=10 := by omega
    subst N
    constructor
    · exact Or.inr (Or.inl rfl)
    · norm_num [oppositeDomain]
      exact congruent_refl _
  · exact False.elim (SingletonPairComparisons.thirteen_not_maximal hm)
  · have hn : N=14 := by omega
    subst N
    constructor
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · norm_num [oppositeDomain]
      rw [SingletonPairComparisons.singleton_pair_fourteen]
      exact congruent_refl _

theorem two_one_pair_form {N R S : ℕ} (hN : 0<N) (hsmall : N≤17) (hRS : R≤S)
    (harea : N+3=(R+1)*(S+1)) (hk : 3≤R)
    (hsum : (R+1)+(S+1)=minimumSideSum N) (v : Bool)
    (hm : IsMaximizer (cornerPrimal R S (SeventeenPrimalComparisons.pairFamily v))) :
    ExceptionalSize N ∧ Congruent (cornerPrimal R S (SeventeenPrimalComparisons.pairFamily v)) (oppositeDomain N) := by
  rcases three_hulls hN hsmall hRS harea hk hsum with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · have hn : N=13 := by omega
    subst N
    constructor
    · exact Or.inr (Or.inr (Or.inl rfl))
    · norm_num [oppositeDomain]
      exact square_pair_congruent v
  · have hn : N=17 := by omega
    subst N
    cases v
    · exact False.elim (SeventeenPrimalComparisons.other_candidates_not_maximal.1 hm)
    · constructor
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · norm_num [oppositeDomain]
        have he : cornerPrimal 3 4 (SeventeenPrimalComparisons.pairFamily true)=SmallCases.winner17Domain := by decide +kernel
        rw [he]
        exact congruent_refl _

theorem opposite_pair_form {N R S a b : ℕ} (hN : 0<N) (hsmall : N≤17) (hRS : R≤S)
    (ha : 0<a) (hb : 0<b) (hab : a+b≤3)
    (hR : a+b≤R) (hS : a+b≤S) (harea : N+(a+b)=(R+1)*(S+1))
    (hsum : (R+1)+(S+1)=minimumSideSum N) (c : Corner) (u v : Bool)
    (hm : IsMaximizer (cornerPrimal R S (twoCornerFamily c (opposite c)
      (stripDiagram a u) (stripDiagram b v)))) :
    ExceptionalSize N ∧ Congruent (cornerPrimal R S (twoCornerFamily c (opposite c)
      (stripDiagram a u) (stripDiagram b v))) (oppositeDomain N) := by
  have hn := pair_normalization (R := R) (S := S) c
    (stripDiagram_ferrers a u) (stripDiagram_ferrers b v)
    (by simpa only [stripDiagram_card] using hR) (by simpa only [stripDiagram_card] using hS)
  have ha2 : a≤2 := by omega
  have hb2 : b≤2 := by omega
  interval_cases a <;> interval_cases b
  · simp only [stripDiagram_one] at hn hm ⊢
    obtain ⟨hsize,hform⟩ := singleton_pair_form hN hsmall hRS harea hR hsum (hn.isMaximizer_iff.mp hm)
    exact ⟨hsize,hn.trans hform⟩
  · simp only [stripDiagram_one] at hn hm ⊢
    have ht := pair_swap (R := R) (S := S) (horizontalStrip_isFerrers 1) (stripDiagram_ferrers 2 v)
      (by simpa only [card_horizontalStrip,stripDiagram_card] using hR)
      (by simpa only [card_horizontalStrip,stripDiagram_card] using hS)
    have hc := hn.trans ht
    obtain ⟨hsize,hform⟩ := two_one_pair_form hN hsmall hRS harea hR hsum v (hc.isMaximizer_iff.mp hm)
    exact ⟨hsize,hc.trans hform⟩
  · simp only [stripDiagram_one] at hn hm ⊢
    obtain ⟨hsize,hform⟩ := two_one_pair_form hN hsmall hRS harea hR hsum u (hn.isMaximizer_iff.mp hm)
    exact ⟨hsize,hn.trans hform⟩
  · omega

end
end SpanningTreeIsoperimetry.SmallPairClassification
