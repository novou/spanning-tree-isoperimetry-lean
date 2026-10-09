import SpanningTreeIsoperimetry.MaximizingStripClassification
import SpanningTreeIsoperimetry.SmallPairClassification
import SpanningTreeIsoperimetry.NonuniquenessExamples

/-! Complete small-cardinality equality classification in concrete lattice
congruence, including exactly the four nonunique cardinalities. -/
namespace SpanningTreeIsoperimetry.SmallMaximizerClassification
open Ferrers CornerEnergy CornerPrimalDomains CornerProfileNormalization
open SmallMaximizerProfiles SmallPairClassification MaximizingStripClassification SmallMaximumValue
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def SmallForm (N : ℕ) (A : Domain) : Prop :=
  (N≠7 ∧ N≠14 ∧ N≠17 ∧ Congruent A (canonicalDomain N)) ∨
  (N=3 ∧ Congruent A (cornerStrip 2 2 1)) ∨
  (N=8 ∧ Congruent A (cornerStrip 3 3 1)) ∨
  (N=10 ∧ Congruent A (cornerStrip 3 4 2)) ∨
  (ExceptionalSize N ∧ Congruent A (oppositeDomain N))

theorem SmallForm.pullback {N : ℕ} {A B : Domain} (h : SmallForm N B) (hc : Congruent A B) :
    SmallForm N A := by
  rcases h with ⟨h7,h14,h17,ht⟩|⟨h3,ht⟩|⟨h8,ht⟩|⟨h10,ht⟩|⟨he,ht⟩
  · exact Or.inl ⟨h7,h14,h17,hc.trans ht⟩
  · exact Or.inr (Or.inl ⟨h3,hc.trans ht⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h8,hc.trans ht⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h10,hc.trans ht⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨he,hc.trans ht⟩)))

theorem strip_form {N r s k : ℕ} (hN : 0<N) (hr : 1≤r) (hrs : r≤s)
    (hk : k<r) (harea : r*s=N+k) (hsum : r+s=minimumSideSum N)
    (hm : IsMaximizer (cornerStrip r s k)) : SmallForm N (cornerStrip r s k) := by
  have hp := maximizing_strip_parameters hN hr hrs hk harea hsum hm
  have hc := canonical_maximal_of_strip hN hr hrs hk harea hsum hm
  have h7 : N≠7 := by intro h; subst N; exact canonicalDomain_not_maximal_seven hc
  have h14 : N≠14 := by intro h; subst N; exact canonicalDomain_not_maximal_fourteen hc
  have h17 : N≠17 := by intro h; subst N; exact canonicalDomain_not_maximal_seventeen hc
  rcases hp with hp|⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩
  · left
    refine ⟨h7,h14,h17,?_⟩
    have he : canonicalDomain N=cornerStrip r s k := by unfold canonicalDomain; rw [hp]
    rw [he]
    exact congruent_refl _
  · exact Or.inr (Or.inl ⟨rfl,congruent_refl _⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl,congruent_refl _⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,congruent_refl _⟩)))

theorem single_family_form {N R S k : ℕ} (hN : 0<N) (hRS : R≤S)
    (hR : k≤R) (hS : k≤S) (harea : N+k=(R+1)*(S+1))
    (hsum : (R+1)+(S+1)=minimumSideSum N) (c : Corner) (v : Bool)
    (hm : IsMaximizer (cornerPrimal R S (singleFamily c (stripDiagram k v)))) :
    SmallForm N (cornerPrimal R S (singleFamily c (stripDiagram k v))) := by
  have hc := single_normalization (R := R) (S := S) c (stripDiagram_ferrers k v)
    (by simpa only [stripDiagram_card] using hR) (by simpa only [stripDiagram_card] using hS)
  have ht := hc.isMaximizer_iff.mp hm
  rw [single_strip_primal] at hc ht
  cases v
  · have ho := maximizing_orientation_congruent (by omega : 1≤R+1) (by omega : R+1≤S+1)
      (by omega : k<R+1) ht
    have hf := strip_form hN (by omega) (by omega) (by omega) harea.symm hsum (ho.isMaximizer_iff.mp ht)
    exact hf.pullback (hc.trans ho)
  · have hf := strip_form hN (by omega) (by omega) (by omega) harea.symm hsum ht
    exact hf.pullback hc

theorem profile_form {N R S : ℕ} {M : Corner → Diagram}
    (hN : 0<N) (hsmall : N≤17) (hRS : R≤S)
    (hR : totalDefect M≤R) (hS : totalDefect M≤S)
    (harea : N+totalDefect M=(R+1)*(S+1))
    (hsum : (R+1)+(S+1)=minimumSideSum N)
    (hm : IsMaximizer (cornerPrimal R S M)) (hp : SmallMaximizerProfile M) :
    SmallForm N (cornerPrimal R S M) := by
  rcases hp with hs|he|hp|ht
  · obtain ⟨c,k,v,rfl⟩ := hs
    have heq : totalDefect (singleFamily c (stripDiagram k.val v))=k.val := by
      rw [singleFamily,totalDefect_twoCornerFamily (opposite_distinct c)]
      simp only [stripDiagram_card,Finset.card_empty,add_zero]
    change totalDefect (singleFamily c (stripDiagram k.val v))≤R at hR
    change totalDefect (singleFamily c (stripDiagram k.val v))≤S at hS
    change N+totalDefect (singleFamily c (stripDiagram k.val v))=(R+1)*(S+1) at harea
    rw [heq] at hR hS harea
    exact single_family_form hN hRS hR hS harea hsum c v hm
  · obtain ⟨c,rfl⟩ := he
    have heq : totalDefect (singleFamily c threeCell)=3 := by
      rw [singleFamily,totalDefect_twoCornerFamily (opposite_distinct c),card_threeCell]
      simp
    change totalDefect (singleFamily c threeCell)≤R at hR
    change totalDefect (singleFamily c threeCell)≤S at hS
    change N+totalDefect (singleFamily c threeCell)=(R+1)*(S+1) at harea
    rw [heq] at hR hS harea
    have hc := single_normalization (R := R) (S := S) c ThreeCellEnergy.ell_isFerrers
      (by simpa only [card_threeCell] using hR) (by simpa only [card_threeCell] using hS)
    have hmax := hc.isMaximizer_iff.mp hm
    rcases three_hulls hN hsmall hRS harea hR hsum with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact False.elim (ThirteenCandidateExclusions.ell_not_maximal hmax)
    · exact False.elim (SeventeenPrimalComparisons.other_candidates_not_maximal.2.1 hmax)
  · obtain ⟨c,a,b,ha,hb,hab,u,v,rfl⟩ := hp
    have heq : totalDefect (twoCornerFamily c (opposite c) (stripDiagram a.val u)
        (stripDiagram b.val v))=a.val+b.val := by
      rw [totalDefect_twoCornerFamily (opposite_distinct c)]
      simp only [stripDiagram_card]
    change totalDefect (twoCornerFamily c (opposite c) (stripDiagram a.val u) (stripDiagram b.val v))≤R at hR
    change totalDefect (twoCornerFamily c (opposite c) (stripDiagram a.val u) (stripDiagram b.val v))≤S at hS
    change N+totalDefect (twoCornerFamily c (opposite c) (stripDiagram a.val u) (stripDiagram b.val v))=
      (R+1)*(S+1) at harea
    rw [heq] at hR hS harea
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (opposite_pair_form hN hsmall hRS ha hb hab hR hS harea hsum c u v hm))))
  · obtain ⟨d,rfl⟩ := ht
    change totalDefect (missingFamily d)≤R at hR
    change totalDefect (missingFamily d)≤S at hS
    change N+totalDefect (missingFamily d)=(R+1)*(S+1) at harea
    rw [missingFamily_total] at hR hS harea
    have hmax := (triple_normalization d hR hS).isMaximizer_iff.mp hm
    rcases three_hulls hN hsmall hRS harea hR hsum with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact False.elim (ThirteenCandidateExclusions.normalized_triple_not_maximal hmax)
    · exact False.elim (SeventeenPrimalComparisons.other_candidates_not_maximal.2.2 hmax)

theorem normalized_form {A : Domain} {R S : ℕ} (hm : IsMaximizer A)
    (hh : IsStandardHull A (R+1) (S+1)) (hrs : R≤S) (hs : A.card≤17) : SmallForm A.card A := by
  obtain ⟨he,hM,hR,hS⟩ := maximizer_canonicalCorner_model hm hh
  have hp := (small_normalized_maximizer_profiles hm hh hrs hs).2.2
  have hN := (standardHull_to_foundation hh).card_pos
  have hsum := (maximizer_hull_shape hm (standardHull_to_foundation hh)).2.2
  have hprod : R≤(R+1)*(S+1) := by nlinarith [Nat.zero_le (R*S)]
  have hcard := (congrArg Finset.card he).trans (cornerPrimal_card hM hR hS)
  have harea : A.card+totalDefect (canonicalCornerFamily A R S)=(R+1)*(S+1) := by
    rw [hcard,Nat.sub_add_cancel (hR.trans hprod)]
  have hmax : IsMaximizer (cornerPrimal R S (canonicalCornerFamily A R S)) := by rw [← he]; exact hm
  have hf := profile_form hN hs hrs hR hS harea hsum hmax hp
  rwa [← he] at hf

theorem small_maximizer_form {A : Domain} (hm : IsMaximizer A) (hs : A.card≤17) : SmallForm A.card A := by
  obtain ⟨B,R,S,hc,hB,hh,hrs⟩ := OrderedNormalization.exists_ordered_standard_maximizer hm
  have hf := normalized_form hB hh hrs (by rw [← hc.card_eq]; exact hs)
  rw [← hc.card_eq] at hf
  exact hf.pullback hc

theorem oppositeDomain_maximal {N : ℕ} (h : ExceptionalSize N) : IsMaximizer (oppositeDomain N) := by
  rcases h with rfl|rfl|rfl|rfl|rfl <;> norm_num [oppositeDomain]
  · exact SmallMaximizers.winner_seven_maximizer
  · exact SmallMaximizers.opposite_ten_maximizer
  · exact SmallMaximizers.opposite_thirteen_maximizer
  · exact SmallMaximizers.winner_fourteen_maximizer
  · exact SmallMaximizers.winner_seventeen_maximizer

theorem SmallForm.isMaximizer {N : ℕ} {A : Domain} (h : SmallForm N A) (hN : 0<N) (hs : N≤17) :
    IsMaximizer A := by
  rcases h with ⟨h7,h14,h17,hc⟩|⟨rfl,hc⟩|⟨rfl,hc⟩|⟨rfl,hc⟩|⟨he,hc⟩
  · exact hc.isMaximizer_iff.mpr (SmallMaximizers.canonical_small_maximizer hN hs h7 h14 h17)
  · exact hc.isMaximizer_iff.mpr NonuniquenessExamples.alternative_three_maximizer
  · exact hc.isMaximizer_iff.mpr NonuniquenessExamples.alternative_eight_maximizer
  · exact hc.isMaximizer_iff.mpr NonuniquenessExamples.alternative_ten_maximizer
  · exact hc.isMaximizer_iff.mpr (oppositeDomain_maximal he)

theorem small_maximizer_iff {A : Domain} (hN : 0<A.card) (hs : A.card≤17) :
    IsMaximizer A ↔ SmallForm A.card A :=
  ⟨fun hm => small_maximizer_form hm hs,fun h => h.isMaximizer hN hs⟩

def preferredDomain (N : ℕ) : Domain :=
  if N=7 ∨ N=14 ∨ N=17 then oppositeDomain N else canonicalDomain N

theorem SmallForm.unique_away {N : ℕ} {A : Domain} (h : SmallForm N A)
    (h3 : N≠3) (h8 : N≠8) (h10 : N≠10) (h13 : N≠13) : Congruent A (preferredDomain N) := by
  rcases h with ⟨h7,h14,h17,hc⟩|⟨he,hc⟩|⟨he,hc⟩|⟨he,hc⟩|⟨he,hc⟩
  · have hn : ¬(N=7 ∨ N=14 ∨ N=17) := by tauto
    simpa only [preferredDomain,if_neg hn] using hc
  · exact False.elim (h3 he)
  · exact False.elim (h8 he)
  · exact False.elim (h10 he)
  · have hn : N=7 ∨ N=14 ∨ N=17 := by unfold ExceptionalSize at he; tauto
    simpa only [preferredDomain,if_pos hn] using hc

theorem nonuniqueness_small_iff {N : ℕ} (hN : 0<N) (hs : N≤17) :
    HasNonisometricMaximizers N ↔ N=3 ∨ N=8 ∨ N=10 ∨ N=13 := by
  constructor
  · rintro ⟨A,B,hA,hB,hmA,hmB,hnot⟩
    by_contra hn
    have h3 : N≠3 := by tauto
    have h8 : N≠8 := by tauto
    have h10 : N≠10 := by tauto
    have h13 : N≠13 := by tauto
    have hfA := small_maximizer_form hmA (by rw [hA]; exact hs)
    have hfB := small_maximizer_form hmB (by rw [hB]; exact hs)
    rw [hA] at hfA
    rw [hB] at hfB
    exact hnot ((hfA.unique_away h3 h8 h10 h13).trans (hfB.unique_away h3 h8 h10 h13).symm)
  · exact NonuniquenessExamples.listed_sizes_nonunique

end
end SpanningTreeIsoperimetry.SmallMaximizerClassification
