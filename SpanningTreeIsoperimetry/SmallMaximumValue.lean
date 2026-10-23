module

public import SpanningTreeIsoperimetry.SmallMaximizerProfiles
public import SpanningTreeIsoperimetry.OrderedNormalization
public import SpanningTreeIsoperimetry.SingletonPairComparisons
public import SpanningTreeIsoperimetry.ThirteenCandidateExclusions
public import SpanningTreeIsoperimetry.ProposedMaximumBounds

@[expose] public section

/-! The complete maximum-value formula for cardinalities one through seventeen.
The bounds apply to arbitrary connected induced lattice domains. -/
namespace SpanningTreeIsoperimetry.SmallMaximumValue
open Ferrers CornerEnergy CornerPrimalDomains CornerProfileNormalization
open SmallMaximizerProfiles ProposedMaximumBounds
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem small_hulls {N R S k : ℕ} (hN : 0<N) (hsmall : N≤17) (hRS : R≤S)
    (harea : N+k=(R+1)*(S+1)) (hk : k≤R) (hk2 : 2≤k)
    (hsum : (R+1)+(S+1)=minimumSideSum N) :
    (R=2 ∧ S=2 ∧ k=2) ∨ (R=2 ∧ S=3 ∧ k=2) ∨ (R=2 ∧ S=4 ∧ k=2) ∨
      (R=3 ∧ S=3 ∧ k=2) ∨ (R=3 ∧ S=3 ∧ k=3) ∨ (R=3 ∧ S=4 ∧ k=3) := by
  have hm := ceil_sqrt_is_minimum_side_sum hN
  change IsMinimumSideSum N (minimumSideSum N) at hm
  rw [← hsum] at hm
  have hh := SmallShapeCatalogue.small_nonstrip_hulls hsmall (by omega : 0<R+1)
    (by omega : R+1≤S+1) harea (by omega : k<R+1) hk2 hm
  omega

theorem three_hulls {N R S : ℕ} (hN : 0<N) (hsmall : N≤17) (hRS : R≤S)
    (harea : N+3=(R+1)*(S+1)) (hk : 3≤R)
    (hsum : (R+1)+(S+1)=minimumSideSum N) : (R=3 ∧ S=3) ∨ (R=3 ∧ S=4) := by
  have hh := small_hulls hN hsmall hRS harea hk (by decide : 2≤3) hsum
  omega

theorem singleton_pair_bound {N R S : ℕ} (hN : 0<N) (hsmall : N≤17) (hRS : R≤S)
    (harea : N+2=(R+1)*(S+1)) (hk : 2≤R)
    (hsum : (R+1)+(S+1)=minimumSideSum N) :
    treeCount (cornerPrimal R S SmallTenComparison.singletonPair)≤proposedMaximum N := by
  have hh := small_hulls hN hsmall hRS harea hk le_rfl hsum
  have hc : (R=2 ∧ S=2) ∨ (R=2 ∧ S=3) ∨ (R=2 ∧ S=4) ∨ (R=3 ∧ S=3) := by omega
  rcases hc with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · have hn : N=7 := by omega
    subst N
    rw [SingletonPairComparisons.seven_count]
    norm_num [proposedMaximum]
  · have hn : N=10 := by omega
    subst N
    rw [SmallTenComparison.opposite_ten_count]
    norm_num [proposedMaximum,SmallTenComparison.canonical_ten_count]
  · have hn : N=13 := by omega
    subst N
    rw [SingletonPairComparisons.thirteen_count]
    norm_num [proposedMaximum,CanonicalThirteen.canonical13_treeCount]
  · have hn : N=14 := by omega
    subst N
    rw [SingletonPairComparisons.fourteen_count]
    norm_num [proposedMaximum]

theorem two_one_pair_bound {N R S : ℕ} (hN : 0<N) (hsmall : N≤17) (hRS : R≤S)
    (harea : N+3=(R+1)*(S+1)) (hk : 3≤R)
    (hsum : (R+1)+(S+1)=minimumSideSum N) (v : Bool) :
    treeCount (cornerPrimal R S (SeventeenPrimalComparisons.pairFamily v))≤proposedMaximum N := by
  rcases three_hulls hN hsmall hRS harea hk hsum with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · have hn : N=13 := by omega
    subst N
    rw [ThirteenCandidateExclusions.pair_square_count]
    norm_num [proposedMaximum,CanonicalThirteen.canonical13_treeCount]
  · have hn : N=17 := by omega
    subst N
    rw [SeventeenPrimalComparisons.pair_count]
    cases v <;> norm_num [proposedMaximum]

theorem opposite_pair_bound {N R S a b : ℕ} (hN : 0<N) (hsmall : N≤17) (hRS : R≤S)
    (ha : 0<a) (hb : 0<b) (hab : a+b≤3)
    (hR : a+b≤R) (hS : a+b≤S) (harea : N+(a+b)=(R+1)*(S+1))
    (hsum : (R+1)+(S+1)=minimumSideSum N) (c : Corner) (u v : Bool) :
    treeCount (cornerPrimal R S (twoCornerFamily c (opposite c)
      (stripDiagram a u) (stripDiagram b v)))≤proposedMaximum N := by
  have hn := pair_normalization (R := R) (S := S) c
    (stripDiagram_ferrers a u) (stripDiagram_ferrers b v)
    (by simpa only [stripDiagram_card] using hR) (by simpa only [stripDiagram_card] using hS)
  rw [hn.treeCount_eq]
  have ha2 : a≤2 := by omega
  have hb2 : b≤2 := by omega
  interval_cases a <;> interval_cases b
  · simp only [stripDiagram_one]
    exact singleton_pair_bound hN hsmall hRS harea hR hsum
  · simp only [stripDiagram_one]
    have ht := pair_swap (R := R) (S := S) (horizontalStrip_isFerrers 1) (stripDiagram_ferrers 2 v)
      (by simpa only [card_horizontalStrip,stripDiagram_card] using hR)
      (by simpa only [card_horizontalStrip,stripDiagram_card] using hS)
    rw [ht.treeCount_eq]
    exact two_one_pair_bound hN hsmall hRS harea hR hsum v
  · simp only [stripDiagram_one]
    exact two_one_pair_bound hN hsmall hRS harea hR hsum u
  · omega

theorem profile_bound {N R S : ℕ} {M : Corner → Diagram}
    (hN : 0<N) (hsmall : N≤17) (hRS : R≤S)
    (hR : totalDefect M≤R) (hS : totalDefect M≤S)
    (harea : N+totalDefect M=(R+1)*(S+1))
    (hsum : (R+1)+(S+1)=minimumSideSum N)
    (hmax : IsMaximizer (cornerPrimal R S M)) (hp : SmallMaximizerProfile M) :
    treeCount (cornerPrimal R S M)≤proposedMaximum N := by
  rcases hp with hs|he|hp|ht
  · obtain ⟨c,k,v,rfl⟩ := hs
    have heq : totalDefect (singleFamily c (stripDiagram k.val v))=k.val := by
      rw [singleFamily,totalDefect_twoCornerFamily (opposite_distinct c)]
      simp only [stripDiagram_card,Finset.card_empty,add_zero]
    change totalDefect (singleFamily c (stripDiagram k.val v))≤R at hR
    change N+totalDefect (singleFamily c (stripDiagram k.val v))=(R+1)*(S+1) at harea
    rw [heq] at hR harea
    exact (single_strip_le_canonical hN hRS hR harea.symm hsum c v).trans (canonical_le_proposed N)
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
    have hm := hc.isMaximizer_iff.mp hmax
    rcases three_hulls hN hsmall hRS harea hR hsum with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact False.elim (ThirteenCandidateExclusions.ell_not_maximal hm)
    · exact False.elim (SeventeenPrimalComparisons.other_candidates_not_maximal.2.1 hm)
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
    exact opposite_pair_bound hN hsmall hRS ha hb hab hR hS harea hsum c u v
  · obtain ⟨d,rfl⟩ := ht
    change totalDefect (missingFamily d)≤R at hR
    change totalDefect (missingFamily d)≤S at hS
    change N+totalDefect (missingFamily d)=(R+1)*(S+1) at harea
    rw [missingFamily_total] at hR hS harea
    have hm := (triple_normalization d hR hS).isMaximizer_iff.mp hmax
    rcases three_hulls hN hsmall hRS harea hR hsum with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact False.elim (ThirteenCandidateExclusions.normalized_triple_not_maximal hm)
    · exact False.elim (SeventeenPrimalComparisons.other_candidates_not_maximal.2.2 hm)

theorem normalized_maximizer_bound {A : Domain} {R S : ℕ} (hmax : IsMaximizer A)
    (hh : IsStandardHull A (R+1) (S+1)) (hRS : R≤S) (hsmall : A.card≤17) :
    treeCount A≤proposedMaximum A.card := by
  obtain ⟨hmodel,hM,hR,hS⟩ := maximizer_canonicalCorner_model hmax hh
  have hp := (small_normalized_maximizer_profiles hmax hh hRS hsmall).2.2
  have hN := (standardHull_to_foundation hh).card_pos
  have hsum := (maximizer_hull_shape hmax (standardHull_to_foundation hh)).2.2
  have hprod : R≤(R+1)*(S+1) := by nlinarith [Nat.zero_le (R*S)]
  have hcard := (congrArg Finset.card hmodel).trans (cornerPrimal_card hM hR hS)
  have harea : A.card+totalDefect (canonicalCornerFamily A R S)=(R+1)*(S+1) := by
    rw [hcard,Nat.sub_add_cancel (hR.trans hprod)]
  have hm : IsMaximizer (cornerPrimal R S (canonicalCornerFamily A R S)) := by rw [← hmodel]; exact hmax
  have hb := profile_bound hN hsmall hRS hR hS harea hsum hm hp
  rwa [← hmodel] at hb

theorem small_maximizer_count {A : Domain} (hmax : IsMaximizer A) (hsmall : A.card≤17) :
    treeCount A=proposedMaximum A.card := by
  obtain ⟨B,R,S,hc,hm,hh,hrs⟩ := OrderedNormalization.exists_ordered_standard_maximizer hmax
  have hb := normalized_maximizer_bound hm hh hrs (by rw [← hc.card_eq]; exact hsmall)
  rw [← hc.treeCount_eq,← hc.card_eq] at hb
  exact le_antisymm hb (proposed_le_maximizer hmax)

theorem maximum_value_small {N : ℕ} (hN : 0<N) (hsmall : N≤17) :
    (∃ S : Domain, S.card=N ∧ (domainGraph S).Connected ∧ treeCount S=proposedMaximum N) ∧
      ∀ S : Domain, S.card=N → (domainGraph S).Connected → treeCount S≤proposedMaximum N := by
  refine ⟨proposed_attained hN,?_⟩
  obtain ⟨A,hcard,hmax⟩ := MaximizerGeometry.exists_isMaximizer hN
  have hv := small_maximizer_count hmax (by rw [hcard]; exact hsmall)
  rw [hcard] at hv
  intro S hS hconn
  have h := hmax.2 S (hS.trans hcard.symm) hconn
  rwa [hv] at h

end
end SpanningTreeIsoperimetry.SmallMaximumValue
