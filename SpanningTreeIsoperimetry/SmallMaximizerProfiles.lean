module

public import SpanningTreeIsoperimetry.SmallCornerProfiles
public import SpanningTreeIsoperimetry.AdjacentPairExclusion
public import SpanningTreeIsoperimetry.CanonicalCornerPrimal

@[expose] public section

/-! Every normalized maximizer with at most seventeen vertices is in the
explicit strip/L/opposite-pair/three-singleton list. Adjacent pairs are excluded
by an actual strict count improvement with the same cardinality. -/
namespace SpanningTreeIsoperimetry.SmallMaximizerProfiles
open Ferrers CornerEnergy CornerPrimalDomains SmallCornerProfiles
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def OppositePairProfile (M : Corner → Diagram) : Prop :=
  ∃ c : Corner, ∃ a b : Fin 3, 0<a.val ∧ 0<b.val ∧ a.val+b.val≤3 ∧
    ∃ u v : Bool, M=twoCornerFamily c (reflectCorner (false,false) c)
      (stripDiagram a.val u) (stripDiagram b.val v)

def SmallMaximizerProfile (M : Corner → Diagram) : Prop :=
  SingleStripProfile M ∨ EllProfile M ∨ OppositePairProfile M ∨ TripleProfile M

theorem sparse_maximizer_profiles {R S : ℕ} {M : Corner → Diagram}
    (hM : ∀ c, IsFerrers (M c)) (hk : totalDefect M≤3)
    (hR : totalDefect M≤R) (hS : totalDefect M≤S)
    (hmax : IsMaximizer (cornerPrimal R S M)) : SmallMaximizerProfile M := by
  rcases sparse_ferrers_profiles hM hk with hs|he|hp|ht
  · exact Or.inl hs
  · exact Or.inr (Or.inl he)
  · obtain ⟨c,d,hcd,a,b,ha,hb,hsize,u,v,hpair⟩ := hp
    have htotal : totalDefect M=a.val+b.val := by
      rw [hpair,totalDefect_twoCornerFamily hcd]
      simp only [stripDiagram_card]
    have hrc : (stripDiagram a.val u).card+(stripDiagram b.val v).card≤R := by
      simpa only [htotal,stripDiagram_card] using hR
    have hsc : (stripDiagram a.val u).card+(stripDiagram b.val v).card≤S := by
      simpa only [htotal,stripDiagram_card] using hS
    have hna : (stripDiagram a.val u).Nonempty := by
      apply Finset.card_pos.mp
      simpa only [stripDiagram_card] using ha
    have hnb : (stripDiagram b.val v).Nonempty := by
      apply Finset.card_pos.mp
      simpa only [stripDiagram_card] using hb
    have hmaxPair : IsMaximizer (cornerPrimal R S (twoCornerFamily c d
        (stripDiagram a.val u) (stripDiagram b.val v))) := by rw [← hpair]; exact hmax
    have hd := pair_maximizer_opposite hcd (stripDiagram_ferrers a.val u)
      (stripDiagram_ferrers b.val v) hna hnb hrc hsc hmaxPair
    subst d
    exact Or.inr (Or.inr (Or.inl ⟨c,a,b,ha,hb,hsize,u,v,hpair⟩))
  · exact Or.inr (Or.inr (Or.inr ht))

theorem small_normalized_maximizer_profiles {A : Domain} {R S : ℕ}
    (hmax : IsMaximizer A) (hh : IsStandardHull A (R+1) (S+1))
    (hRS : R≤S) (hsmall : A.card≤17) :
    A=cornerPrimal R S (canonicalCornerFamily A R S) ∧
      totalDefect (canonicalCornerFamily A R S)≤3 ∧
      SmallMaximizerProfile (canonicalCornerFamily A R S) := by
  have hf := standardHull_to_foundation hh
  have hN : 0<A.card := hf.card_pos
  have hsum := (maximizer_hull_shape hmax hf).2.2
  have hmin := ceil_sqrt_is_minimum_side_sum hN
  change IsMinimumSideSum A.card (minimumSideSum A.card) at hmin
  rw [← hsum] at hmin
  have hsq := hmin.2.1
  have hpred : (R+1)+(S+1)-1+1=(R+1)+(S+1) := by omega
  have hsum9 : (R+1)+(S+1)≤9 := by nlinarith
  have hR3 : R≤3 := by omega
  obtain ⟨hmodel,hM,hR,hS⟩ := maximizer_canonicalCorner_model hmax hh
  have hk : totalDefect (canonicalCornerFamily A R S)≤3 := by omega
  refine ⟨hmodel,hk,?_⟩
  apply sparse_maximizer_profiles hM hk hR hS
  rw [← hmodel]
  exact hmax

end
end SpanningTreeIsoperimetry.SmallMaximizerProfiles
