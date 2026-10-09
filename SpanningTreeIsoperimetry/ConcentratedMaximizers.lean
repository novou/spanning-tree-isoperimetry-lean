import SpanningTreeIsoperimetry.ClassificationAssembly
import SpanningTreeIsoperimetry.SourceHullArithmetic

/-! Every large maximizing concentrated corner family is the canonical strip,
with no restriction on which admissible rectangle contains it. -/
namespace SpanningTreeIsoperimetry.ConcentratedMaximizers
open Ferrers CornerEnergy CornerPrimalDomains
open SmallMaximizerClassification SmallPairClassification
open scoped Classical
noncomputable section

theorem smallForm_large_congruent {N : ℕ} {A : Domain} (hN : 18≤N) (hf : SmallForm N A) :
    Congruent A (canonicalDomain N) := by
  rcases hf with ⟨_,_,_,hc⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨he,_⟩
  · exact hc
  · omega
  · omega
  · omega
  · rcases he with h|h|h|h|h <;> omega

theorem concentrated_family_congruent {N R S k : ℕ} {M : Corner → Diagram}
    (hN : 18≤N) (hRS : R≤S) (hR : totalDefect M≤R) (hS : totalDefect M≤S)
    (harea : N+totalDefect M=(R+1)*(S+1))
    (hsum : (R+1)+(S+1)=minimumSideSum N)
    (hcard : totalDefect M=k) (hc : CornerConcentration.IsConcentrated Finset.univ M)
    (hm : IsMaximizer (cornerPrimal R S M)) :
    Congruent (cornerPrimal R S M) (canonicalDomain N) := by
  have hRk : k≤R := by omega
  have hSk : k≤S := by omega
  have hAk : N+k=(R+1)*(S+1) := by omega
  obtain ⟨c,v,rfl⟩ := CanonicalCornerConcentration.single_family_of_concentrated hcard hc
  exact smallForm_large_congruent hN
    (single_family_form (by omega) hRS hRk hSk hAk hsum c v hm)


/-- A zero selector leaves only the canonical admissible hull. -/
theorem zero_index_maximizer_congruent {A : Domain} (hm : IsMaximizer A)
    (hN : 18≤A.card) (hzero : SourceHullArithmetic.canonicalIndex A.card=0) :
    Congruent A (canonicalDomain A.card) := by
  obtain ⟨B,R,S,hAB,hB,hh,hrs⟩ := OrderedNormalization.exists_ordered_standard_maximizer hm
  have hNB : 18≤B.card := by rw [← hAB.card_eq]; exact hN
  have hzB : SourceHullArithmetic.canonicalIndex B.card=0 := by rw [← hAB.card_eq]; exact hzero
  obtain ⟨he,hM,hR,hS⟩ := maximizer_canonicalCorner_model hB hh
  have hsum := (maximizer_hull_shape hB (standardHull_to_foundation hh)).2.2
  have hprod : R≤(R+1)*(S+1) := by nlinarith [Nat.zero_le (R*S)]
  have hcard := (congrArg Finset.card he).trans (cornerPrimal_card hM hR hS)
  have harea : B.card+totalDefect (canonicalCornerFamily B R S)=(R+1)*(S+1) := by
    rw [hcard,Nat.sub_add_cancel (hR.trans hprod)]
  have hp := SourceHullArithmetic.source_parameters_of_hull (by omega : 0<B.card)
    (by omega : 0<R+1) (by omega : R+1≤S+1) harea.symm hsum
  have ht : minimumSideSum B.card/2-(R+1)=SourceHullArithmetic.canonicalIndex B.card := by omega
  rw [ht,SourceHullArithmetic.source_at_canonical] at hp
  have hf := CanonicalRectangleBounds.canonical_flux_hypotheses (by omega : 0<B.card)
  change _ ∧ _ ∧ _ ∧ _ ∧
    (canonicalParameters B.card).1+(canonicalParameters B.card).2.2≤(canonicalParameters B.card).2.1 at hf
  rw [hp.2] at hf
  dsimp only at hf
  have hc := ClassificationAssembly.normalized_canonical_maximizer hB hh hrs hNB (by omega)
  rw [← hAB.card_eq] at hc
  exact hAB.trans hc

end
end SpanningTreeIsoperimetry.ConcentratedMaximizers
