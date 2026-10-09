import SpanningTreeIsoperimetry.CanonicalCornerConcentration
import SpanningTreeIsoperimetry.SmallMaximizerClassification

/-! Final classification interfaces. Canonical-hull equality is unconditional.
The global assembly lemmas explicitly require the remaining large-hull
reduction; they are not a proof of the still-open classification target. -/
namespace SpanningTreeIsoperimetry.ClassificationAssembly
open Ferrers CornerEnergy CornerPrimalDomains
open scoped Classical
noncomputable section

theorem normalized_canonical_maximizer {A : Domain} {R S : ℕ}
    (hm : IsMaximizer A) (hh : IsStandardHull A (R+1) (S+1))
    (hrs : R≤S) (hN : 18≤A.card)
    (hcanonical : totalDefect (canonicalCornerFamily A R S)≤S-R) :
    Congruent A (canonicalDomain A.card) := by
  obtain ⟨he,hM,hR,hS⟩ := maximizer_canonicalCorner_model hm hh
  have hpos : 0<A.card := by omega
  have hsum := (maximizer_hull_shape hm (standardHull_to_foundation hh)).2.2
  have hprod : R≤(R+1)*(S+1) := by nlinarith [Nat.zero_le (R*S)]
  have hcard := (congrArg Finset.card he).trans (cornerPrimal_card hM hR hS)
  have harea : A.card+totalDefect (canonicalCornerFamily A R S)=(R+1)*(S+1) := by
    rw [hcard,Nat.sub_add_cancel (hR.trans hprod)]
  have hp := CanonicalStrips.terminal_parameters hpos (by omega : 1≤R+1)
    (by omega : R+1≤S+1) harea.symm hsum (by omega)
  have hb := CanonicalCornerConcentration.canonical_family_optimal hN hp hM rfl
  simp only [Nat.add_sub_cancel] at hb
  rw [← he] at hb
  have hge := hm.2 (canonicalDomain A.card) (canonicalDomain_card hpos)
    (CanonicalStrips.canonicalDomain_connected hpos)
  exact hb.2.mp (le_antisymm hb.1 hge)

/-- The remaining geometric reduction, recorded as a proposition rather than
an assumed theorem. -/
def CanonicalHullReduction : Prop :=
  ∀ (A : Domain) (R S : ℕ), IsMaximizer A → IsStandardHull A (R+1) (S+1) →
    R≤S → 18≤A.card → totalDefect (canonicalCornerFamily A R S)≤S-R

theorem unique_classification_of_hull_reduction (hred : CanonicalHullReduction) :
    UniqueClassificationTarget := by
  have hc : ∀ {A : Domain}, IsMaximizer A → 18≤A.card →
      Congruent A (canonicalDomain A.card) := by
    intro A hm hN
    obtain ⟨B,R,S,hAB,hB,hh,hrs⟩ := OrderedNormalization.exists_ordered_standard_maximizer hm
    have hNB : 18≤B.card := by rw [← hAB.card_eq]; exact hN
    have hBC := normalized_canonical_maximizer hB hh hrs hNB (hred B R S hB hh hrs hNB)
    rw [← hAB.card_eq] at hBC
    exact hAB.trans hBC
  intro N hN
  obtain ⟨A,hcard,hm⟩ := MaximizerGeometry.exists_isMaximizer (by omega : 0<N)
  have hA := hc hm (by rw [hcard]; exact hN)
  rw [hcard] at hA
  refine ⟨hA.isMaximizer_iff.mp hm,?_⟩
  intro B hB hmB
  have hb := hc hmB (by rw [hB]; exact hN)
  rwa [hB] at hb

theorem maximum_value_of_unique_classification (hlarge : UniqueClassificationTarget) :
    MaximumValueTarget := by
  intro N hN
  by_cases hs : N≤17
  · exact SmallMaximumValue.maximum_value_small hN hs
  · have hm := (hlarge N (by omega)).1
    have hv : proposedMaximum N=treeCount (canonicalDomain N) := by
      simp only [proposedMaximum,show N≠7 by omega,show N≠14 by omega,show N≠17 by omega,ite_false]
    refine ⟨ProposedMaximumBounds.proposed_attained hN,?_⟩
    intro A hcard hconn
    rw [hv]
    exact hm.2 A (hcard.trans (canonicalDomain_card hN).symm) hconn

theorem nonuniqueness_of_unique_classification (hlarge : UniqueClassificationTarget) :
    NonuniquenessTarget := by
  intro N hN
  by_cases hs : N≤17
  · exact SmallMaximizerClassification.nonuniqueness_small_iff hN hs
  · constructor
    · rintro ⟨A,B,hA,hB,hmA,hmB,hnot⟩
      have ha := (hlarge N (by omega)).2 A hA hmA
      have hb := (hlarge N (by omega)).2 B hB hmB
      exact False.elim (hnot (ha.trans hb.symm))
    · intro he
      rcases he with rfl|rfl|rfl|rfl <;> omega

end
end SpanningTreeIsoperimetry.ClassificationAssembly
