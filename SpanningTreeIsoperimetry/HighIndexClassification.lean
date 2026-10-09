import SpanningTreeIsoperimetry.ConcentratedMaximizers
import SpanningTreeIsoperimetry.LargeImbalanceExclusion

/-! Full large-selector classification from actual count comparisons.
The remaining positive-selector classification cases have selector at most three. -/
namespace SpanningTreeIsoperimetry.HighIndexClassification
open Ferrers CornerEnergy CornerPrimalDomains SourceHullArithmetic
open ClassificationAssembly ConcentratedMaximizers
open scoped Classical
noncomputable section

theorem normalized_high_index {A : Domain} {R S : ℕ} (hm : IsMaximizer A)
    (hh : IsStandardHull A (R+1) (S+1)) (hrs : R≤S)
    (hN : 18≤A.card) (hT : 4≤canonicalIndex A.card) :
    Congruent A (canonicalDomain A.card) := by
  obtain ⟨he,hM,hR,hS⟩ := maximizer_canonicalCorner_model hm hh
  have hpos : 0<A.card := by omega
  have hsum := (maximizer_hull_shape hm (standardHull_to_foundation hh)).2.2
  have hprod : R≤(R+1)*(S+1) := by nlinarith [Nat.zero_le (R*S)]
  have hcard := (congrArg Finset.card he).trans (cornerPrimal_card hM hR hS)
  have harea : A.card+totalDefect (canonicalCornerFamily A R S)=(R+1)*(S+1) := by
    rw [hcard,Nat.sub_add_cancel (hR.trans hprod)]
  by_cases hcan : totalDefect (canonicalCornerFamily A R S)≤S-R
  · exact normalized_canonical_maximizer hm hh hrs hN hcan
  · by_cases hcon : CornerConcentration.IsConcentrated Finset.univ (canonicalCornerFamily A R S)
    · have hmax : IsMaximizer (cornerPrimal R S (canonicalCornerFamily A R S)) := by rw [← he]; exact hm
      have hc := concentrated_family_congruent hN hrs hR hS harea hsum rfl hcon hmax
      rwa [← he] at hc
    · let t := minimumSideSum A.card/2-(R+1)
      have hp := source_parameters_of_hull hpos (by omega : 0<R+1) (by omega : R+1≤S+1)
        harea.symm hsum
      have hne : (R+1,S+1,totalDefect (canonicalCornerFamily A R S))≠canonicalParameters A.card := by
        intro heq
        have hflux := CanonicalRectangleBounds.canonical_flux_hypotheses hpos
        change _ ∧ _ ∧ _ ∧ _ ∧
          (canonicalParameters A.card).1+(canonicalParameters A.card).2.2≤(canonicalParameters A.card).2.1 at hflux
        rw [← heq] at hflux
        dsimp only at hflux
        omega
      have ht : t<canonicalIndex A.card := source_index_lt_of_noncanonical hpos
        (by omega) (by omega) harea.symm hsum hne
      have hlt := LargeImbalanceExclusion.count_lt_canonical hpos hT ht
        (canonicalCornerFamily A R S) hM (by rw [hp.2]) hcon
      rw [hp.2] at hlt
      simp only [Nat.add_sub_cancel] at hlt
      rw [← he] at hlt
      have hge := hm.2 (canonicalDomain A.card) (canonicalDomain_card hpos)
        (CanonicalStrips.canonicalDomain_connected hpos)
      exact False.elim (hlt.not_ge hge)

theorem high_index_maximizer_congruent {A : Domain} (hm : IsMaximizer A)
    (hN : 18≤A.card) (hT : 4≤canonicalIndex A.card) :
    Congruent A (canonicalDomain A.card) := by
  obtain ⟨B,R,S,hAB,hB,hh,hrs⟩ := OrderedNormalization.exists_ordered_standard_maximizer hm
  have hc := normalized_high_index hB hh hrs
    (by rw [← hAB.card_eq]; exact hN) (by rw [← hAB.card_eq]; exact hT)
  rw [← hAB.card_eq] at hc
  exact hAB.trans hc

end
end SpanningTreeIsoperimetry.HighIndexClassification
