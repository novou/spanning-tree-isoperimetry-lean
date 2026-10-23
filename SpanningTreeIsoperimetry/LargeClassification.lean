module

public import SpanningTreeIsoperimetry.SingleCornerExclusion
public import SpanningTreeIsoperimetry.ClassificationAssembly
public import SpanningTreeIsoperimetry.ConcentratedMaximizers

@[expose] public section

/-! Complete large-cardinality classification, assembled from actual corner
exclusions and strip equality. No missing mathematical lemma is a premise. -/
namespace SpanningTreeIsoperimetry.LargeClassification
open Ferrers CornerEnergy CornerPrimalDomains CornerProfileNormalization StripRigidity
open ClassificationAssembly ConcentratedMaximizers SingleCornerSmallOrientation
open scoped Classical
noncomputable section

theorem normalized_maximizer_congruent {A : Domain} {R S : ℕ} (hm : IsMaximizer A)
    (hh : IsStandardHull A (R+1) (S+1)) (hrs : R≤S) (hN : 18≤A.card) :
    Congruent A (canonicalDomain A.card) := by
  obtain ⟨he,hM,hR,hS⟩ := maximizer_canonicalCorner_model hm hh
  let F := canonicalCornerFamily A R S
  change A=cornerPrimal R S F at he
  change ∀ c,IsFerrers (F c) at hM
  change totalDefect F≤R at hR
  change totalDefect F≤S at hS
  have hsum := (maximizer_hull_shape hm (standardHull_to_foundation hh)).2.2
  have hprod : R≤(R+1)*(S+1) := by nlinarith [Nat.zero_le (R*S)]
  have hcard := (congrArg Finset.card he).trans (cornerPrimal_card hM hR hS)
  have harea : A.card+totalDefect F=(R+1)*(S+1) := by
    rw [hcard,Nat.sub_add_cancel (hR.trans hprod)]
  have hmaxF : IsMaximizer (cornerPrimal R S F) := by rw [← he]; exact hm
  by_cases htwo : ∃ c d : Corner, c≠d ∧ (F c).Nonempty ∧ (F d).Nonempty
  · obtain ⟨c,d,hcd,hc,hd⟩ := htwo
    have hn := MulticornerExclusion.not_isMaximizer hN (by omega : R+1≤S+1)
      (by omega : totalDefect F<R+1) harea.symm hsum F hM rfl hcd hc hd
    simp only [Nat.add_sub_cancel] at hn
    exact False.elim (hn hmaxF)
  · by_cases hz : totalDefect F=0
    · apply normalized_canonical_maximizer hm hh hrs hN
      change totalDefect F≤S-R
      omega
    · have hsome : ∃ c : Corner, (F c).Nonempty := by
        by_contra hn
        have hzero (c : Corner) : F c=∅ := Finset.not_nonempty_iff_eq_empty.mp (fun hc => hn ⟨c,hc⟩)
        have htot : totalDefect F=0 := by simp [totalDefect,hzero]
        exact hz htot
      obtain ⟨c,hc⟩ := hsome
      have hother (d : Corner) (hd : d≠c) : F d=∅ :=
        Finset.not_nonempty_iff_eq_empty.mp (fun hn => htwo ⟨c,d,hd.symm,hc,hn⟩)
      by_cases hs : IsStraightStrip (F c)
      · have hconc : CornerConcentration.IsConcentrated Finset.univ F :=
          ⟨c,Finset.mem_univ c,hc,hs,fun d _ hd => hother d hd⟩
        have hcong := concentrated_family_congruent hN hrs hR hS harea hsum rfl hconc hmaxF
        rwa [← he] at hcong
      · have hsingle : F=singleFamily c (F c) := by
          funext d
          by_cases hd : d=c
          · subst d
            simp [singleFamily,twoCornerFamily]
          · simp [singleFamily,twoCornerFamily,hd,hother d hd]
        have htotal : totalDefect F=(F c).card :=
          (congrArg totalDefect hsingle).trans (singleFamily_total c (F c))
        have hsingleMax : IsMaximizer (cornerPrimal R S (singleFamily c (F c))) := by
          rw [← hsingle]
          exact hmaxF
        have hn := SingleCornerExclusion.not_isMaximizer hN (by omega : R+1≤S+1)
          (hM c) hs (by omega : (F c).card<R+1)
          (by omega : (R+1)*(S+1)=A.card+(F c).card) hsum c
        simp only [Nat.add_sub_cancel] at hn
        exact False.elim (hn hsingleMax)

theorem maximizer_congruent {A : Domain} (hm : IsMaximizer A) (hN : 18≤A.card) :
    Congruent A (canonicalDomain A.card) := by
  obtain ⟨B,R,S,hAB,hB,hh,hrs⟩ := OrderedNormalization.exists_ordered_standard_maximizer hm
  have hc := normalized_maximizer_congruent hB hh hrs (by rw [← hAB.card_eq]; exact hN)
  rw [← hAB.card_eq] at hc
  exact hAB.trans hc

theorem canonical_isMaximizer {N : ℕ} (hN : 18≤N) : IsMaximizer (canonicalDomain N) := by
  obtain ⟨A,hcard,hm⟩ := MaximizerGeometry.exists_isMaximizer (by omega : 0<N)
  have hc := maximizer_congruent hm (by rw [hcard]; exact hN)
  rw [hcard] at hc
  exact hc.isMaximizer_iff.mp hm

theorem uniqueClassificationTarget : UniqueClassificationTarget := by
  intro N hN
  refine ⟨canonical_isMaximizer hN,?_⟩
  intro A hcard hm
  have hc := maximizer_congruent hm (by rw [hcard]; exact hN)
  rwa [hcard] at hc

theorem maximizer_iff {A : Domain} (hN : 18≤A.card) :
    IsMaximizer A ↔ Congruent A (canonicalDomain A.card) :=
  ⟨fun hm => maximizer_congruent hm hN,
    fun hc => hc.isMaximizer_iff.mpr (canonical_isMaximizer hN)⟩

end
end SpanningTreeIsoperimetry.LargeClassification
