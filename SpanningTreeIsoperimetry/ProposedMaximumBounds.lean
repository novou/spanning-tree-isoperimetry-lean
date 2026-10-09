import SpanningTreeIsoperimetry.CanonicalChecks
import SpanningTreeIsoperimetry.CanonicalStrips

/-! The proposed values have actual connected witnesses at every size.
The upper bound and classification are separate results. -/
namespace SpanningTreeIsoperimetry.ProposedMaximumBounds
open ConcreteCounts SmallCases
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem canonical_le_proposed (N : ℕ) : treeCount (canonicalDomain N)≤proposedMaximum N := by
  by_cases h7 : N=7
  · subst N
    rw [canonicalDomain_exception_counts.1]
    norm_num [proposedMaximum]
  by_cases h14 : N=14
  · subst N
    rw [canonicalDomain_exception_counts.2.1]
    norm_num [proposedMaximum]
  by_cases h17 : N=17
  · subst N
    rw [canonicalDomain_exception_counts.2.2]
    norm_num [proposedMaximum]
  simp only [proposedMaximum,h7,h14,h17,ite_false,le_refl]

theorem proposed_attained {N : ℕ} (hN : 0<N) :
    ∃ S : Domain, S.card=N ∧ (domainGraph S).Connected ∧ treeCount S=proposedMaximum N := by
  by_cases h7 : N=7
  · subst N
    refine ⟨winner7Domain,winner7Domain_card,winner7_connected,?_⟩
    rw [winner7_treeCount]
    norm_num [proposedMaximum]
  by_cases h14 : N=14
  · subst N
    refine ⟨winner14Domain,winner14Domain_card,winner14_connected,?_⟩
    rw [winner14_treeCount]
    norm_num [proposedMaximum]
  by_cases h17 : N=17
  · subst N
    refine ⟨winner17Domain,seventeen_domain_sizes.1,winner17_connected,?_⟩
    rw [winner17_treeCount]
    norm_num [proposedMaximum]
  refine ⟨canonicalDomain N,canonicalDomain_card hN,CanonicalStrips.canonicalDomain_connected hN,?_⟩
  simp only [proposedMaximum,h7,h14,h17,ite_false]

theorem proposed_le_maximizer {A : Domain} (hmax : IsMaximizer A) :
    proposedMaximum A.card≤treeCount A := by
  have hN : 0<A.card := Finset.card_pos.mpr (connected_domain_nonempty hmax.1)
  obtain ⟨S,hcard,hconn,hcount⟩ := proposed_attained hN
  rw [← hcount]
  exact hmax.2 S hcard hconn

end SpanningTreeIsoperimetry.ProposedMaximumBounds
