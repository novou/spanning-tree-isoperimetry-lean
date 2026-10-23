module

public import SpanningTreeIsoperimetry.SmallMaximumValue

@[expose] public section

/-! Attainment and equality for the actual small maximum values. -/
namespace SpanningTreeIsoperimetry.SmallMaximizers
open SmallMaximumValue

theorem isMaximizer_iff_count {A : Domain} (hc : (domainGraph A).Connected) (hs : A.card≤17) :
    IsMaximizer A ↔ treeCount A=proposedMaximum A.card := by
  constructor
  · exact fun hm => small_maximizer_count hm hs
  · intro he
    have hN : 0<A.card := Finset.card_pos.mpr (connected_domain_nonempty hc)
    refine ⟨hc,?_⟩
    intro B hcard hconn
    have hb := (maximum_value_small hN hs).2 B hcard hconn
    rwa [← he] at hb

theorem canonical_small_maximizer {N : ℕ} (hN : 0<N) (hs : N≤17)
    (h7 : N≠7) (h14 : N≠14) (h17 : N≠17) : IsMaximizer (canonicalDomain N) := by
  apply (isMaximizer_iff_count (CanonicalStrips.canonicalDomain_connected hN)
    (by rw [canonicalDomain_card hN]; exact hs)).mpr
  rw [canonicalDomain_card hN]
  simp only [proposedMaximum,h7,h14,h17,ite_false]

theorem winner_seven_maximizer : IsMaximizer ConcreteCounts.winner7Domain := by
  apply (isMaximizer_iff_count ConcreteCounts.winner7_connected
    (by rw [ConcreteCounts.winner7Domain_card]; decide)).mpr
  rw [ConcreteCounts.winner7Domain_card,ConcreteCounts.winner7_treeCount]
  norm_num [proposedMaximum]

theorem winner_fourteen_maximizer : IsMaximizer ConcreteCounts.winner14Domain := by
  apply (isMaximizer_iff_count ConcreteCounts.winner14_connected
    (by rw [ConcreteCounts.winner14Domain_card]; decide)).mpr
  rw [ConcreteCounts.winner14Domain_card,ConcreteCounts.winner14_treeCount]
  norm_num [proposedMaximum]

theorem winner_seventeen_maximizer : IsMaximizer SmallCases.winner17Domain := by
  apply (isMaximizer_iff_count ConcreteCounts.winner17_connected
    (by rw [SmallCases.seventeen_domain_sizes.1])).mpr
  rw [SmallCases.seventeen_domain_sizes.1,ConcreteCounts.winner17_treeCount]
  norm_num [proposedMaximum]

theorem opposite_ten_maximizer :
    IsMaximizer (CornerPrimalDomains.cornerPrimal 2 3 SmallTenComparison.singletonPair) := by
  have hc : (domainGraph (CornerPrimalDomains.cornerPrimal 2 3 SmallTenComparison.singletonPair)).Connected := by
    apply (treeCount_pos_iff_connected _).mp
    rw [SmallTenComparison.opposite_ten_count]
    decide
  apply (isMaximizer_iff_count hc (by rw [SmallTenComparison.opposite_ten_card]; decide)).mpr
  rw [SmallTenComparison.opposite_ten_card,SmallTenComparison.opposite_ten_count]
  norm_num [proposedMaximum,SmallTenComparison.canonical_ten_count]

theorem opposite_thirteen_maximizer :
    IsMaximizer (CornerPrimalDomains.cornerPrimal 3 3 SmallPrimalComparisons.oppositeFamily) := by
  have hc : (domainGraph (CornerPrimalDomains.cornerPrimal 3 3 SmallPrimalComparisons.oppositeFamily)).Connected := by
    apply (treeCount_pos_iff_connected _).mp
    rw [SmallPrimalComparisons.opposite_primal_count]
    decide
  apply (isMaximizer_iff_count hc
    (by rw [SmallPrimalComparisons.small_primal_cardinalities.1]; decide)).mpr
  rw [SmallPrimalComparisons.small_primal_cardinalities.1,SmallPrimalComparisons.opposite_primal_count]
  norm_num [proposedMaximum,CanonicalThirteen.canonical13_treeCount]

end SpanningTreeIsoperimetry.SmallMaximizers
