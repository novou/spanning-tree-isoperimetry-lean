module

public import SpanningTreeIsoperimetry.CornerProfileNormalization
public import SpanningTreeIsoperimetry.CanonicalThirteen
public import SpanningTreeIsoperimetry.SeventeenPrimalComparisons

@[expose] public section

/-! Actual N13 count comparisons after symmetry normalization. -/
namespace SpanningTreeIsoperimetry.ThirteenCandidateExclusions
open Ferrers CornerEnergy CornerPrimalDomains CornerProfileNormalization
open SmallPrimalComparisons
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem ell_not_maximal : ¬IsMaximizer (cornerPrimal 3 3 ellFamily) := by
  intro hm
  have hcard : (canonicalDomain 13).card=(cornerPrimal 3 3 ellFamily).card := by
    rw [canonicalDomain_card (by decide : 0<13),small_primal_cardinalities.2.1]
  have h := hm.2 (canonicalDomain 13) hcard (CanonicalStrips.canonicalDomain_connected (by decide))
  rw [CanonicalThirteen.canonical13_treeCount,ell_primal_count] at h
  omega

theorem triple_not_maximal : ¬IsMaximizer (cornerPrimal 3 3 tripleFamily) := by
  intro hm
  have hcard : (canonicalDomain 13).card=(cornerPrimal 3 3 tripleFamily).card := by
    rw [canonicalDomain_card (by decide : 0<13),small_primal_cardinalities.2.2]
  have h := hm.2 (canonicalDomain 13) hcard (CanonicalStrips.canonicalDomain_connected (by decide))
  rw [CanonicalThirteen.canonical13_treeCount,triple_primal_count] at h
  omega

theorem tripleFamily_missing : tripleFamily=missingFamily (true,false) := by decide +kernel

theorem normalized_triple_not_maximal : ¬IsMaximizer (cornerPrimal 3 3 (missingFamily (false,false))) := by
  intro hm
  have hc := triple_normalization (R := 3) (S := 3) (true,false) (by decide) (by decide)
  have hback := hc.isMaximizer_iff.mpr hm
  rw [← tripleFamily_missing] at hback
  exact triple_not_maximal hback

theorem pair_square_count (v : Bool) :
    treeCount (cornerPrimal 3 3 (SeventeenPrimalComparisons.pairFamily v))=2656 := by
  cases v
  · have he : SeventeenPrimalComparisons.pairFamily false=oppositeFamily := by decide +kernel
    rw [he,opposite_primal_count]
  · have hf := pair_family_fit (R := 3) (S := 3)
      (by decide : (true,true)≠(false,false)) (stripDiagram_ferrers 2 true)
      (horizontalStrip_isFerrers 1) (by decide) (by decide)
    have hc := cornerPrimal_transpose_congruent hf
    change Congruent (cornerPrimal 3 3 (SeventeenPrimalComparisons.pairFamily true))
      (cornerPrimal 3 3 (transposedFamily (SeventeenPrimalComparisons.pairFamily true))) at hc
    have he : transposedFamily (SeventeenPrimalComparisons.pairFamily true)=oppositeFamily := by decide +kernel
    rw [he] at hc
    rw [hc.treeCount_eq,opposite_primal_count]

end
end SpanningTreeIsoperimetry.ThirteenCandidateExclusions
