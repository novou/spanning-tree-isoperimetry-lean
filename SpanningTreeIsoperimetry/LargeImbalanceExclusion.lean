import SpanningTreeIsoperimetry.NormalizedRectangleError
import SpanningTreeIsoperimetry.LargeImbalanceCountBridge

/-! Actual large-imbalance exclusion from the checked normalized rectangle
error; no analytic premise is assumed. -/
namespace SpanningTreeIsoperimetry.LargeImbalanceExclusion
open SourceHullArithmetic CanonicalRectangleBounds CornerPrimalDomains
open Ferrers CornerEnergy
open scoped Classical
noncomputable section

theorem canonical_short_ge_four {N : ℕ} (hN : 0<N) (hT : 4≤canonicalIndex N) :
    4≤(canonicalParameters N).1 := by
  have hsize := canonical_size_relation hN
  change (canonicalIndex N)^2-canonicalIndex N+
    canonicalIndex N*(minimumSideSum N%2)+(canonicalParameters N).2.2+1≤
      (canonicalParameters N).1 at hsize
  have hm := Nat.mul_le_mul hT (show 3≤canonicalIndex N-1 by omega)
  have he : canonicalIndex N*(canonicalIndex N-1)=(canonicalIndex N)^2-canonicalIndex N := by
    rw [Nat.mul_sub_left_distrib,pow_two]
    simp
  rw [he] at hm
  omega

theorem count_lt_canonical {N t : ℕ} (hN : 0<N)
    (hT : 4≤canonicalIndex N) (ht : t<canonicalIndex N)
    (M : Corner → Diagram) (hM : ∀ c, IsFerrers (M c))
    (hcard : totalDefect M=(sourceParameters N t).2.2)
    (hnot : ¬CornerConcentration.IsConcentrated Finset.univ M) :
    treeCount (cornerPrimal ((sourceParameters N t).1-1) ((sourceParameters N t).2.1-1) M)<
      treeCount (canonicalDomain N) := by
  apply LargeImbalanceCountBridge.count_lt_canonical_of_absorption hN hT ht M hM hcard hnot
  rw [hcard]
  exact (NormalizedRectangleError.source_absorption hN (canonical_short_ge_four hN hT) ht).le

end
end SpanningTreeIsoperimetry.LargeImbalanceExclusion
