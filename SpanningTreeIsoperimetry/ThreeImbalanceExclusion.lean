import SpanningTreeIsoperimetry.ThreeImbalanceTest
import SpanningTreeIsoperimetry.NormalizedRectangleError
import SpanningTreeIsoperimetry.CanonicalStrips

/-! Actual multicorner exclusion for the entire canonical-index-three
regime. No rectangle-error or scalar-comparison premise is supplied. -/
namespace SpanningTreeIsoperimetry.ThreeImbalanceExclusion
open Ferrers CornerEnergy CornerPrimalDomains SourceHullArithmetic
  CrossHullCountComparison CanonicalRectangleBounds
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem canonical_short_ge_seven {N : ℕ} (hN : 0<N) (hT : canonicalIndex N=3) :
    7≤(canonicalParameters N).1 := by
  have h := canonical_size_relation hN
  change (canonicalIndex N)^2-canonicalIndex N+canonicalIndex N*(minimumSideSum N%2)+
    (canonicalParameters N).2.2+1≤(canonicalParameters N).1 at h
  rw [hT] at h
  omega

theorem count_lt_canonical {N t : ℕ} (hN : 0<N) (hT : canonicalIndex N=3) (ht : t<canonicalIndex N)
    (M : Corner → Diagram) (hM : ∀ c, IsFerrers (M c))
    (hcard : totalDefect M=(sourceParameters N t).2.2)
    {c d : Corner} (hdc : d≠c) (hc : (M c).Nonempty) (hd : (M d).Nonempty) :
    treeCount (cornerPrimal ((sourceParameters N t).1-1) ((sourceParameters N t).2.1-1) M)<
      treeCount (canonicalDomain N) := by
  let r := (sourceParameters N t).1
  let s := (sourceParameters N t).2.1
  let k := (sourceParameters N t).2.2
  let R := (canonicalParameters N).1
  let S := (canonicalParameters N).2.1
  let j := (canonicalParameters N).2.2
  have hf := source_hull_facts hN ht.le
  have htar := selected_hull_properties_of_ceil hN
  change 0<R ∧ R≤S ∧ R+S=minimumSideSum N ∧ R*S=N+j ∧ j<R at htar
  have hR7 : 7≤R := canonical_short_ge_seven hN hT
  have htarSide := (source_hull_facts hN (le_refl (canonicalIndex N))).side_difference
  rw [source_at_canonical,hT] at htarSide
  change S=R+2*3+minimumSideSum N%2 at htarSide
  have hr : totalDefect M≤r-1 := by have hh:=hf.deficit_lt_short; change k<r at hh; change totalDefect M=k at hcard; omega
  have hs : totalDefect M≤s-1 := by have hh:=hf.ordered; change r≤s at hh; omega
  have hj : j+1<S := by omega
  have hsrcArea : r*s=N+k := hf.area
  have hsrcSum : r+s=minimumSideSum N := hf.side_sum
  change treeCount (cornerPrimal (r-1) (s-1) M)<treeCount (cornerStrip R S j)
  apply count_lt_of_normalized_cost (show 3≤R by omega) hf.canonical_short_le hf.ordered
    hf.long_le_canonical M hM hr hs hj
    (show r*s+j=R*S+totalDefect M by change totalDefect M=k at hcard; omega)
    (show r+s=R+S by omega)
  · rw [hcard]
    exact (NormalizedRectangleError.source_absorption hN (by omega : 4≤(canonicalParameters N).1) ht).le
  · exact ThreeImbalanceTest.actual_selector_multicorner_test hN hT ht M hM hcard hdc hc hd

theorem not_isMaximizer {N t : ℕ} (hN : 0<N) (hT : canonicalIndex N=3) (ht : t<canonicalIndex N)
    (M : Corner → Diagram) (hM : ∀ c, IsFerrers (M c))
    (hcard : totalDefect M=(sourceParameters N t).2.2)
    {c d : Corner} (hdc : d≠c) (hc : (M c).Nonempty) (hd : (M d).Nonempty) :
    ¬IsMaximizer (cornerPrimal ((sourceParameters N t).1-1) ((sourceParameters N t).2.1-1) M) := by
  intro hmax
  have hf := source_hull_facts hN ht.le
  have hr : totalDefect M≤(sourceParameters N t).1-1 := by rw [hcard]; have hh:=hf.deficit_lt_short; omega
  have hs : totalDefect M≤(sourceParameters N t).2.1-1 := by have hh:=hf.ordered; omega
  have hsize : (cornerPrimal ((sourceParameters N t).1-1) ((sourceParameters N t).2.1-1) M).card=N := by
    rw [cornerPrimal_card hM hr hs,hcard,Nat.sub_add_cancel (show 1≤(sourceParameters N t).1 by have hh:=hf.short_pos; omega),
      Nat.sub_add_cancel (show 1≤(sourceParameters N t).2.1 by have hh:=hf.short_pos; have ho:=hf.ordered; omega),hf.area]
    omega
  have hh := hmax.2 (canonicalDomain N) ((canonicalDomain_card hN).trans hsize.symm)
    (CanonicalStrips.canonicalDomain_connected hN)
  have hs := count_lt_canonical hN hT ht M hM hcard hdc hc hd
  omega

end
end SpanningTreeIsoperimetry.ThreeImbalanceExclusion
