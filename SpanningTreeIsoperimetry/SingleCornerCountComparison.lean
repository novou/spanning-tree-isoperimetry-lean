module

public import SpanningTreeIsoperimetry.SingleCornerSmallOrientation
public import SpanningTreeIsoperimetry.NormalizedRectangleError
public import SpanningTreeIsoperimetry.CrossHullCountComparison
public import SpanningTreeIsoperimetry.SourceHullArithmetic

@[expose] public section

/-! Actual count transport for a single occupied corner. The rectangle error
is discharged by the checked normalized absorption theorem. -/
namespace SpanningTreeIsoperimetry.SingleCornerCountComparison
open Ferrers CornerEnergy CornerPrimalDomains CornerProfileNormalization SingleCornerSmallOrientation
open SourceHullArithmetic CrossHullCountComparison AspectCost FluxBounds
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem single_energy_sum (c : Corner) (M : Diagram) :
    (∑ d,realEnergy (singleFamily c M d))=realEnergy M := by
  simp [singleFamily,twoCornerFamily,apply_ite,realEnergy_empty]

theorem count_lt_of_cost {N t : ℕ} (hN : 0<N) (hR : 4≤(canonicalParameters N).1)
    (ht : t<canonicalIndex N) {M : Diagram} (hM : IsFerrers M)
    (hk : M.card=(sourceParameters N t).2.2) (c : Corner)
    (hcost : realEnergy (horizontalStrip (canonicalParameters N).2.2)+
      D (aspectOffset (canonicalParameters N).1 (canonicalParameters N).2.1)-
      D (aspectOffset (sourceParameters N t).1 (sourceParameters N t).2.1)+
      fluxBound (canonicalParameters N).1 (canonicalParameters N).2.1 (canonicalParameters N).2.2<
        realEnergy M) :
    treeCount (cornerPrimal ((sourceParameters N t).1-1) ((sourceParameters N t).2.1-1)
      (singleFamily c M))<treeCount (canonicalDomain N) := by
  let r := (sourceParameters N t).1
  let s := (sourceParameters N t).2.1
  let k := (sourceParameters N t).2.2
  let R := (canonicalParameters N).1
  let S := (canonicalParameters N).2.1
  let j := (canonicalParameters N).2.2
  have hf := source_hull_facts hN ht.le
  have htar := selected_hull_properties_of_ceil hN
  change 0<R ∧ R≤S ∧ R+S=minimumSideSum N ∧ R*S=N+j ∧ j<R at htar
  have htarget := (source_hull_facts hN (le_refl (canonicalIndex N))).side_difference
  rw [source_at_canonical] at htarget
  change S=R+2*canonicalIndex N+minimumSideSum N%2 at htarget
  have hj : j+1<S := by omega
  have hMF := singleFamily_ferrers c hM
  have htotal : totalDefect (singleFamily c M)=k := by rw [singleFamily_total,hk]
  have hr : totalDefect (singleFamily c M)≤r-1 := by
    have hh := hf.deficit_lt_short
    change k<r at hh
    omega
  have hs : totalDefect (singleFamily c M)≤s-1 := by
    have hh := hf.ordered
    change r≤s at hh
    omega
  have harea : r*s=N+k := hf.area
  have hsum : r+s=minimumSideSum N := hf.side_sum
  change treeCount (cornerPrimal (r-1) (s-1) (singleFamily c M))<treeCount (cornerStrip R S j)
  apply count_lt_of_normalized_cost (show 3≤R by omega) hf.canonical_short_le hf.ordered
    hf.long_le_canonical (singleFamily c M) hMF hr hs hj
    (show r*s+j=R*S+totalDefect (singleFamily c M) by omega) (show r+s=R+S by omega)
  · rw [htotal]
    exact (NormalizedRectangleError.source_absorption hN hR ht).le
  · rw [single_energy_sum]
    exact hcost

theorem not_maximal_of_cost {N t : ℕ} (hN : 0<N) (hR : 4≤(canonicalParameters N).1)
    (ht : t<canonicalIndex N) {M : Diagram} (hM : IsFerrers M)
    (hk : M.card=(sourceParameters N t).2.2) (c : Corner)
    (hcost : realEnergy (horizontalStrip (canonicalParameters N).2.2)+
      D (aspectOffset (canonicalParameters N).1 (canonicalParameters N).2.1)-
      D (aspectOffset (sourceParameters N t).1 (sourceParameters N t).2.1)+
      fluxBound (canonicalParameters N).1 (canonicalParameters N).2.1 (canonicalParameters N).2.2<
        realEnergy M) :
    ¬IsMaximizer (cornerPrimal ((sourceParameters N t).1-1) ((sourceParameters N t).2.1-1)
      (singleFamily c M)) := by
  have hf := source_hull_facts hN ht.le
  have hr : M.card≤(sourceParameters N t).1-1 := by rw [hk]; have hh := hf.deficit_lt_short; omega
  have hs : M.card≤(sourceParameters N t).2.1-1 := by have hh := hf.ordered; omega
  have hsize : (cornerPrimal ((sourceParameters N t).1-1) ((sourceParameters N t).2.1-1)
      (singleFamily c M)).card=N := by
    rw [single_card c hM hr hs,hk,
      Nat.sub_add_cancel (show 1≤(sourceParameters N t).1 by have hh := hf.short_pos; omega),
      Nat.sub_add_cancel (show 1≤(sourceParameters N t).2.1 by have hh := hf.short_pos; have ho := hf.ordered; omega),hf.area]
    omega
  intro hmax
  have hm := hmax.2 (canonicalDomain N) ((canonicalDomain_card hN).trans hsize.symm)
    (CanonicalStrips.canonicalDomain_connected hN)
  exact (not_lt_of_ge hm) (count_lt_of_cost hN hR ht hM hk c hcost)

end
end SpanningTreeIsoperimetry.SingleCornerCountComparison
