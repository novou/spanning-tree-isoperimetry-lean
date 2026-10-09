import SpanningTreeIsoperimetry.SmallIndexMulticornerExclusion
import SpanningTreeIsoperimetry.LargeImbalanceExclusion
import SpanningTreeIsoperimetry.CanonicalCornerConcentration

/-! Actual exclusion of every multicorner family on a minimum-side-sum hull.
The small-index and large-index actual count estimates are fully instantiated. -/
namespace SpanningTreeIsoperimetry.MulticornerExclusion
open Ferrers CornerEnergy CornerPrimalDomains SourceHullArithmetic
open scoped Classical
noncomputable section

theorem count_lt_canonical {N r s k : ℕ} (hN : 18≤N) (hrs : r≤s)
    (hk : k<r) (harea : r*s=N+k) (hsum : r+s=minimumSideSum N)
    (M : Corner → Diagram) (hM : ∀ c,IsFerrers (M c)) (hcard : totalDefect M=k)
    {c d : Corner} (hcd : c≠d) (hc : (M c).Nonempty) (hd : (M d).Nonempty) :
    treeCount (cornerPrimal (r-1) (s-1) M)<treeCount (canonicalDomain N) := by
  have hpos : 0<N := by omega
  have hk2 : 2≤k := by
    have h := SmallFamilyExclusion.two_nonempty_total hcd hc hd
    omega
  have hnot := MulticornerEnergyMinimum.not_concentrated_of_two Finset.univ M
    (Finset.mem_univ c) (Finset.mem_univ d) hcd.symm hc hd
  obtain ⟨ht,hp⟩ := source_parameters_of_hull hpos (by omega : 0<r) hrs harea hsum
  let t := minimumSideSum N/2-r
  change t≤canonicalIndex N at ht
  change sourceParameters N t=(r,s,k) at hp
  by_cases he : t=canonicalIndex N
  · rw [he,source_at_canonical] at hp
    have hh := CanonicalCornerConcentration.canonical_nonstrip_strict hN hp hk2 hM hcard hnot
    simpa only [canonicalDomain,hp] using hh
  · have htt : t<canonicalIndex N := by omega
    have hsrc : totalDefect M=(sourceParameters N t).2.2 := by rw [hp]; exact hcard
    by_cases hT : 4≤canonicalIndex N
    · have hh := LargeImbalanceExclusion.count_lt_canonical hpos hT htt M hM hsrc hnot
      simpa only [hp] using hh
    · have hh := SmallIndexMulticornerExclusion.count_lt_canonical hN (by omega) htt M hM hsrc
        hcd.symm hc hd
      simpa only [hp] using hh

theorem not_isMaximizer {N r s k : ℕ} (hN : 18≤N) (hrs : r≤s)
    (hk : k<r) (harea : r*s=N+k) (hsum : r+s=minimumSideSum N)
    (M : Corner → Diagram) (hM : ∀ c,IsFerrers (M c)) (hcard : totalDefect M=k)
    {c d : Corner} (hcd : c≠d) (hc : (M c).Nonempty) (hd : (M d).Nonempty) :
    ¬IsMaximizer (cornerPrimal (r-1) (s-1) M) := by
  intro hm
  have hR : totalDefect M≤r-1 := by omega
  have hS : totalDefect M≤s-1 := by omega
  have hsize : (cornerPrimal (r-1) (s-1) M).card=N := by
    rw [cornerPrimal_card hM hR hS,hcard,Nat.sub_add_cancel (by omega : 1≤r),
      Nat.sub_add_cancel (by omega : 1≤s),harea]
    omega
  have hb := hm.2 (canonicalDomain N)
    ((canonicalDomain_card (by omega : 0<N)).trans hsize.symm)
    (CanonicalStrips.canonicalDomain_connected (by omega : 0<N))
  exact (count_lt_canonical hN hrs hk harea hsum M hM hcard hcd hc hd).not_ge hb

end
end SpanningTreeIsoperimetry.MulticornerExclusion
