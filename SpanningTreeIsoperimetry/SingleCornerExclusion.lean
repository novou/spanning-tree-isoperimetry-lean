import SpanningTreeIsoperimetry.SquareSingleCornerExclusion
import SpanningTreeIsoperimetry.SingleCornerSmallExclusion

/-! Every nonstrip single corner on a minimum-side-sum hull is excluded,
including the square-hook alternative, with all corner placements allowed. -/
namespace SpanningTreeIsoperimetry.SingleCornerExclusion
open Ferrers CornerEnergy CornerPrimalDomains CornerProfileNormalization StripRigidity
open SourceHullArithmetic SingleCornerSmallOrientation
open scoped Classical
noncomputable section

theorem single_not_concentrated {M : Diagram} (hn : ¬IsStraightStrip M) (c : Corner) :
    ¬CornerConcentration.IsConcentrated Finset.univ (singleFamily c M) := by
  rintro ⟨d,_,hd,hs,ho⟩
  by_cases hcd : c=d
  · subst d
    exact hn (by simpa [singleFamily,twoCornerFamily] using hs)
  · have he := ho c (Finset.mem_univ c) hcd
    have he : M=∅ := by simpa [singleFamily,twoCornerFamily] using he
    exact (nonempty_of_not_straight hn).ne_empty he

theorem not_isMaximizer {N r s : ℕ} {M : Diagram} (hN : 18≤N) (hrs : r≤s)
    (hM : IsFerrers M) (hn : ¬IsStraightStrip M) (hk : M.card<r)
    (harea : r*s=N+M.card) (hsum : r+s=minimumSideSum N) (c : Corner) :
    ¬IsMaximizer (cornerPrimal (r-1) (s-1) (singleFamily c M)) := by
  intro hm
  have hpos : 0<N := by omega
  have hr : 1≤r := by omega
  have hs : 1≤s := by omega
  have hsrc : (cornerPrimal (r-1) (s-1) (singleFamily c M)).card=N := by
    rw [single_card c hM (by omega) (by omega),Nat.sub_add_cancel hr,Nat.sub_add_cancel hs,harea]
    omega
  have hmax := hm.2 (canonicalDomain N) ((canonicalDomain_card hpos).trans hsrc.symm)
    (CanonicalStrips.canonicalDomain_connected hpos)
  have hF := singleFamily_ferrers c hM
  have htotal := singleFamily_total c M
  have hnot := single_not_concentrated hn c
  obtain ⟨ht,hp⟩ := source_parameters_of_hull hpos (by omega : 0<r) hrs harea hsum
  let t := minimumSideSum N/2-r
  change t≤canonicalIndex N at ht
  change sourceParameters N t=(r,s,M.card) at hp
  by_cases he : t=canonicalIndex N
  · rw [he,source_at_canonical] at hp
    have hk2 : 2≤M.card := by
      by_contra hh
      exact hn (SmallShapeCatalogue.ferrers_two_cell_strip hM (by omega))
    have hh := CanonicalCornerConcentration.canonical_nonstrip_strict hN hp hk2 hF htotal hnot
    have hh : treeCount (cornerPrimal (r-1) (s-1) (singleFamily c M))<treeCount (canonicalDomain N) := by
      simpa only [canonicalDomain,hp] using hh
    exact hh.not_ge hmax
  · have htt : t<canonicalIndex N := by omega
    have hsrcDef : M.card=(sourceParameters N t).2.2 := by rw [hp]
    by_cases hT : 4≤canonicalIndex N
    · have hcard : totalDefect (singleFamily c M)=(sourceParameters N t).2.2 := htotal.trans hsrcDef
      have hh := LargeImbalanceExclusion.count_lt_canonical hpos hT htt (singleFamily c M) hF hcard hnot
      rw [hp] at hh
      exact hh.not_ge hmax
    · by_cases ht0 : t=0
      · have hp0 : sourceParameters N 0=(r,s,M.card) := by simpa only [ht0] using hp
        by_cases he0 : minimumSideSum N%2=0
        · have hside := (source_hull_facts hpos (Nat.zero_le (canonicalIndex N))).side_difference
          rw [hp0,he0] at hside
          norm_num at hside
          have heq : s=r := by omega
          subst s
          exact (SquareSingleCornerExclusion.not_isMaximizer hN hM (by omega : M.card≤r-1) hn
            (by simpa only [Nat.sub_add_cancel hr] using harea)
            (by simpa only [Nat.sub_add_cancel hr] using hsum) c) hm
        · have he1 : minimumSideSum N%2=1 := by omega
          have hh := SingleCornerZeroReduction.zero_odd_not_maximal hpos he1 hM hn
            (show M.card=(sourceParameters N 0).2.2 by rw [hp0]) c
          rw [hp0] at hh
          exact hh hm
      · have hh := SingleCornerSmallExclusion.positive_index_not_maximal hpos (by omega) (by omega : 1≤t)
          htt hM hn hsrcDef c
        rw [hp] at hh
        exact hh hm

end
end SpanningTreeIsoperimetry.SingleCornerExclusion
