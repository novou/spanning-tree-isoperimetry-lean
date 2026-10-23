module

public import SpanningTreeIsoperimetry.SingleCornerSelectorGeometry
public import SpanningTreeIsoperimetry.SingleCornerCountComparison
public import SpanningTreeIsoperimetry.SingleCornerParameterCosts
public import SpanningTreeIsoperimetry.SingleCornerOddGeometry
public import SpanningTreeIsoperimetry.SingleCornerGapTwo

@[expose] public section

/-! Actual exclusion of nonstrip single corners at every positive
noncanonical source index when the canonical index is at most three. -/
namespace SpanningTreeIsoperimetry.SingleCornerSmallExclusion
open Ferrers CornerEnergy StripRigidity CornerPrimalDomains CornerProfileNormalization
open SourceHullArithmetic SingleCornerSelectorGeometry SingleCornerCountComparison
open SingleCornerParameterCosts SingleCornerOddGeometry SingleCornerSmallReduction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem two_middle_not_maximal {N : ℕ} (hN : 0<N) (hT : canonicalIndex N=2)
    {M : Diagram} (hM : IsFerrers M) (hn : ¬IsStraightStrip M)
    (hk : M.card=(sourceParameters N 1).2.2) (c : Corner) :
    ¬IsMaximizer (cornerPrimal ((sourceParameters N 1).1-1) ((sourceParameters N 1).2.1-1)
      (singleFamily c M)) := by
  let R := (canonicalParameters N).1
  let S := (canonicalParameters N).2.1
  let j := (canonicalParameters N).2.2
  let r := (sourceParameters N 1).1
  let s := (sourceParameters N 1).2.1
  have hd := two_middle_data hN hT
  have hd : r=R+1 ∧ s=r+2+minimumSideSum N%2 ∧ M.card=j+3+minimumSideSum N%2 ∧
    j≤4+minimumSideSum N%2 ∧ j+4+2*(minimumSideSum N%2)≤r := by
      simpa only [← hk] using hd
  have hf := source_hull_facts hN (show 1≤canonicalIndex N by omega)
  have hshort : M.card≤r-1 := by have hh := hf.deficit_lt_short; change (sourceParameters N 1).2.2<r at hh; omega
  have hside := (canonical_data hN).1
  change S=R+2*canonicalIndex N+minimumSideSum N%2 at hside
  rw [hT] at hside
  by_cases he : minimumSideSum N%2=0
  · rw [he] at hd hside
    apply SingleCornerGapTwo.not_maximal hM hshort hn
    have hp := hf.short_pos
    change 0<r at hp
    change s-1-(r-1)=2
    omega
  · have he1 : minimumSideSum N%2=1 := by omega
    rw [he1] at hd hside
    have hrlo : j+6≤r := by omega
    have hcard : M.card=j+4 := by omega
    have hj : j≤5 := by omega
    have hss : s=r+3 := by omega
    have hor := odd_geometry_or_energy hM hn hj hcard hrlo c
    rcases hor with hor|henergy
    · change ¬IsMaximizer (cornerPrimal (r-1) (s-1) (singleFamily c M))
      rw [hss]
      exact hor
    · apply not_maximal_of_cost hN (show 4≤(canonicalParameters N).1 by change 4≤R; omega)
        (show 1<canonicalIndex N by omega) hM hk c
      exact (odd_two_cost hj hrlo hd.1 hss (show S=r+4 by omega)).trans henergy

theorem three_positive_not_maximal {N t : ℕ} (hN : 0<N) (hT : canonicalIndex N=3)
    (ht0 : 1≤t) (ht : t<canonicalIndex N) {M : Diagram}
    (hM : IsFerrers M) (hn : ¬IsStraightStrip M) (hk : M.card=(sourceParameters N t).2.2)
    (c : Corner) :
    ¬IsMaximizer (cornerPrimal ((sourceParameters N t).1-1) ((sourceParameters N t).2.1-1)
      (singleFamily c M)) := by
  let R := (canonicalParameters N).1
  let S := (canonicalParameters N).2.1
  let j := (canonicalParameters N).2.2
  let r := (sourceParameters N t).1
  let s := (sourceParameters N t).2.1
  have hd := three_data hN hT
  change S=R+6+minimumSideSum N%2 ∧ j≤6+minimumSideSum N%2 ∧ j+7+3*(minimumSideSum N%2)≤R at hd
  have hf := source_hull_facts hN ht.le
  have hR : 4≤(canonicalParameters N).1 := by change 4≤R; omega
  by_cases he : minimumSideSum N%2=0
  · rw [he] at hd
    by_cases ht1 : t=1
    · subst t
      have hs := (three_first_data hN hT).2.1
      rw [he] at hs
      have hshort : M.card≤(sourceParameters N 1).1-1 := by rw [hk]; have hh := hf.deficit_lt_short; omega
      apply SingleCornerGapTwo.not_maximal hM hshort hn
      have hp := hf.short_pos
      omega
    · have ht2 : t=2 := by omega
      subst t
      have hs := three_second_data hN hT
      rw [he] at hs
      apply not_maximal_of_cost hN hR ht hM hk c
      apply even_three_cost (show j≤6 by omega) (show j+7≤R by omega) hs.1
        (show (sourceParameters N 2).2.1=(sourceParameters N 2).1+4 by omega)
        (show S=R+6 by omega) hM hn
      omega
  · have he1 : minimumSideSum N%2=1 := by omega
    rw [he1] at hd
    have hr : r=R+1 ∨ r=R+2 := by
      by_cases ht1 : t=1
      · right
        simpa only [r,R,ht1] using (three_first_data hN hT).1
      · left
        have ht2 : t=2 := by omega
        simpa only [r,R,ht2] using (three_second_data hN hT).1
    have hcard : j+5≤M.card := by
      by_cases ht1 : t=1
      · have hh := (three_first_data hN hT).2.2.1
        rw [he1] at hh
        rw [ht1] at hk
        change M.card=(sourceParameters N 1).2.2 at hk
        omega
      · have ht2 : t=2 := by omega
        have hh := (three_second_data hN hT).2.2.1
        rw [he1] at hh
        rw [ht2] at hk
        omega
    have hsum : r+s=2*R+7 := by
      have hsrc := hf.side_sum
      have htar := (source_hull_facts hN (le_refl (canonicalIndex N))).side_sum
      rw [source_at_canonical] at htar
      change r+s=minimumSideSum N at hsrc
      change R+S=minimumSideSum N at htar
      omega
    apply not_maximal_of_cost hN hR ht hM hk c
    exact odd_three_cost (show j≤7 by omega) (show j+10≤R by omega) hr hsum
      (show S=R+7 by omega) hM hn hcard

theorem positive_index_not_maximal {N t : ℕ} (hN : 0<N) (hT : canonicalIndex N≤3)
    (ht0 : 1≤t) (ht : t<canonicalIndex N) {M : Diagram}
    (hM : IsFerrers M) (hn : ¬IsStraightStrip M) (hk : M.card=(sourceParameters N t).2.2)
    (c : Corner) :
    ¬IsMaximizer (cornerPrimal ((sourceParameters N t).1-1) ((sourceParameters N t).2.1-1)
      (singleFamily c M)) := by
  rcases (show canonicalIndex N=2 ∨ canonicalIndex N=3 by omega) with h2|h3
  · have ht1 : t=1 := by omega
    subst t
    exact two_middle_not_maximal hN h2 hM hn hk c
  · exact three_positive_not_maximal hN h3 ht0 ht hM hn hk c

end
end SpanningTreeIsoperimetry.SingleCornerSmallExclusion
