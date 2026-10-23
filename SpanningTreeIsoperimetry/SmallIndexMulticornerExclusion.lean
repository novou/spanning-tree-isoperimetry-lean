module

public import SpanningTreeIsoperimetry.SmallFamilyExclusion
public import SpanningTreeIsoperimetry.OddTwoImbalanceExclusion
public import SpanningTreeIsoperimetry.EvenTwoImbalanceExclusion
public import SpanningTreeIsoperimetry.ThreeImbalanceExclusion

@[expose] public section

/-! Complete actual multicorner exclusion for noncanonical selector indices≤3. -/
namespace SpanningTreeIsoperimetry.SmallIndexMulticornerExclusion
open Ferrers CornerEnergy CornerPrimalDomains SourceHullArithmetic
noncomputable section

theorem count_lt_canonical {N t : ℕ} (hN : 18≤N) (hT : canonicalIndex N≤3)
    (ht : t<canonicalIndex N) (M : Corner → Diagram) (hM : ∀ c,IsFerrers (M c))
    (hcard : totalDefect M=(sourceParameters N t).2.2)
    {c d : Corner} (hdc : d≠c) (hc : (M c).Nonempty) (hd : (M d).Nonempty) :
    treeCount (cornerPrimal ((sourceParameters N t).1-1) ((sourceParameters N t).2.1-1) M)<
      treeCount (canonicalDomain N) := by
  have hTs : canonicalIndex N=1 ∨ canonicalIndex N=2 ∨ canonicalIndex N=3 := by omega
  rcases hTs with hTs|hTs|hTs
  · exact SmallFamilyExclusion.first_twenty_regimes hN ht M hM hcard (Or.inl hTs) hdc.symm hc hd
  · have he : minimumSideSum N%2=0 ∨ minimumSideSum N%2=1 := by omega
    rcases he with he|he
    · by_cases hj : (canonicalParameters N).2.2≤2
      · exact SmallFamilyExclusion.first_twenty_regimes hN ht M hM hcard
          (Or.inr ⟨hTs,he,hj⟩) hdc.symm hc hd
      · have hj4 : (canonicalParameters N).2.2≤4 := by
          let m := minimumSideSum N/2
          let Δ := m*(m+minimumSideSum N%2)-N
          have hh := selector_remainder_lt_step (selectorIndex_bounds Δ (minimumSideSum N%2)).1
            (selectorIndex_bounds Δ (minimumSideSum N%2)).2
          change (canonicalParameters N).2.2<2*canonicalIndex N+minimumSideSum N%2+1 at hh
          rw [hTs,he] at hh
          omega
        exact EvenTwoImbalanceExclusion.count_lt_canonical (by omega) hTs he ht
          (by omega) M hM hcard hdc hc hd
    · exact OddTwoImbalanceExclusion.count_lt_canonical (by omega) hTs he ht M hM hcard hdc hc hd
  · exact ThreeImbalanceExclusion.count_lt_canonical (by omega) hTs ht M hM hcard hdc hc hd

theorem not_isMaximizer {N t : ℕ} (hN : 18≤N) (hT : canonicalIndex N≤3)
    (ht : t<canonicalIndex N) (M : Corner → Diagram) (hM : ∀ c,IsFerrers (M c))
    (hcard : totalDefect M=(sourceParameters N t).2.2)
    {c d : Corner} (hdc : d≠c) (hc : (M c).Nonempty) (hd : (M d).Nonempty) :
    ¬IsMaximizer (cornerPrimal ((sourceParameters N t).1-1) ((sourceParameters N t).2.1-1) M) := by
  intro hmax
  have hf := source_hull_facts (by omega : 0<N) ht.le
  have hr : totalDefect M≤(sourceParameters N t).1-1 := by
    rw [hcard]
    have hh := hf.deficit_lt_short
    omega
  have hs : totalDefect M≤(sourceParameters N t).2.1-1 := by have hh:=hf.ordered; omega
  have hsize : (cornerPrimal ((sourceParameters N t).1-1) ((sourceParameters N t).2.1-1) M).card=N := by
    rw [cornerPrimal_card hM hr hs,hcard,Nat.sub_add_cancel (show 1≤(sourceParameters N t).1 by have hh:=hf.short_pos; omega),
      Nat.sub_add_cancel (show 1≤(sourceParameters N t).2.1 by have hh:=hf.short_pos; have ho:=hf.ordered; omega),hf.area]
    omega
  have hh := hmax.2 (canonicalDomain N) ((canonicalDomain_card (by omega : 0<N)).trans hsize.symm)
    (CanonicalStrips.canonicalDomain_connected (by omega : 0<N))
  exact (not_le_of_gt (count_lt_canonical hN hT ht M hM hcard hdc hc hd)) hh

end
end SpanningTreeIsoperimetry.SmallIndexMulticornerExclusion
