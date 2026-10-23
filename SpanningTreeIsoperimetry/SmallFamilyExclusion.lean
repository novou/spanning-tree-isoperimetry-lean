module

public import SpanningTreeIsoperimetry.SmallFamilyRowComparison
public import SpanningTreeIsoperimetry.SmallFamilyPatternReduction
public import SpanningTreeIsoperimetry.SourceHullArithmetic

@[expose] public section

/-! Actual count exclusion for every multicorner family in the first table. -/
namespace SpanningTreeIsoperimetry.SmallFamilyExclusion
open Ferrers CornerEnergy CornerPrimalDomains SmallFamilyPatternData
  SmallFamilyRowComparison SmallFamilyPatternReduction SourceHullArithmetic
noncomputable section

theorem supported_family_lt_canonical {N r a k : ℕ} (hN : 18≤N)
    (M : Corner → Diagram) (hM : ∀ c,IsFerrers (M c)) (hcard : totalDefect M=k)
    (hsize : k<r) (harea : r*(r+a)=N+k) (hsum : r+(r+a)=minimumSideSum N)
    (hsupport : Supported a k) {c d : Corner} (hcd : c≠d)
    (hc : (M c).Nonempty) (hd : (M d).Nonempty) :
    treeCount (cornerPrimal (r-1) (r+a-1) M)<treeCount (canonicalDomain N) := by
  rcases supported_family_alternative hN hM hcard hsize harea hsum hsupport hcd hc hd with h|h
  · exact h
  · exact row_bound_lt_canonical hN M hM hcard hsize harea hsum h

theorem source_hull_lt_of_supported {N t : ℕ} (hN : 18≤N) (ht : t≤canonicalIndex N)
    (M : Corner → Diagram) (hM : ∀ c,IsFerrers (M c))
    (hcard : totalDefect M=(sourceParameters N t).2.2)
    (hsupport : Supported (2*t+minimumSideSum N%2) (sourceParameters N t).2.2)
    {c d : Corner} (hcd : c≠d) (hc : (M c).Nonempty) (hd : (M d).Nonempty) :
    treeCount (cornerPrimal ((sourceParameters N t).1-1) ((sourceParameters N t).2.1-1) M)<
      treeCount (canonicalDomain N) := by
  have hf := source_hull_facts (by omega : 0<N) ht
  have hside : (sourceParameters N t).2.1=(sourceParameters N t).1+(2*t+minimumSideSum N%2) := by
    simpa only [Nat.add_assoc] using hf.side_difference
  rw [hside]
  apply supported_family_lt_canonical hN M hM hcard hf.deficit_lt_short
    (by simpa only [hside] using hf.area) (by simpa only [hside] using hf.side_sum)
    hsupport hcd hc hd

theorem source_parameters_supported {N t : ℕ} (ht : t<canonicalIndex N)
    (hk : 2≤(sourceParameters N t).2.2)
    (hreg : canonicalIndex N=1 ∨ (canonicalIndex N=2 ∧ minimumSideSum N%2=0 ∧
      (canonicalParameters N).2.2≤2)) :
    Supported (2*t+minimumSideSum N%2) (sourceParameters N t).2.2 := by
  let m := minimumSideSum N/2
  let e := minimumSideSum N%2
  let d := m*(m+e)-N
  have he : e≤1 := by dsimp [e]; omega
  have hb := selectorIndex_bounds d e
  have hj := selector_remainder_lt_step hb.1 hb.2
  have hfeas := hb.1
  change canonicalIndex N*(canonicalIndex N+e)≤d at hfeas
  change d-canonicalIndex N*(canonicalIndex N+e)<2*canonicalIndex N+e+1 at hj
  change 2≤d-t*(t+e) at hk
  change Supported (2*t+e) (d-t*(t+e))
  rcases hreg with hT|⟨hT,he0,hj2⟩
  · have ht0 : t=0 := by omega
    subst t
    rw [hT] at hj
    interval_cases e <;> norm_num [Supported] at hk hj ⊢ <;> omega
  · have ht1 : t≤1 := by omega
    have he0' : e=0 := he0
    change d-canonicalIndex N*(canonicalIndex N+e)≤2 at hj2
    rw [hT,he0'] at hj2
    rw [hT,he0'] at hfeas
    rw [he0']
    interval_cases t <;> norm_num [Supported] at hk hj2 hfeas ⊢ <;> omega

theorem two_nonempty_total {M : Corner → Diagram} {c d : Corner} (hcd : c≠d)
    (hc : (M c).Nonempty) (hd : (M d).Nonempty) : 2≤totalDefect M := by
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun c : Corner => (M c).card)
    (Finset.subset_univ ({c,d} : Finset Corner)) (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_pair hcd] at hsum
  change (M c).card+(M d).card≤totalDefect M at hsum
  have hc0 := Finset.card_pos.mpr hc
  have hd0 := Finset.card_pos.mpr hd
  omega

theorem first_twenty_regimes {N t : ℕ} (hN : 18≤N) (ht : t<canonicalIndex N)
    (M : Corner → Diagram) (hM : ∀ c,IsFerrers (M c))
    (hcard : totalDefect M=(sourceParameters N t).2.2)
    (hreg : canonicalIndex N=1 ∨ (canonicalIndex N=2 ∧ minimumSideSum N%2=0 ∧
      (canonicalParameters N).2.2≤2))
    {c d : Corner} (hcd : c≠d) (hc : (M c).Nonempty) (hd : (M d).Nonempty) :
    treeCount (cornerPrimal ((sourceParameters N t).1-1) ((sourceParameters N t).2.1-1) M)<
      treeCount (canonicalDomain N) := by
  have hk := two_nonempty_total hcd hc hd
  rw [hcard] at hk
  exact source_hull_lt_of_supported hN ht.le M hM hcard
    (source_parameters_supported ht hk hreg) hcd hc hd

end
end SpanningTreeIsoperimetry.SmallFamilyExclusion
