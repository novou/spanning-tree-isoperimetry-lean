module

public import SpanningTreeIsoperimetry.CanonicalChecks
public import SpanningTreeIsoperimetry.CanonicalStrips
public import SpanningTreeIsoperimetry.LatticeCongruenceExtra

@[expose] public section

/-! All globally maximizing single strips are canonical, except the three
actual adjacent-hull ties at cardinalities 3, 8 and 10. -/
namespace SpanningTreeIsoperimetry.MaximizingStripClassification
open CanonicalStrips StripTreeComparisons StripPolarization
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem maximizing_strip_count {N r s k : ℕ} (hN : 0<N) (hr : 1≤r) (hrs : r≤s)
    (hk : k<r) (harea : r*s=N+k) (hsum : r+s=minimumSideSum N)
    (hm : IsMaximizer (cornerStrip r s k)) :
    treeCount (cornerStrip r s k)=treeCount (canonicalDomain N) := by
  apply le_antisymm (strip_le_canonical hN hr hrs hk harea hsum)
  have hc : (canonicalDomain N).card=(cornerStrip r s k).card := by
    rw [canonicalDomain_card hN,card_cornerStrip hr (by omega)]
    omega
  exact hm.2 (canonicalDomain N) hc (canonicalDomain_connected hN)

theorem canonical_maximal_of_strip {N r s k : ℕ} (hN : 0<N) (hr : 1≤r) (hrs : r≤s)
    (hk : k<r) (harea : r*s=N+k) (hsum : r+s=minimumSideSum N)
    (hm : IsMaximizer (cornerStrip r s k)) : IsMaximizer (canonicalDomain N) := by
  apply isMaximizer_of_same_count hm
  · rw [canonicalDomain_card hN,card_cornerStrip hr (by omega)]
    omega
  · exact canonicalDomain_connected hN
  · exact (maximizing_strip_count hN hr hrs hk harea hsum hm).symm

theorem maximizing_strip_parameters {N r s k : ℕ} (hN : 0<N) (hr : 1≤r) (hrs : r≤s)
    (hk : k<r) (harea : r*s=N+k) (hsum : r+s=minimumSideSum N)
    (hm : IsMaximizer (cornerStrip r s k)) :
    canonicalParameters N=(r,s,k) ∨
      (N=3 ∧ r=2 ∧ s=2 ∧ k=1) ∨
      (N=8 ∧ r=3 ∧ s=3 ∧ k=1) ∨
      (N=10 ∧ r=3 ∧ s=4 ∧ k=2) := by
  by_cases ht : k<s-r+1
  · exact Or.inl (terminal_parameters hN hr hrs harea hsum ht)
  have hg : s-r+1≤k := by omega
  have hcount := maximizing_strip_count hN hr hrs hk harea hsum hm
  have hchain := adjacent_hull_treeCount hr hrs hk hg
  have hnext := strip_le_canonical hN (by omega : 1≤r-1) (by omega : r-1≤s+1)
    (by omega : k-(s-r+1)<r-1) (next_hull_area hr hrs harea hg) (by omega)
  have heq : treeCount (cornerStrip r s k)=treeCount (cornerStrip (r-1) (s+1) (k-(s-r+1))) := by omega
  have he := (adjacent_hull_treeCount_eq_iff hr hrs hk hg).mp heq
  have hc := (adjacent_equality_triples hr hrs hk hg).mp he
  have hcan := canonical_maximal_of_strip hN hr hrs hk harea hsum hm
  simp only [Prod.mk.injEq] at hc
  rcases hc with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|
    ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
  · exact Or.inr (Or.inl ⟨by omega,rfl,rfl,rfl⟩)
  · have hn : N=7 := by omega
    subst N
    exact False.elim (canonicalDomain_not_maximal_seven hcan)
  · exact Or.inr (Or.inr (Or.inl ⟨by omega,rfl,rfl,rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by omega,rfl,rfl,rfl⟩))
  · have hn : N=14 := by omega
    subst N
    exact False.elim (canonicalDomain_not_maximal_fourteen hcan)
  · have hn : N=17 := by omega
    subst N
    exact False.elim (canonicalDomain_not_maximal_seventeen hcan)

theorem horizontal_card {r s k : ℕ} (hr : 1≤r) (hrs : r≤s) (hk : k<r) :
    (horizontalCornerStrip r s k).card=r*s-k := by
  rw [horizontal_eq_transpose,card_transposeDomain,card_cornerStrip (by omega) (by omega),Nat.mul_comm]

theorem maximizing_orientation_congruent {r s k : ℕ} (hr : 1≤r) (hrs : r≤s) (hk : k<r)
    (hm : IsMaximizer (horizontalCornerStrip r s k)) :
    Congruent (horizontalCornerStrip r s k) (cornerStrip r s k) := by
  have hlo := orientation_treeCount hr hrs hk
  have hhi := hm.2 (cornerStrip r s k)
    (by rw [card_cornerStrip hr (by omega),horizontal_card hr hrs hk])
    (cornerStrip_connected_of_short_deficit hr hrs hk)
  have he : treeCount (horizontalCornerStrip r s k)=treeCount (cornerStrip r s k) := by omega
  rcases (orientation_treeCount_eq_iff hr hrs hk).mp he with hsq|hsmall
  · subst s
    rw [horizontal_eq_transpose]
    exact congruent_transpose _
  · have hsets : horizontalCornerStrip r s k=cornerStrip r s k := by
      interval_cases k <;> ext p <;>
        simp only [horizontalCornerStrip,cornerStrip,Finset.mem_sdiff,mem_rectangle] <;> omega
    rw [hsets]
    exact congruent_refl _

end SpanningTreeIsoperimetry.MaximizingStripClassification
