import SpanningTreeIsoperimetry.CornerProfileNormalization
import SpanningTreeIsoperimetry.TwoCornerStripTree
import SpanningTreeIsoperimetry.CanonicalStrips

/-! Actual strict canonical improvements for every two-strip family having
one strip of length equal to the hull gap plus two, in every placement. -/
namespace SpanningTreeIsoperimetry.FoldableCornerPairs
open Ferrers CornerEnergy CornerPrimalDomains CornerProfileNormalization
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem pair_le_opposite {R S : ℕ} {A B : Diagram} {c d : Corner} (hcd : c≠d)
    (hA : IsFerrers A) (hB : IsFerrers B) (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hR : A.card+B.card≤R) (hS : A.card+B.card≤S) :
    treeCount (cornerPrimal R S (twoCornerFamily c d A B))≤treeCount (oppositePrimal R S A B) := by
  by_cases hd : d=opposite c
  · subst d
    exact (pair_normalization c hA hB hR hS).treeCount_eq.le
  · have hn := (cornerPrimal_reflect_congruent c (pair_family_fit hcd hA hB hR hS)).treeCount_eq
    simp only [reflectedFamily_twoCornerFamily,reflectCorner_self] at hn
    rcases adjacent_normal_forms c d hcd hd with hnormal|hnormal
    · rw [hn,hnormal]
      exact (separate_corners_treeCount A B hA hB hneA hneB hR hS).le
    · rw [hn,hnormal]
      have hsource := (cornerPrimal_transpose_congruent
        (pair_family_fit (by decide : (true,true)≠(true,false)) hA hB hR hS)).treeCount_eq
      have htarget := (cornerPrimal_transpose_congruent
        (pair_family_fit (by decide : (true,true)≠(false,false)) hA hB hR hS)).treeCount_eq
      rw [transposedFamily_twoCornerFamily] at hsource htarget
      have hna : (transpose A).Nonempty := by simpa only [transpose] using hneA.image Prod.swap
      have hnb : (transpose B).Nonempty := by simpa only [transpose] using hneB.image Prod.swap
      have hsep := separate_corners_treeCount (transpose A) (transpose B)
        (transpose_isFerrers hA) (transpose_isFerrers hB) hna hnb
        (by simpa only [card_transpose] using hS) (by simpa only [card_transpose] using hR)
      change treeCount (cornerPrimal R S (twoCornerFamily (true,true) (true,false) A B))≤
        treeCount (cornerPrimal R S (twoCornerFamily (true,true) (false,false) A B))
      rw [hsource,htarget]
      exact hsep.le

theorem opposite_fold_lt_canonical {N r s b : ℕ} (hN : 18≤N) (hrs : r≤s) (hb : 1≤b)
    (hsize : s-r+b+2<r) (harea : r*s=N+(s-r+2+b)) (hsum : r+s=minimumSideSum N)
    (v w : Bool) :
    treeCount (twoStripPrimal r s (s-r+2) b v w)<treeCount (canonicalDomain N) := by
  have hfold := two_corner_fold_treeCount hrs hb hsize v w
  have hstrict : treeCount (twoStripPrimal r s (s-r+2) b v w)<
      treeCount (cornerStrip (r-1) (s+1) (b+1)) := by
    apply lt_of_le_of_ne hfold
    intro he
    obtain ⟨hr,hs,hb⟩ := (two_corner_fold_treeCount_eq_iff hrs hb hsize v w).mp he
    subst r
    subst s
    subst b
    norm_num at harea
    omega
  have hrr : r-1+1=r := by omega
  have hsr : s-r+r=s := Nat.sub_add_cancel hrs
  have htarget : (r-1)*(s+1)=N+(b+1) := by nlinarith
  have hcanon := CanonicalStrips.strip_le_canonical (by omega : 0<N) (by omega : 1≤r-1)
    (by omega : r-1≤s+1) (by omega : b+1<r-1) htarget (by omega)
  exact hstrict.trans_le hcanon

/-- This closes every folded row in the small-imbalance multicorner table:
all strip orientations and all distinct corner placements are included. -/
theorem foldable_pair_lt_canonical {N r s b : ℕ} (hN : 18≤N) (hrs : r≤s) (hb : 1≤b)
    (hsize : s-r+b+2<r) (harea : r*s=N+(s-r+2+b)) (hsum : r+s=minimumSideSum N)
    {c d : Corner} (hcd : c≠d) (v w : Bool) :
    treeCount (cornerPrimal (r-1) (s-1)
      (twoCornerFamily c d (stripDiagram (s-r+2) v) (stripDiagram b w)))<treeCount (canonicalDomain N) := by
  have hA := stripDiagram_ferrers (s-r+2) v
  have hB := stripDiagram_ferrers b w
  have hna : (stripDiagram (s-r+2) v).Nonempty := by
    apply Finset.card_pos.mp
    rw [stripDiagram_card]
    omega
  have hnb : (stripDiagram b w).Nonempty := by
    apply Finset.card_pos.mp
    rw [stripDiagram_card]
    omega
  have hp := pair_le_opposite hcd hA hB hna hnb
    (by simp only [stripDiagram_card]; omega : (stripDiagram (s-r+2) v).card+(stripDiagram b w).card≤r-1)
    (by simp only [stripDiagram_card]; omega : (stripDiagram (s-r+2) v).card+(stripDiagram b w).card≤s-1)
  exact hp.trans_lt (opposite_fold_lt_canonical hN hrs hb hsize harea hsum v w)

end
end SpanningTreeIsoperimetry.FoldableCornerPairs
