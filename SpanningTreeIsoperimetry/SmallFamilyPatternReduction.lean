import SpanningTreeIsoperimetry.SmallFamilyThreeCorners
import SpanningTreeIsoperimetry.SmallFamilyStripPairs
import SpanningTreeIsoperimetry.SmallFamilyNonstripPairs

/-! Exhaustive reduction of the first twenty small-family rows. Every
placement and every Ferrers shape is covered by support and size arguments. -/
namespace SpanningTreeIsoperimetry.SmallFamilyPatternReduction
open Ferrers CornerEnergy CornerPrimalDomains SmallFamilySourceBounds SmallFamilyPatternData
open SmallFamilyFoldable SmallFamilyStripPairs SmallFamilyNonstripPairs SmallFamilyThreeCorners
open StripRigidity
open scoped Classical
noncomputable section

theorem ordered_pair_rows {r a p q : ℕ} {A B : Diagram} {c d : Corner}
    (hcd : c≠d) (hA : IsFerrers A) (hB : IsFerrers B)
    (hAp : A.card=p) (hBq : B.card=q) (hp : 1≤p) (hpq : p≤q)
    (hsize : p+q<r) (harea : 18+(p+q)≤r*(r+a)) (hsupport : Supported a (p+q)) :
    Foldable a (twoCornerFamily c d A B) ∨ RowBound r a (p+q) (twoCornerFamily c d A B) := by
  by_cases hBS : IsStraightStrip B
  · by_cases hAS : IsStraightStrip A
    · exact strip_pair_rows hcd hAS hBS hAp hBq hp hpq hsize harea hsupport
    · have hp3 : 3≤p := by have h := nonstrip_card_ge_three hA hAS; omega
      have hk6 : p+q≤6 := by rcases hsupport with h|h|h <;> omega
      have hpq' : q≤p := by omega
      have hh := nonstrip_pair_rows (r := r) (a := a) hcd.symm hB hA hAS hBq hAp (by omega) hpq'
        (by omega) (show Supported a (q+p) by simpa only [Nat.add_comm] using hsupport)
      right
      rw [← twoCornerFamily_swap hcd A B] at hh
      simpa only [Nat.add_comm] using hh
  · exact Or.inr (nonstrip_pair_rows hcd hA hB hBS hAp hBq hp hpq hsize hsupport)

theorem supported_family_rows {r a k : ℕ} {M : Corner → Diagram}
    (hM : ∀ c, IsFerrers (M c)) (hcard : totalDefect M=k) (hsize : k<r)
    (harea : 18+k≤r*(r+a)) (hsupport : Supported a k)
    {c d : Corner} (hcd : c≠d) (hc : (M c).Nonempty) (hd : (M d).Nonempty) :
    Foldable a M ∨ RowBound r a k M := by
  rcases pair_or_three hcd hc hd with hpair|⟨e,hce,hde,he⟩
  · have hAB : (M c).card+(M d).card=k := by
      have ht := congrArg totalDefect hpair
      rw [totalDefect_twoCornerFamily hcd] at ht
      omega
    have hp := Finset.card_pos.mpr hc
    have hq := Finset.card_pos.mpr hd
    by_cases horder : (M c).card≤(M d).card
    · have hh := ordered_pair_rows hcd (hM c) (hM d) rfl rfl (by omega) horder
        (by omega : (M c).card+(M d).card<r)
        (by omega : 18+((M c).card+(M d).card)≤r*(r+a))
        (show Supported a ((M c).card+(M d).card) by rw [hAB]; exact hsupport)
      simpa only [← hpair,hAB] using hh
    · have hBA : (M d).card+(M c).card=k := by omega
      have hh := ordered_pair_rows hcd.symm (hM d) (hM c) rfl rfl (by omega) (by omega)
        (by omega : (M d).card+(M c).card<r)
        (by omega : 18+((M d).card+(M c).card)≤r*(r+a))
        (show Supported a ((M d).card+(M c).card) by rw [hBA]; exact hsupport)
      simpa only [← twoCornerFamily_swap hcd (M c) (M d),← hpair,hBA] using hh
  · exact Or.inr (three_corner_rows hM hcard hsize hsupport hcd hce hde hc hd he)

/-- Actual strict-fold or table-row alternative for every supported family. -/
theorem supported_family_alternative {N r a k : ℕ} {M : Corner → Diagram}
    (hN : 18≤N) (hM : ∀ c, IsFerrers (M c)) (hcard : totalDefect M=k) (hsize : k<r)
    (harea : r*(r+a)=N+k) (hsum : r+(r+a)=minimumSideSum N) (hsupport : Supported a k)
    {c d : Corner} (hcd : c≠d) (hc : (M c).Nonempty) (hd : (M d).Nonempty) :
    treeCount (cornerPrimal (r-1) (r+a-1) M)<treeCount (canonicalDomain N) ∨ RowBound r a k M := by
  rcases supported_family_rows hM hcard hsize (by omega) hsupport hcd hc hd with hf|hr
  · exact Or.inl (foldable_count_lt hN hcard hsize harea hsum hf)
  · exact Or.inr hr

end
end SpanningTreeIsoperimetry.SmallFamilyPatternReduction
