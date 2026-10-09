import SpanningTreeIsoperimetry.SingleCornerSmallReduction
import SpanningTreeIsoperimetry.RectangularNotchEll

/-! Exhaustive actual exclusion of every nonstrip single Ferrers corner
when the two hull side lengths differ by two. -/
namespace SpanningTreeIsoperimetry.SingleCornerGapTwo
open Ferrers CornerEnergy CornerFolds CornerPrimalDomains CornerProfileNormalization
open SingleCornerSmallOrientation SingleCornerSmallReduction StripRigidity
noncomputable section

theorem not_maximal {u v : ℕ} {M : Diagram} (hM : IsFerrers M)
    (hk : M.card≤u) (hn : ¬IsStraightStrip M) (hgap : v-u=2) (c : Corner) :
    ¬IsMaximizer (cornerPrimal u v (singleFamily c M)) := by
  by_cases hh : 2<ferrersHeight M
  · exact tall_nonsquare_not_maximal hM (by omega) hk hn (by omega) c
  · rcases gap_two_cases hM hk hn (by omega) hgap c with hm|he|he
    · exact hm
    · subst M
      have hc : threeCell.card=3 := by decide +kernel
      rw [hc] at hk
      have hm := RectangularNotchEll.ell_not_maximal (r := u+1) (by omega) c
      simpa only [show u+1-1=u by omega,show u+1+2-1=v by omega] using hm
    · subst M
      have hc : (faceRectangle 2 2).card=4 := by decide +kernel
      rw [hc] at hk
      have hm := RectangularNotchComparison.notch_not_maximal (b := 2) (r := u+1)
        (Or.inl rfl) (by omega) c true
      simpa only [RectangularNotchComparison.notch,ite_true,
        show u+1-1=u by omega,show u+1+2-1=v by omega] using hm

end
end SpanningTreeIsoperimetry.SingleCornerGapTwo
