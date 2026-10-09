import SpanningTreeIsoperimetry.SingleCornerSmallReduction
import SpanningTreeIsoperimetry.SingleCornerSmallEnergyBounds
import SpanningTreeIsoperimetry.RectangularNotchComparison

/-! The shallow odd-index-two single-corner alternatives: a strict actual
improvement or the exact strong quadrant-energy bound needed by its cost. -/
namespace SpanningTreeIsoperimetry.SingleCornerOddGeometry
open Ferrers CornerEnergy CornerFolds CornerPrimalDomains CornerProfileNormalization
open SingleCornerSmallOrientation SingleCornerSmallReduction SingleCornerSmallEnergyBounds
open RectangularNotchComparison StripRigidity
open scoped Classical
noncomputable section

private theorem rectangle_sides {a b : ℕ} (hne : (faceRectangle a b).Nonempty)
    (hn : ¬IsStraightStrip (faceRectangle a b)) : 2≤a ∧ 2≤b := by
  have hc : 0<a*b := by simpa [faceRectangle] using Finset.card_pos.mpr hne
  have ha : 0<a := by nlinarith
  have hb : 0<b := by nlinarith
  have ha1 : a≠1 := by
    intro he
    subst a
    apply hn
    right
    simpa [faceRectangle] using rectangle_vertical b
  have hb1 : b≠1 := by
    intro he
    subst b
    apply hn
    left
    simpa [faceRectangle] using rectangle_horizontal a
  omega

theorem odd_geometry_or_energy {r j : ℕ} {M : Diagram} (hM : IsFerrers M)
    (hn : ¬IsStraightStrip M) (hj : j≤5) (hk : M.card=j+4) (hr : j+6≤r)
    (c : Corner) :
    ¬IsMaximizer (cornerPrimal (r-1) (r+3-1) (singleFamily c M)) ∨
      (if j=0 then (2837 : ℝ)/50000 else 7421/100000)<realEnergy M := by
  by_cases hj0 : j=0
  · right
    simp only [hj0,ite_true]
    have hh := RefinedCornerEnvelope.nonstrip_absolute_lower hM hn
    norm_num at hh ⊢
    exact hh
  have hk5 : 5≤M.card := by omega
  have hcard : M.card≤9 := by omega
  by_cases hrect : IsRectangle M
  · obtain ⟨a,b,he⟩ := hrect
    change M=faceRectangle a b at he
    subst M
    obtain ⟨ha,hb⟩ := rectangle_sides (nonempty_of_not_straight hn) hn
    have hc : (faceRectangle a b).card=a*b := by simp [faceRectangle]
    rw [hc] at hk hk5 hcard
    by_cases ha3 : 3≤a
    · by_cases hb3 : 3≤b
      · right
        simp only [hj0,ite_false]
        exact rectangle_three_lower ha3 hb3
      · have hbe : b=2 := by omega
        subst b
        have hamax : a≤4 := by omega
        interval_cases a
        · left
          have he : j=2 := by omega
          have ht := notch_not_maximal (b := 3) (r := r) (Or.inr rfl) (by omega) c true
          simpa only [notch,ite_true] using ht
        · left
          apply two_row_wide_not_maximal hM (by omega) (by rw [hc]; omega) hn
          · decide +kernel
          · have hw : ferrersWidth (faceRectangle 4 2)=4 := by decide +kernel
            rw [hw]
            omega
    · have hae : a=2 := by omega
      subst a
      have hbmax : b≤4 := by omega
      have hb3 : 3≤b := by omega
      interval_cases b
      · left
        have ht := notch_not_maximal (b := 3) (r := r) (Or.inr rfl) (by omega) c false
        simpa only [notch,Bool.false_eq_true,ite_false] using ht
      · left
        apply tall_nonsquare_not_maximal hM (by omega) (by rw [hc]; omega) hn
        have hh : ferrersHeight (faceRectangle 2 4)=4 := by decide +kernel
        rw [hh]
        omega
  · right
    simp only [hj0,ite_false]
    exact nonrectangle_large_lower hM hk5 hrect

end
end SpanningTreeIsoperimetry.SingleCornerOddGeometry
