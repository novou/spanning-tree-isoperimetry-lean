import SpanningTreeIsoperimetry.RectangularNotchComparison

/-! The remaining L-shaped single-corner notch, with its actual weighted
finite correction and same-cardinality rectangular competitor. -/
namespace SpanningTreeIsoperimetry.RectangularNotchEll
open Ferrers CornerEnergy CornerPrimalDomains CornerProfileNormalization SingleCornerSmallOrientation
open CrossHullCountComparison SmallFamilySourceBounds SmallFamilyCountComparison
open SmallFamilyProfiles SmallFamilyMonotonicity SmallFamilyCostBounds MulticornerEndpointChecks
open SmallCornerCorrections
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

private theorem threeCell_isFerrers : IsFerrers threeCell := by
  intro p hp q hqx hqy
  simp only [threeCell,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] at hp ⊢
  rcases hp with h|h|h <;> rcases p with ⟨x,y⟩ <;> rcases q with ⟨a,b⟩ <;> simp_all only [Prod.mk.injEq] <;> omega

theorem ell_correction {r : ℕ} (hr : 4≤r) :
    (10/3 : ℝ)/(r : ℝ)^4+(5/3 : ℝ)/((r : ℝ)-1)^4<
      correction (faceRectangle (r-1) (r+2-1)) threeCell := by
  have h := correction_ge_cell_sum (r-1) (r+2-1) threeCell
  have h0 := single_ordered_lower (r := r) (s := r+2) (by omega) (by omega)
  have h1 := single_ordered_lower (r := r-1) (s := r+2) (by omega) (by omega)
  have h2 := single_ordered_lower (r := r) (s := r+1) (by omega) (by omega)
  have he : ((r-1 : ℕ) : ℝ)=(r : ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  rw [he] at h1
  have hn : r+2-1-1=r+1-1 := by omega
  norm_num [threeCell,Nat.sub_zero,hn] at h
  change 5/(3*(r : ℝ)^4)<correction (faceRectangle (r-1) (r+2-1)) {(0,0)} at h0
  change 5/(3*((r : ℝ)-1)^4)<correction (faceRectangle (r-1-1) (r+2-1)) {(0,0)} at h1
  change 5/(3*(r : ℝ)^4)<correction (faceRectangle (r-1) (r+1-1)) {(0,0)} at h2
  have hid : (10/3 : ℝ)/(r : ℝ)^4+(5/3 : ℝ)/((r : ℝ)-1)^4=
      2*(5/(3*(r : ℝ)^4))+5/(3*((r : ℝ)-1)^4) := by simp only [div_div]; ring
  norm_num only [threeCell,show r+2-1=r+1 by omega,show r+1-1=r by omega] at h0 h1 h2 ⊢
  linarith only [h,h0,h1,h2,hid]

theorem ell_count {r : ℕ} (hr : 4≤r) (c : Corner) :
    treeCount (cornerPrimal (r-1) (r+2-1) (singleFamily c threeCell))<
      treeCount (cornerStrip (r-1) (r+3) 0) := by
  have hM := singleFamily_ferrers c threeCell_isFerrers
  have hcard : threeCell.card=3 := by decide +kernel
  have hshort : totalDefect (singleFamily c threeCell)≤r-1 := by rw [singleFamily_total,hcard]; omega
  have hlong : totalDefect (singleFamily c threeCell)≤r+2-1 := by rw [singleFamily_total,hcard]; omega
  have harea : r*(r+2)+0=(r-1)*(r+3)+totalDefect (singleFamily c threeCell) := by
    rw [singleFamily_total,hcard]
    have he := Nat.sub_add_cancel (show 1≤r by omega)
    nlinarith
  have hcost := endpointCost_lt_floor (i := 25) (r := (r : ℝ))
    (by norm_num [leftEnd]; exact_mod_cast hr)
  apply count_lt_of_profile (R := r-1) (r := r) (s := r+2) (S := r+3) (a := 2) (h := 1)
    (j := 0) (by omega) (by omega) (by omega) rfl (by omega) (by omega)
    (singleFamily c threeCell) hM hshort hlong (by omega) harea 25
  · norm_num [gap]
  · norm_num [hullShift]
  · norm_num [sourceShift]
  · norm_num [errorCoeff]
    split_ifs <;> norm_num
  · exact hcost
  · have hu := finite_target_upper (R := r-1) (S := r+3) (j := 0) (by omega) (by omega) (by omega)
    simpa [horizontalStrip,FluxBounds.fluxBound_zero,realEnergy_empty,targetCap,targetCapKind] using hu
  · rw [← sourceEnergy_eq_finite hM hshort hlong]
    change quadrantFloor 25+weightedLoss Finset.univ (coeff 25) shifts (r : ℝ)≤
      sourceEnergy r (r+2) (twoCornerFamily c (opposite c) threeCell ∅)
    rw [sourceEnergy_pair r (r+2) (opposite_distinct c),diagramEnergy_empty,add_zero,diagramEnergy]
    have hb := quadrantFloor_lt 25
    have he : RefinedObstructionPolynomials.ell.diagram=threeCell := by decide +kernel
    norm_num [quadrantValue,he] at hb
    have hw : weightedLoss Finset.univ (coeff 25) shifts (r : ℝ)=
        (10/3 : ℝ)/(r : ℝ)^4+(5/3 : ℝ)/((r : ℝ)-1)^4 := by
      norm_num [weightedLoss,coeff,shifts,Fin.sum_univ_succ]
    rw [hw]
    exact (add_lt_add hb (ell_correction hr)).le

theorem ell_not_maximal {r : ℕ} (hr : 4≤r) (c : Corner) :
    ¬IsMaximizer (cornerPrimal (r-1) (r+2-1) (singleFamily c threeCell)) := by
  have hcard : threeCell.card=3 := by decide +kernel
  have hc : (cornerStrip (r-1) (r+3) 0).card=
      (cornerPrimal (r-1) (r+2-1) (singleFamily c threeCell)).card := by
    rw [card_cornerStrip (by omega : 1≤r-1) (by omega : 0≤r+3),
      single_card c threeCell_isFerrers (by rw [hcard]; omega) (by rw [hcard]; omega),hcard,
      Nat.sub_add_cancel (show 1≤r by omega),Nat.sub_add_cancel (show 1≤r+2 by omega)]
    have he := Nat.sub_add_cancel (show 1≤r by omega)
    have ha : r*(r+2)=(r-1)*(r+3)+3 := by nlinarith
    omega
  have hconn := CanonicalStrips.cornerStrip_connected_of_short_deficit (r := r-1) (s := r+3) (k := 0)
    (by omega) (by omega) (by omega)
  intro hm
  exact (not_lt_of_ge (hm.2 _ hc hconn)) (ell_count hr c)

end
end SpanningTreeIsoperimetry.RectangularNotchEll
