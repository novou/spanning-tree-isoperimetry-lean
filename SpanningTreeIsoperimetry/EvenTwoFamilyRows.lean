module

public import SpanningTreeIsoperimetry.SmallFamilyCountComparison
public import SpanningTreeIsoperimetry.SmallCornerCorrections
public import SpanningTreeIsoperimetry.MulticornerEnergyMinimum

@[expose] public section

/-! Actual multicorner comparisons for the even selector-two deficit-three
families, using the certified rows20 and21. -/
namespace SpanningTreeIsoperimetry.EvenTwoFamilyRows
open Ferrers CornerEnergy CornerPrimalDomains CrossHullCountComparison
  SmallFamilyProfiles SmallFamilyMonotonicity SmallFamilyCostBounds
  SmallFamilyCountComparison MulticornerEndpointChecks SmallCornerCorrections
  FixedStripEnergyUpper
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem square_seven {r : ℕ} (hr8 : 8≤r) (M : Corner → Diagram)
    (hM : ∀ c,IsFerrers (M c)) (hk : totalDefect M=7)
    {c d : Corner} (hdc : d≠c) (hc : (M c).Nonempty) (hd : (M d).Nonempty) :
    treeCount (cornerPrimal (r-1) (r-1) M)<treeCount (cornerStrip (r-2) (r+2) 3) := by
  have hr : totalDefect M≤r-1 := by omega
  have hfit : 3≤r+2-1 := by omega
  have htarget := finiteTargetEnergy_antitone (by decide : 2≤6) (by omega : 2≤r-2)
    (by decide : 3≤10-1) hfit (by omega : 6≤r-2) (by omega : 10≤r+2)
  have hq := MulticornerEnergyMinimum.two_nonempty_minimum Finset.univ M
    (fun c _ => hM c) (Finset.mem_univ c) (Finset.mem_univ d) hdc hc hd
  change realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip (totalDefect M-1))≤_ at hq
  rw [hk] at hq
  have hcharge := source_energy_charged M hM hr hr
  rw [hk] at hcharge
  have hsingle := single_square_lower (by omega : 2≤r)
  have hsource : quadrantFloor 20+weightedLoss Finset.univ (coeff 20) shifts r≤
      finiteSourceEnergy M hM hr hr := by
    norm_num [quadrantFloor,weightedLoss,coeff,shifts,Fin.sum_univ_succ] at hcharge ⊢
    change _+7*single r r≤_ at hcharge
    have hw : (84 : ℝ)/5/(r : ℝ)^4=7*(12/(5*(r : ℝ)^4)) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [hw]
    linarith only [hq,hcharge,hsingle,RefinedStripEnergy.strip_energy_bounds_1.1,
      RefinedStripEnergy.strip_energy_bounds_6.1]
  have hcost := endpointCost_lt_floor 20 (show leftEnd 20≤(r : ℝ) by
    norm_num [leftEnd]; exact_mod_cast hr8)
  apply count_lt_of_profile (a := 0) (h := 2) (by omega : 3≤r-2) (by decide)
    (by omega) (by omega) (by omega) (by omega) M hM hr hr hfit
    (show r*r+3=(r-2)*(r+2)+totalDefect M by
      rw [hk]
      have he : r=(r-2)+2 := by omega
      conv_lhs => rw [he]
      conv_rhs => rw [show r+2=(r-2)+4 by omega]
      ring)
    20 (by norm_num [gap]) (by norm_num [hullShift]) (by norm_num [sourceShift])
    (by rw [if_neg (show r-2≠3 by omega)]; norm_num [errorCoeff]) hcost
    (by norm_num [targetCapKind,targetCap]; exact htarget) hsource

theorem gap_two_six {r : ℕ} (hr7 : 7≤r) (M : Corner → Diagram)
    (hM : ∀ c,IsFerrers (M c)) (hk : totalDefect M=6)
    {c d : Corner} (hdc : d≠c) (hc : (M c).Nonempty) (hd : (M d).Nonempty) :
    treeCount (cornerPrimal (r-1) (r+2-1) M)<treeCount (cornerStrip (r-1) (r+3) 3) := by
  have hr : totalDefect M≤r-1 := by omega
  have hs : totalDefect M≤r+2-1 := by omega
  have hfit : 3≤r+3-1 := by omega
  have htarget := finiteTargetEnergy_antitone (by decide : 2≤6) (by omega : 2≤r-1)
    (by decide : 3≤10-1) hfit (by omega : 6≤r-1) (by omega : 10≤r+3)
  have hq := MulticornerEnergyMinimum.two_nonempty_minimum Finset.univ M
    (fun c _ => hM c) (Finset.mem_univ c) (Finset.mem_univ d) hdc hc hd
  change realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip (totalDefect M-1))≤_ at hq
  rw [hk] at hq
  have hcharge := source_energy_charged M hM hr hs
  rw [hk] at hcharge
  have hsingle := single_ordered_lower (by omega : 2≤r) (by omega : r≤r+2)
  have hsource : quadrantFloor 21+weightedLoss Finset.univ (coeff 21) shifts r≤
      finiteSourceEnergy M hM hr hs := by
    norm_num [quadrantFloor,weightedLoss,coeff,shifts,Fin.sum_univ_succ] at hcharge ⊢
    change _+6*single r (r+2)≤_ at hcharge
    have hw : (10 : ℝ)/(r : ℝ)^4=6*(5/(3*(r : ℝ)^4)) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [hw]
    linarith only [hq,hcharge,hsingle,RefinedStripEnergy.strip_energy_bounds_1.1,
      RefinedStripEnergy.strip_energy_bounds_5.1]
  have hcost := endpointCost_lt_floor 21 (show leftEnd 21≤(r : ℝ) by
    norm_num [leftEnd]; exact_mod_cast hr7)
  apply count_lt_of_profile (a := 2) (h := 1) (by omega : 3≤r-1) (by decide)
    (by omega) (by omega) (by omega) (by omega) M hM hr hs hfit
    (show r*(r+2)+3=(r-1)*(r+3)+totalDefect M by
      rw [hk]
      have he : r=(r-1)+1 := by omega
      conv_lhs => rw [he]
      conv_rhs => rw [show r+3=(r-1)+4 by omega]
      ring)
    21 (by norm_num [gap]) (by norm_num [hullShift]) (by norm_num [sourceShift])
    (by rw [if_neg (show r-1≠3 by omega)]; norm_num [errorCoeff]) hcost
    (by norm_num [targetCapKind,targetCap]; exact htarget) hsource

theorem source_floor_twenty_two {r s m : ℕ} (hr2 : 2≤r) (hrs : r≤s) (hrm : r≤m)
    (M : Corner → Diagram) (hM : ∀ c,IsFerrers (M c)) (hk : 7≤totalDefect M)
    (hr : totalDefect M≤r-1) (hs : totalDefect M≤s-1)
    {c d : Corner} (hdc : d≠c) (hc : (M c).Nonempty) (hd : (M d).Nonempty) :
    quadrantFloor 22+weightedLoss Finset.univ (coeff 22) shifts m≤
      finiteSourceEnergy M hM hr hs := by
  have hq := MulticornerEnergyMinimum.two_nonempty_minimum Finset.univ M
    (fun c _ => hM c) (Finset.mem_univ c) (Finset.mem_univ d) hdc hc hd
  change realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip (totalDefect M-1))≤_ at hq
  have hE := realEnergy_strip_monotone (show 6≤totalDefect M-1 by omega)
  have hcharge := source_energy_charged M hM hr hs
  have hsingle := single_ordered_lower hr2 hrs
  have hr0 : (0 : ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have hm0 : (0 : ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hw : 5/(3*(m : ℝ)^4)≤5/(3*(r : ℝ)^4) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    gcongr
  have hlower := hw.trans_lt hsingle
  have hmul := mul_le_mul_of_nonneg_right (show (7 : ℝ)≤totalDefect M by exact_mod_cast hk)
    (show 0≤single r s by linarith [show 0<5/(3*(m : ℝ)^4) by positivity])
  change _+(totalDefect M : ℝ)*single r s≤_ at hcharge
  norm_num [quadrantFloor,weightedLoss,coeff,shifts,Fin.sum_univ_succ]
  have hid : (35 : ℝ)/3/(m : ℝ)^4=7*(5/(3*(m : ℝ)^4)) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hid]
  linarith only [hq,hE,hcharge,hmul,hlower,RefinedStripEnergy.strip_energy_bounds_1.1,
    RefinedStripEnergy.strip_energy_bounds_6.1]

end
end SpanningTreeIsoperimetry.EvenTwoFamilyRows
