module

public import SpanningTreeIsoperimetry.SmallFamilyRowData
public import SpanningTreeIsoperimetry.SmallFamilyCostBounds

@[expose] public section

/-! Target-side monotonicity and cost endpoints for the first twenty rows. -/
namespace SpanningTreeIsoperimetry.SmallFamilyRowTargets
open SmallFamilyRowData SmallFamilyProfiles SmallFamilyCostBounds
  MulticornerEndpointChecks CrossHullCountComparison FixedStripEnergyUpper
  Ferrers CornerEnergy
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem target_fits {r : ℕ} (i : Fin 20) (hr : rowStart i≤r) :
    3≤r-rowShift i ∧ 2≤r+rowGap i+rowShift i ∧
      rowTarget i+1<r+rowGap i+rowShift i ∧
      r+rowGap i+rowShift i≤3*(r-rowShift i) := by
  fin_cases i <;> norm_num [rowStart,rowShift,rowGap,rowTarget] at hr ⊢ <;> omega

theorem target_short_deficit {r : ℕ} (i : Fin 20) (hr : rowStart i≤r) :
    rowTarget i<r-rowShift i := by
  fin_cases i <;> norm_num [rowStart,rowShift,rowTarget] at hr ⊢ <;> omega

theorem row_shift_zero (i : Fin 20) : sourceShift (index i)=0 := by
  fin_cases i <;> norm_num [sourceShift,index]

theorem row_remainder_coefficient {r : ℕ} (i : Fin 20) (hr : rowStart i≤r) :
    (if r-rowShift i=3 then (1 : ℝ)/3 else 1/4)≤errorCoeff (index i) := by
  fin_cases i <;> norm_num [rowStart,rowShift,errorCoeff,index] at hr ⊢
  all_goals split_ifs <;> norm_num at * <;> omega

set_option maxHeartbeats 1000000 in
theorem target_bound {r : ℕ} (i : Fin 20) (hr : rowStart i≤r)
    (hR : 2≤r-rowShift i) (hj : rowTarget i≤r+rowGap i+rowShift i-1) :
    finiteTargetEnergy hR hj≤targetCap (targetCapKind (index i)) := by
  have hf := target_fits i hr
  by_cases hz : rowTarget i=0
  · have hcap : targetCap (targetCapKind (index i))=0 := by
      fin_cases i <;> norm_num [rowTarget] at hz <;>
        norm_num [index,targetCapKind,targetCap]
    rw [hcap]
    have hh := finite_target_upper hf.1 hf.2.1 hf.2.2.1
    have he : realEnergy (horizontalStrip (rowTarget i))+
        FluxBounds.fluxBound ((r-rowShift i : ℕ) : ℝ) ((r+rowGap i+rowShift i : ℕ) : ℝ) (rowTarget i)=0 := by
      rw [hz]
      simp [realEnergy_strip_zero,FluxBounds.fluxBound,FluxBounds.cubic,FluxBounds.quadratic]
    rw [he] at hh
    exact hh
  · fin_cases i <;> norm_num [rowTarget] at hz
    all_goals norm_num [rowStart,rowShift,rowGap,rowTarget,index,targetCapKind,targetCap] at hr hR hj ⊢
    all_goals apply finiteTargetEnergy_antitone <;> omega

theorem cost_bound {r : ℕ} (i : Fin 20) (hr : rowStart i≤r) :
    endpointCost (index i) r<quadrantFloor (index i) := by
  rcases start_or_extra i hr with h|⟨rfl,h⟩
  · exact endpointCost_lt_floor (index i) h
  · exact extra_five_lt_floor (h.elim Or.inl (fun h => Or.inr (Or.inl h)))

end
end SpanningTreeIsoperimetry.SmallFamilyRowTargets
