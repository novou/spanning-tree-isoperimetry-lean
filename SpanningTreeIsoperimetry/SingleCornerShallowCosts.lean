module

public import SpanningTreeIsoperimetry.MulticornerEndpointChecks
public import SpanningTreeIsoperimetry.FluxBounds
public import SpanningTreeIsoperimetry.AspectCost

@[expose] public section

/-! The single-corner endpoint comparisons lifted to the entire shallow
parameter ranges by the checked aspect and flux monotonicity. -/
namespace SpanningTreeIsoperimetry.SingleCornerShallowCosts
open Ferrers CornerEnergy FluxBounds AspectCost MulticornerEndpointChecks SmallFamilyMonotonicity
noncomputable section

theorem aspectStep_antitone {a h : ℝ} (ha : 0≤a) (hh : 0≤h) :
    AntitoneOn (aspectStep a h) (Set.Ioi h) := by
  have hm := shifted_difference_antitone (A := a+2*h) (B := a) (a := -h) (b := 0)
    ha (by linarith) (by linarith)
  intro x hx y hy hxy
  have ht := hm (by simpa only [neg_neg] using hx) (by simpa only [neg_neg] using hy) hxy
  simpa only [add_zero,sub_eq_add_neg,aspectStep] using ht

theorem single_odd_cost {r : ℝ} (j : Fin 6) (hr : (j.val : ℝ)+6≤r) :
    realEnergy (horizontalStrip j.val)+aspectStep 3 1 r+fluxBound (r-1) (r+4) j.val<
      (if j=0 then (2837 : ℝ)/50000 else 7421/100000) := by
  have hj := Nat.cast_nonneg (α := ℝ) j.val
  have hA := aspectStep_antitone (a := 3) (h := 1) (by norm_num) (by norm_num)
    (show (j.val : ℝ)+6∈Set.Ioi 1 by change 1<(j.val : ℝ)+6; linarith)
    (show r∈Set.Ioi 1 by change 1<r; linarith) hr
  have hB := (fluxBound_antitone_left (r := (j.val : ℝ)+5) (R := r-1) (s := r+4)
    (by linarith) (by linarith) hj).trans
    (fluxBound_antitone_right (r := (j.val : ℝ)+5) (s := (j.val : ℝ)+10) (S := r+4)
      hj (by linarith) (by linarith))
  have h := single_odd_endpoint j
  unfold singleOddCost at h
  exact lt_of_le_of_lt (add_le_add (add_le_add le_rfl hA) hB) h

/-- One theorem covers the six checked shallow index-three ranges. -/
theorem shallow_three_cost {r : ℝ} (i : Fin 6) (j : ℕ)
    (hjlo : rangeStart i≤(j : ℝ)) (hjhi : j≤(rangeEnd i).val)
    (hr : (j : ℝ)+sourceBase i≤r) :
    realEnergy (horizontalStrip j)+aspectStep (shallowGap i) (shallowShift i) r+
      fluxBound (r-shallowShift i) (r+shallowGap i+shallowShift i) j<shallowUpper i := by
  have hj := Nat.cast_nonneg (α := ℝ) j
  have ha : 0≤shallowGap i := by fin_cases i <;> norm_num [shallowGap]
  have hh : 0≤shallowShift i := by fin_cases i <;> norm_num [shallowShift]
  have hleft : shallowShift i<rangeStart i+sourceBase i := by
    fin_cases i <;> norm_num [shallowShift,rangeStart,sourceBase]
  have hbase : rangeStart i+sourceBase i≤r := by linarith
  have hA := aspectStep_antitone ha hh hleft (lt_of_lt_of_le hleft hbase) hbase
  have hE := realEnergy_strip_monotone hjhi
  have hshort : sourceBase i-shallowShift i=fluxShortBase i := by
    fin_cases i <;> norm_num [sourceBase,shallowShift,fluxShortBase]
  have hlong : sourceBase i+shallowGap i+shallowShift i=fluxLongBase i := by
    fin_cases i <;> norm_num [sourceBase,shallowGap,shallowShift,fluxLongBase]
  have hsa : 5≤fluxShortBase i := by fin_cases i <;> norm_num [fluxShortBase]
  have hsb : fluxShortBase i≤fluxLongBase i := by fin_cases i <;> norm_num [fluxShortBase,fluxLongBase]
  have hB := (fluxBound_antitone_left (r := (j : ℝ)+fluxShortBase i)
    (R := r-shallowShift i) (s := r+shallowGap i+shallowShift i)
    (by linarith) (by linarith) hj).trans
    (fluxBound_antitone_right (r := (j : ℝ)+fluxShortBase i) (s := (j : ℝ)+fluxLongBase i)
      (S := r+shallowGap i+shallowShift i) hj (by linarith) (by linarith))
  have hend : ((rangeEnd i).val : ℝ)≤fluxShortBase i-1 := by
    fin_cases i <;> norm_num [rangeEnd,fluxShortBase]
  have hjend : (j : ℝ)≤(rangeEnd i).val := by exact_mod_cast hjhi
  have hmono := fluxBound_diagonal_monotone hsa hsb
    (show (j : ℝ)∈Set.Icc 0 (fluxShortBase i-1) from ⟨hj,hjend.trans hend⟩)
    (show ((rangeEnd i).val : ℝ)∈Set.Icc 0 (fluxShortBase i-1) from ⟨Nat.cast_nonneg _,hend⟩) hjend
  have hB' : fluxBound ((j : ℝ)+fluxShortBase i) ((j : ℝ)+fluxLongBase i) j≤
      fluxBound ((rangeEnd i).val+fluxShortBase i) ((rangeEnd i).val+fluxLongBase i) (rangeEnd i).val := by
    simpa only [add_comm] using hmono
  exact lt_of_le_of_lt (add_le_add (add_le_add hE hA) (hB.trans hB')) (shallow_three_endpoint i)

end
end SpanningTreeIsoperimetry.SingleCornerShallowCosts
