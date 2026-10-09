import SpanningTreeIsoperimetry.SmallFamilyPatternData

/-! Natural side/deficit metadata for the first twenty profile rows. -/
namespace SpanningTreeIsoperimetry.SmallFamilyRowData
open SmallFamilyProfiles SmallFamilyPatternData
noncomputable section

def rowGap : Fin 20 → ℕ := ![0,1,0,1,1,2,0,0,1,1,2,0,0,0,1,1,2,0,0,0]
def rowShift : Fin 20 → ℕ := ![1,1,1,1,1,1,2,2,1,1,1,2,2,2,1,1,1,2,2,2]
def rowStart : Fin 20 → ℕ := ![5,4,5,5,5,4,5,5,5,5,5,6,6,6,6,6,6,7,7,7]
def rowTarget : Fin 20 → ℕ := ![1,0,2,1,1,0,0,0,2,2,1,1,1,1,3,3,2,2,2,2]
def index (i : Fin 20) : Fin 26 := ⟨i.val,by omega⟩

theorem gap_cast (i : Fin 20) : gap (index i)=(rowGap i : ℝ) := by
  fin_cases i <;> norm_num [gap,index,rowGap]

theorem shift_cast (i : Fin 20) : hullShift (index i)=(rowShift i : ℝ) := by
  fin_cases i <;> norm_num [hullShift,index,rowShift]

theorem target_relation (i : Fin 20) :
    rowTarget i+rowShift i*(rowGap i+rowShift i)=rowDeficit (index i) := by
  fin_cases i <;> norm_num [rowTarget,rowShift,rowGap,rowDeficit,index]

theorem minimum_side {r N : ℕ} (i : Fin 20) (hN : 18≤N)
    (hk : rowDeficit (index i)<r) (harea : r*(r+rowGap i)=N+rowDeficit (index i)) :
    rowStart i≤r := by
  by_contra hlt
  have hr : r<rowStart i := by omega
  fin_cases i <;>
    norm_num [rowStart,rowGap,rowDeficit,index] at hr hk harea <;>
    interval_cases r <;> norm_num at harea <;> omega

theorem start_or_extra {r : ℕ} (i : Fin 20) (hr : rowStart i≤r) :
    leftEnd (index i)≤(r : ℝ) ∨ (r=5 ∧ (index i=6 ∨ index i=7)) := by
  fin_cases i <;> norm_num [rowStart,leftEnd,index] at hr ⊢
  all_goals first
    | exact_mod_cast hr
    | by_cases h : r=5
      · simp [h]
      · left; exact_mod_cast (show 6≤r by omega)

end
end SpanningTreeIsoperimetry.SmallFamilyRowData
