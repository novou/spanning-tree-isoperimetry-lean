import SpanningTreeIsoperimetry.SingleCornerShallowCosts
import SpanningTreeIsoperimetry.RefinedCornerEnvelope

/-! Actual Ferrers energies dominate every shallow index-three cost, using
the complete structural obstruction envelope and the six checked ranges. -/
namespace SpanningTreeIsoperimetry.SingleCornerShallowEnergy
open Ferrers CornerEnergy StripRigidity RefinedCornerEnvelope SingleCornerShallowCosts
open MulticornerEndpointChecks SmallFamilyMonotonicity FluxBounds
noncomputable section

theorem shallow_upper_lt_bound (i : Fin 6) {j k : ℕ}
    (hj : rangeStart i≤(j : ℝ)) (hk : j+5≤k) : shallowUpper i<bound k := by
  have hk5 : 5≤k := by omega
  fin_cases i <;> norm_num [rangeStart] at hj
  all_goals
    norm_cast at hj
    unfold bound
    split_ifs <;> norm_num [shallowUpper] <;> omega

theorem shallow_three_energy {r : ℝ} (i : Fin 6) (j : ℕ)
    (hjlo : rangeStart i≤(j : ℝ)) (hjhi : j≤(rangeEnd i).val)
    (hr : (j : ℝ)+sourceBase i≤r) {M : Diagram}
    (hM : IsFerrers M) (hn : ¬IsStraightStrip M) (hk : j+5≤M.card) :
    realEnergy (horizontalStrip j)+aspectStep (shallowGap i) (shallowShift i) r+
      fluxBound (r-shallowShift i) (r+shallowGap i+shallowShift i) j<realEnergy M :=
  (shallow_three_cost i j hjlo hjhi hr).trans
    ((shallow_upper_lt_bound i hjlo hk).trans (single_nonstrip_bound hM (by omega) hn))

/-- The three even ranges cover all allowed residual deficits. -/
theorem even_three_energy {r : ℝ} {j : ℕ} (hj : j≤6) (hr : (j : ℝ)+8≤r)
    {M : Diagram} (hM : IsFerrers M) (hn : ¬IsStraightStrip M) (hk : j+5≤M.card) :
    realEnergy (horizontalStrip j)+aspectStep 4 1 r+fluxBound (r-1) (r+5) j<realEnergy M := by
  by_cases hj1 : j≤1
  · have h := shallow_three_energy (i := 0) j (by norm_num [rangeStart])
      (by norm_num [rangeEnd]; omega) (by simpa [sourceBase] using hr) hM hn hk
    simpa [shallowGap,shallowShift,show r+4+1=r+5 by ring,show r+3+2=r+5 by ring] using h
  · by_cases hj3 : j≤3
    · have h := shallow_three_energy (i := 1) j (by norm_num [rangeStart]; exact_mod_cast (show 2≤j by omega))
        (by norm_num [rangeEnd]; omega) (by simpa [sourceBase] using hr) hM hn hk
      simpa [shallowGap,shallowShift,show r+4+1=r+5 by ring,show r+3+2=r+5 by ring] using h
    · have h := shallow_three_energy (i := 2) j (by norm_num [rangeStart]; exact_mod_cast (show 4≤j by omega))
        (by norm_num [rangeEnd]; omega) (by simpa [sourceBase] using hr) hM hn hk
      simpa [shallowGap,shallowShift,show r+4+1=r+5 by ring,show r+3+2=r+5 by ring] using h

/-- The three odd ranges cover all allowed residual deficits. -/
theorem odd_three_energy {r : ℝ} {j : ℕ} (hj : j≤7) (hr : (j : ℝ)+12≤r)
    {M : Diagram} (hM : IsFerrers M) (hn : ¬IsStraightStrip M) (hk : j+5≤M.card) :
    realEnergy (horizontalStrip j)+aspectStep 3 2 r+fluxBound (r-2) (r+5) j<realEnergy M := by
  by_cases hj1 : j≤1
  · have h := shallow_three_energy (i := 3) j (by norm_num [rangeStart])
      (by norm_num [rangeEnd]; omega) (by simpa [sourceBase] using hr) hM hn hk
    simpa [shallowGap,shallowShift,show r+4+1=r+5 by ring,show r+3+2=r+5 by ring] using h
  · by_cases hj3 : j≤3
    · have h := shallow_three_energy (i := 4) j (by norm_num [rangeStart]; exact_mod_cast (show 2≤j by omega))
        (by norm_num [rangeEnd]; omega) (by simpa [sourceBase] using hr) hM hn hk
      simpa [shallowGap,shallowShift,show r+4+1=r+5 by ring,show r+3+2=r+5 by ring] using h
    · have h := shallow_three_energy (i := 5) j (by norm_num [rangeStart]; exact_mod_cast (show 4≤j by omega))
        (by norm_num [rangeEnd]; omega) (by simpa [sourceBase] using hr) hM hn hk
      simpa [shallowGap,shallowShift,show r+4+1=r+5 by ring,show r+3+2=r+5 by ring] using h

end
end SpanningTreeIsoperimetry.SingleCornerShallowEnergy
