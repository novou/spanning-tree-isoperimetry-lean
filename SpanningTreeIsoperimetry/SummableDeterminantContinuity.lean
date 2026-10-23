module

public import SpanningTreeIsoperimetry.SummableDeterminantFirstOrder

@[expose] public section

/-! Global continuity estimate for the actual finite-section determinant
limit. The right side uses only the entrywise absolute-sum masses. -/
namespace SpanningTreeIsoperimetry.SummableDeterminantContinuity
open SummableKernelProduct SummableKernelDeterminant SummableDeterminantFirstOrder
open AbsolutelySummableDeterminant FiniteSectionPadding FiniteDeterminantContinuity Filter
open scoped Topology
noncomputable section

theorem difference_summable {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) : Summable (entryNorm (A-B)) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ (hA.add hB)
  intro p
  simpa only [entryNorm,Pi.sub_apply,sub_eq_add_neg,abs_neg] using
    abs_add_le (A p.1 p.2) (-B p.1 p.2)

/-- The finite determinant estimate passes to the actual infinite limit. -/
theorem detLimit_lipschitz {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) :
    |detLimit A hA-detLimit B hB|≤totalMass (A-B)*Real.exp (totalMass A+totalMass B) := by
  have hAB := difference_summable hA hB
  have hleft := ((detLimit_tendsto A hA).sub (detLimit_tendsto B hB)).abs
  have hright := (mass_tendsto hAB).mul (((mass_tendsto hA).add (mass_tendsto hB)).rexp)
  apply le_of_tendsto_of_tendsto hleft hright
  apply Filter.Eventually.of_forall
  intro n
  have he : finiteSection (A-B) n=finiteSection A n-finiteSection B n := by
    ext i j
    rfl
  simpa only [he] using determinant_continuity (finiteSection A n) (finiteSection B n)

end
end SpanningTreeIsoperimetry.SummableDeterminantContinuity
