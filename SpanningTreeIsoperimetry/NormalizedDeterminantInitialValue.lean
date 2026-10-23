module

public import SpanningTreeIsoperimetry.NormalizedExponentialPath

@[expose] public section

/-! The actual determinant deformation starts at the identity. -/
namespace SpanningTreeIsoperimetry.NormalizedDeterminantInitialValue
open NormalizedExponentialInverse NormalizedExponentialNonzero NormalizedExponentialPath
open OneSidedLaurentCompatibility EvenExponentialPath OneSidedLaurentKernels
open SummableKernelDeterminant WeightedPowerSeries
noncomputable section

theorem C_zero (V : PowerSeries ℝ) : C V 0=identity := by
  have hn : N V 0=identity := by simp only [N,neg_zero,even_zero,identity]
  have hw : W V 0=identity := by
    ext i j
    simp only [W,even_zero,M_unit_apply,identity,T_unit_apply]
  rw [C_eq,hn,hw,unit_left]

theorem perturbation_zero (V : PowerSeries ℝ) : perturbation V 0=0 := by
  rw [perturbation,C_zero,sub_self]

theorem determinant_zero {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) : determinant V hV0 hV 0=1 := by
  exact (detLimit_congr (perturbation_summable hV0 hV 0) zero_summable (perturbation_zero V)).trans detLimit_zero

theorem log_determinant_zero {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) : Real.log (determinant V hV0 hV 0)=0 := by
  rw [determinant_zero hV0 hV,Real.log_one]

end
end SpanningTreeIsoperimetry.NormalizedDeterminantInitialValue
