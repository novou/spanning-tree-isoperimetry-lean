module

public import SpanningTreeIsoperimetry.NormalizedLogDerivativeTrace
public import SpanningTreeIsoperimetry.NormalizedDeterminantInitialValue
public import SpanningTreeIsoperimetry.RegularizedTraceValues
public import SpanningTreeIsoperimetry.RegularizedFiniteSectionLimit
public import SpanningTreeIsoperimetry.RegularizedStripCriticalLimit
public import SpanningTreeIsoperimetry.ScalarDeterminantODE

@[expose] public section

/-! The exact strip Fourier identity, with the determinant deformation,
actual symbol and energy identifications, and critical passage all proved
locally. No Toeplitz determinant theorem is assumed. -/
namespace SpanningTreeIsoperimetry.StripFourierIdentity
open WeightedPowerSeries SummableKernelTrace SummableKernelProduct
open ToeplitzHankelKernels OneSidedToeplitz EvenExponentialPath
open RegularizedCircleFactorization RegularizedTraceValues RegularizedStripCriticalLimit
open StripSpectralRegularization Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem log_determinant_value {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (t : ℝ) :
    Real.log (NormalizedExponentialPath.determinant V hV0 hV t)=
      ScalarDeterminantODE.exponent
        (trace (M (evenGenerator V)-T (evenGenerator V)))
        (trace (product (H (lift V)) (H (lift V)))) t := by
  have h := ScalarDeterminantODE.quadratic_of_affine_derivative
    (fun s => Real.log (NormalizedExponentialPath.determinant V hV0 hV s))
    (trace (M (evenGenerator V)-T (evenGenerator V)))
    (trace (product (H (lift V)) (H (lift V))))
    (NormalizedLogDerivativeTrace.hasDerivAt_log_affine hV0 hV) t
  rw [NormalizedDeterminantInitialValue.log_determinant_zero hV0 hV,zero_add] at h
  exact h

theorem regularized_log_determinant {z : ℝ} (hz : 4<z) :
    Real.log (RegularizedFiniteSectionLimit.determinant z hz)=
      -RegularizedFourierQuadraticLimit.evenSum z+RegularizedFourierQuadratic.quadratic z/2 := by
  have h := log_determinant_value (logSeries_constant z) (logSeries_weighted hz) 1
  change Real.log (RegularizedFiniteSectionLimit.determinant z hz)=
    ScalarDeterminantODE.exponent (linearTrace z) (quadraticTrace z) 1 at h
  rw [linearTrace_eq hz,quadraticTrace_eq hz] at h
  simpa only [ScalarDeterminantODE.exponent,mul_one,one_pow] using h

/-- The actual regularized strip supremum has the exact Fourier value. -/
theorem regularized_identity {z : ℝ} (hz : 4<z) :
    stripSupremum z=RegularizedFourierQuadraticLimit.evenSum z-
      RegularizedFourierQuadratic.quadratic z/2 := by
  rw [RegularizedFiniteSectionLimit.stripSupremum_eq_neg_log_determinant hz,
    regularized_log_determinant hz]
  ring

/-- The manuscript's critical constant, with every analytic and matrix
input discharged for the actual lattice energy. -/
theorem strip_limit_identity :
    UniformStripEnergy.stripEnergyLimit=
      (SquareMaximality.squareLatticeEntropy-Real.log (1+Real.sqrt 2))/2-
        (1/2)*∑' n : ℕ,((n+1 : ℕ) : ℝ)*StripFourierCoefficients.coefficient (n+1)^2 := by
  change UniformStripEnergy.stripEnergyLimit=criticalFourierProfile
  have he : stripSupremum =ᶠ[nhdsWithin 4 (Set.Ioi 4)] fourierProfile := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [regularized_identity hz,fourierProfile]
    ring
  have ht : Tendsto fourierProfile (nhdsWithin 4 (Set.Ioi 4))
      (𝓝 UniformStripEnergy.stripEnergyLimit) := stripSupremum_right_limit.congr' he
  exact tendsto_nhds_unique ht fourierProfile_right_limit

end
end SpanningTreeIsoperimetry.StripFourierIdentity
